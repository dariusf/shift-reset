open Shift_reset.ShiftReset

let rec append : ('a list, 'a list, 'a list, 'a list -> ('b, 'b, 'a list) t) fn
    =
 fun xs ->
  match xs with
  | [] -> shift (fun k -> ret (fun x -> ret (k x)))
  | a :: rest ->
    let* r' = append rest in
    ret (a :: r')

let%expect_test "append" =
  let test a = a |> [%derive.show: int list] |> print_endline in
  run
    (let* dl = reset (append [1; 2; 3]) in
     dl [4; 5; 6])
  |> test;
  [%expect {| [1; 2; 3; 4; 5; 6] |}]

let%expect_test "multishot" =
  let test a = a |> [%derive.show: int] |> print_endline in
  run
  @@ reset
       (let* r = shift (fun k -> ret (k 1 + k 2)) in
        ret (r + 1))
  |> test;
  [%expect {| 5 |}]

let%expect_test "multishot atm" =
  let test a = a |> print_endline in
  run
    begin
      reset
        (let* r = shift (fun k -> ret (k 1 ^ k 2)) in
         ret (string_of_int r ^ "!"))
    end
  |> test;
  [%expect {| 1!2! |}]

let%expect_test "printf" =
  let test a = a |> print_endline in
  run
    (reset
       (let* r = shift (fun k -> ret (fun v -> k (string_of_int v))) in
        let* b = shift (fun k -> ret (fun v -> k (string_of_bool v))) in
        ret (r ^ b ^ "!")))
    1 true
  |> test;
  [%expect {| 1true! |}]

(* https://www.cl.cam.ac.uk/teaching/2324/R277/handout-delimited-continuations.pdf *)
(* ⟨1 + ⟨(S k1. k1 100 + k1 10) + (S k2. S k3. 1)⟩⟩ *)
let%expect_test "shift0 and control" =
  let test a = a |> print_endline in
  let r =
    run
    @@ reset
         (let* r =
            reset
              (let* a = shift (fun k1 -> ret (k1 100 + k1 10)) in
               let* b = shift (fun _k2 -> shift (fun _k3 -> ret 1)) in
               ret (a + b))
          in
          ret (1 + r))
  in
  (match r with 3 -> "shift" | 1 -> "shift0" | 2 -> "control" | _ -> "??")
  |> test;
  [%expect {| shift |}]

module Regex = struct
  type regex =
    | Emp
    | Atom of int
    | Seq of regex * regex
    | Disj of regex * regex

  module Simple = struct
    let interp r ns : bool =
      let rec visit r ns : int list option =
        match r with
        | Emp -> Some ns
        | Atom a ->
          (match ns with b :: ns1 when a = b -> Some ns1 | _ -> None)
        | Seq (r1, r2) ->
          (match visit r1 ns with None -> None | Some rest -> visit r2 rest)
        | Disj (_, _) -> failwith "?"
      in
      match visit r ns with Some [] -> true | _ -> false
  end

  module CPS = struct
    let rec visit r ns k : int list option =
      match r with
      | Emp -> k (Some ns)
      | Atom a ->
        k (match ns with b :: ns1 when a = b -> Some ns1 | _ -> None)
      | Seq (r1, r2) ->
        visit r1 ns (function None -> None | Some rest -> visit r2 rest k)
      | Disj (r1, r2) ->
        (match visit r1 ns k with None -> visit r2 ns k | r -> r)

    let interp r ns : bool =
      match visit r ns Fun.id with Some [] -> true | _ -> false
  end

  module TwoCPS = struct
    let rec visit r ns k mk : int list option =
      match r with
      | Emp -> k (Some ns) mk
      | Atom a ->
        k (match ns with b :: ns1 when a = b -> Some ns1 | _ -> None) mk
      | Seq (r1, r2) ->
        visit r1 ns
          (fun v1 mk1 ->
            match v1 with None -> None | Some rest -> visit r2 rest k mk1)
          mk
      | Disj (r1, r2) ->
        (match visit r1 ns k mk with None -> visit r2 ns k mk | r -> r)

    let interp r ns : bool =
      (* something like: visit... (fun nsp -> (fun mk -> 1 + mk ())) (fun () -> 0) *)
      (* match visit r ns (fun x mk -> mk x) Fun.id with Some [] -> true | _ -> false *)
      match visit r ns (fun x mk -> mk x) Fun.id with
      | Some [] -> true
      | _ -> false
  end

  module SR = struct
    let interp r ns : bool =
      let rec visit r ns =
        match r with
        | Emp -> ret (Some ns)
        | Atom a ->
          (match ns with
          | b :: ns1 when a = b -> ret (Some ns1)
          | _ -> ret None)
        | Seq (r1, r2) ->
          let* v = visit r1 ns in
          (match v with
          | None -> ret None
          | Some rest ->
            let* v = visit r2 rest in
            ret v)
        | Disj (r1, r2) ->
          shift (fun k ->
              let* v1 = reset (visit r1 ns <&> k) in
              match v1 with None -> visit r2 ns <&> k | v -> ret v)
      in
      match run (reset (visit r ns)) with Some [] -> true | _ -> false
  end

  let%expect_test _ =
    let test r ns =
      let functions =
        [
          (Simple.interp, "simple");
          (CPS.interp, "CPS");
          (TwoCPS.interp, "2CPS");
          (SR.interp, "SR");
        ]
      in
      let all_results =
        functions
        |> List.map (fun (f, name) ->
            ((try Some (f r ns) with _ -> None), name))
      in
      let to_bool (o, _) = match o with Some b -> b | None -> false in
      let all_true = List.for_all to_bool all_results in
      let all_false = not (List.exists to_bool all_results) in
      if all_true || all_false then
        Format.printf "%b@." (List.hd all_results |> to_bool)
      else
        all_results
        |> List.iter (fun (r, n) ->
            let outcome =
              match r with None -> "fail" | Some b -> string_of_bool b
            in
            Format.printf "%7s: %s@." n outcome)
    in
    test Emp [];
    [%expect {| true |}];
    test Emp [1];
    [%expect {| false |}];

    test (Atom 1) [1];
    [%expect {| true |}];
    test (Atom 1) [2];
    [%expect {| false |}];

    test (Seq (Emp, Atom 2)) [2];
    [%expect {| true |}];
    test (Seq (Atom 2, Emp)) [2];
    [%expect {| true |}];
    test (Seq (Atom 1, Atom 2)) [1; 2];
    [%expect {| true |}];
    test (Seq (Atom 1, Atom 2)) [1; 3];
    [%expect {| false |}];

    (* assoc *)
    test (Seq (Seq (Atom 1, Atom 3), Atom 2)) [1; 3; 2];
    [%expect {| true |}];
    test (Seq (Atom 1, Seq (Atom 3, Atom 2))) [1; 3; 2];
    [%expect {| true |}];

    (* disj *)
    test (Seq (Disj (Atom 1, Atom 2), Atom 3)) [1; 3];
    [%expect
      {|
      simple: fail
         CPS: true
        2CPS: true
          SR: true
      |}];
    test (Seq (Disj (Atom 1, Atom 2), Atom 3)) [2; 3];
    [%expect
      {|
      simple: fail
         CPS: true
        2CPS: true
          SR: true
      |}];

    (* disj comm *)
    test (Seq (Disj (Atom 2, Atom 1), Atom 3)) [1; 3];
    [%expect
      {|
      simple: fail
         CPS: true
        2CPS: true
          SR: true
      |}];
    test (Seq (Disj (Atom 2, Atom 1), Atom 3)) [2; 3];
    [%expect
      {|
      simple: fail
         CPS: true
        2CPS: true
          SR: true
      |}];

    (* disj idem *)
    test (Disj (Atom 1, Atom 1)) [1];
    [%expect
      {|
      simple: fail
         CPS: true
        2CPS: true
          SR: true
      |}]
end
