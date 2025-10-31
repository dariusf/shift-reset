open Shift_reset.ShiftReset

let ( let* ) = bind

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

type regex =
  | Emp
  | Atom of int
  | Seq of regex * regex
  | Disj of regex * regex

let interp r ns : bool =
  let rec visit r ns : int list option =
    match r with
    | Emp -> Some ns
    | Atom a -> (match ns with b :: ns1 when a = b -> Some ns1 | _ -> None)
    | Seq (r1, r2) ->
      (match visit r1 ns with None -> None | Some rest -> visit r2 rest)
    | Disj (_, _) -> failwith "?"
  in
  match visit r ns with Some [] -> true | _ -> false

let interp_cps r ns : bool =
  let rec visit r ns k : int list option =
    match r with
    | Emp -> k (Some ns)
    | Atom a -> k (match ns with b :: ns1 when a = b -> Some ns1 | _ -> None)
    | Seq (r1, r2) ->
      visit r1 ns (function None -> None | Some rest -> visit r2 rest k)
    | Disj (r1, r2) ->
      (match visit r1 ns k with None -> visit r2 ns k | r -> k r)
  in
  match visit r ns Fun.id with Some [] -> true | _ -> false

let interp_cps_m r ns : bool =
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
      (match visit r1 ns k mk with None -> visit r2 ns k mk | r -> k r mk)
  in
  match visit r ns (fun x mk -> mk x) Fun.id with Some [] -> true | _ -> false

let%expect_test _ =
  let test r ns =
    let pr r = r |> [%derive.show: bool] |> print_endline in
    (* interp r ns |> pr; *)
    (* interp_cps r ns |> pr; *)
    interp_cps_m r ns |> pr
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
  [%expect {| true |}]
