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
