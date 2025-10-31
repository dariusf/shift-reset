module SMap = struct
  module M = Map.Make (String)
  include M

  let pp pp_v fmt map =
    Format.fprintf fmt "@[<v 0>{@;<0 2>@[<v 0>%a@]@,}@]"
      (Format.pp_print_list
         ~pp_sep:(fun fmt () -> Format.fprintf fmt ",@ ")
         (fun fmt (k, v) -> Format.fprintf fmt "%s: %a" k pp_v v))
      (bindings map)

  let update_ k f m =
    update k (function None -> failwith "invalid" | Some v -> Some (f v)) m
end

type var = string [@@deriving show { with_path = false }]

type expr =
  | Int of int
  | Plus of expr * expr
  | Var of var
  | Abs of var * expr
  | App of expr * expr
  | Shift of var * expr
  | Reset of expr
[@@deriving show { with_path = false }]

(* A lambda calculus interpreter *)
module LambdaCalculus = struct
  type value =
    | Clo of env * var * expr
    | Int of int
  [@@deriving show { with_path = false }]

  and env = value SMap.t

  let rec interp : env -> expr -> value =
   fun env e ->
    match e with
    | Int i -> Int i
    | Plus (e1, e2) ->
      (match interp env e1 with
      | Int a1 ->
        (match interp env e2 with
        | Int a2 -> Int (a1 + a2)
        | _ -> failwith "cannot add non-ints")
      | _ -> failwith "cannot add non-ints")
    | Var x -> SMap.find x env
    | Abs (x, e) -> Clo (env, x, e)
    | App (e1, e2) ->
      (match interp env e1 with
      | Clo (envc, x, e3) ->
        let v = interp env e2 in
        interp (SMap.add x v envc) e3
      | _ -> failwith "cannot apply non-lambda")
    | Shift (_, _) | Reset _ -> failwith "cannot be implemented"
end

module ECPS = struct
  let fresh =
    let i = ref 0 in
    fun () ->
      let r = !i in
      incr i;
      Format.asprintf "x%d" r

  let id () =
    let x = fresh () in
    Abs (x, Var x)

  open LambdaCalculus

  let v2e (v : value) : expr =
    match v with Int i -> Int i | Clo (_, x, e) -> Abs (x, e)

  (* substitution of closed values into expressions, not capture-avoiding *)
  let rec subst (e : expr) (v : value) x : expr =
    match e with
    | Int i -> Int i
    | Plus (e1, e2) -> Plus (subst e1 v x, subst e2 v x)
    | Var y -> if x = y then v2e v else e
    | Abs (y, e) -> if x = y then Abs (y, e) else Abs (y, subst e v x)
    | App (e1, e2) -> App (subst e1 v x, subst e2 v x)
    | Shift (k, e) -> if x = k then Shift (k, e) else Shift (k, subst e v x)
    | Reset e -> subst e v x

  let rec cps (e : expr) : expr =
    match e with
    | Int i ->
      let k = fresh () in
      Abs (k, App (Var k, Int i))
    | Plus (e1, e2) ->
      let k, a1, a2 = (fresh (), fresh (), fresh ()) in
      Abs
        ( k,
          App
            ( cps e1,
              Abs
                (a1, App (cps e2, Abs (a2, App (Var k, Plus (Var a1, Var a2)))))
            ) )
    | Var x ->
      let k = fresh () in
      Abs (k, App (Var k, Var x))
    | Abs (x, e) ->
      let k = fresh () in
      Abs (k, App (Var k, Abs (x, cps e)))
    | App (e1, e2) ->
      let k, f, x = (fresh (), fresh (), fresh ()) in
      Abs
        ( k,
          App
            ( cps e1,
              Abs (f, App (cps e2, Abs (x, App (App (Var f, Var x), Var k)))) )
        )
    | Shift (k, e) ->
      let kappa, a, kappa' = (fresh (), fresh (), fresh ()) in
      let kk : value =
        Clo
          (SMap.empty, a, Abs (kappa', App (Var kappa', App (Var kappa, Var a))))
      in
      Abs (kappa, App (subst (cps e) kk k, id ()))
    | Reset e ->
      let k = fresh () in
      Abs (k, App (Var k, App (cps e, id ())))

  let interp : env -> expr -> value =
   fun env e -> LambdaCalculus.interp env (App (cps e, id ()))

  let%expect_test _ =
    (* let expr a = a |> [%derive.show: expr] |> print_endline in *)
    let value a = a |> [%derive.show: value] |> print_endline in
    LambdaCalculus.interp SMap.empty (App (id (), Int 1)) |> value;
    [%expect {| (Int 1) |}]
end

(* A continuation-composing interpreter *)
(* https://ps-tuebingen-courses.github.io/pl1-lecture-notes/19-shift-reset/shift-reset.html *)
module CPS = struct
  type value =
    | Clo of env * var * expr
    | Int of int
    | Cont of cont
  [@@deriving show { with_path = false }]

  and cont = value -> ans
  and ans = value
  and env = value SMap.t

  (* interp : env -> expr -> (value -> ans) -> ans = *)
  (* can also use cont monad or let@ *)
  let rec interp : env -> expr -> cont -> ans =
   fun env e k ->
    match e with
    | Int i -> k (Int i)
    | Plus (e1, e2) ->
      interp env e1 (function
        | Int a1 ->
          interp env e2 (function
            | Int a2 -> k (Int (a1 + a2))
            | _ -> failwith "cannot add non-ints")
        | _ -> failwith "cannot add non-ints")
    | Var x -> k (SMap.find x env)
    | Abs (x, e) -> k (Clo (env, x, e))
    | App (e1, e2) ->
      interp env e1 (function
        | Cont k1 -> interp env e2 (fun v2 -> k (k1 v2))
        | Clo (envc, x, e3) ->
          interp env e2 (fun v2 -> interp (SMap.add x v2 envc) e3 k)
        | Int _ -> failwith "cannot apply non-lambda")
    | Shift (x, eb) ->
      let env1 = SMap.add x (Cont k) env in
      interp env1 eb Fun.id
    | Reset e -> k (interp env e Fun.id)

  let%expect_test _ =
    let show a = a |> [%derive.show: value] |> print_endline in
    let e =
      Plus
        ( Int 4,
          Reset
            (Plus
               ( Int 1,
                 Shift ("k", Plus (App (Var "k", Int 2), App (Var "k", Int 3)))
               )) )
    in
    interp SMap.empty e Fun.id |> show;
    [%expect {| (Int 11) |}]
end

(* CPSing the interpreter again makes this in pure CPS *)
(* https://harrisongoldste.in/papers/drafts/wpe-ii.pdf *)
module TwoCPS = struct
  type value =
    | Clo of env * var * expr
    | Int of int
    | Cont of cont
  [@@deriving show { with_path = false }]

  and metacont = value -> ans
  and ans = value
  and cont = value -> metacont -> ans
  and env = value SMap.t

  let rec interp : env -> expr -> cont -> metacont -> ans =
   fun env e k mk ->
    match e with
    | Int i -> k (Int i) mk
    | Plus (e1, e2) ->
      interp env e1
        (fun v1 mk1 ->
          match v1 with
          | Int a1 ->
            interp env e2
              (fun v2 mk2 ->
                match v2 with
                | Int a2 -> k (Int (a1 + a2)) mk2
                | _ -> failwith "cannot add non-ints")
              mk1
          | _ -> failwith "cannot add non-ints")
        mk
    | Var x -> k (SMap.find x env) mk
    | Abs (x, e) -> k (Clo (env, x, e)) mk
    | App (e1, e2) ->
      interp env e1
        (fun v1 mk ->
          match v1 with
          | Int _ -> failwith "cannot apply non-lambda"
          | Cont k1 ->
            interp env e2 (fun v2 mk1 -> k1 v2 (fun v3 -> k v3 mk1)) mk
          | Clo (envc, x, e3) ->
            interp env e2
              (fun v2 mk1 -> interp (SMap.add x v2 envc) e3 k mk1)
              mk)
        mk
    | Shift (x, eb) ->
      (* let env1 = SMap.add x (Cont (fun x mk1 -> k x (fun w -> mk1 w))) env in *)
      let env1 = SMap.add x (Cont k) env in
      interp env1 eb (fun x mk -> mk x) mk
    | Reset e -> interp env e (fun x mk1 -> mk1 x) (fun x -> k x mk)

  let%expect_test _ =
    let show a = a |> [%derive.show: value] |> print_endline in
    let e =
      Plus
        ( Int 4,
          Reset
            (Plus
               ( Int 1,
                 Shift ("k", Plus (App (Var "k", Int 2), App (Var "k", Int 3)))
               )) )
    in
    interp SMap.empty e (fun x mk -> mk x) Fun.id |> show;
    [%expect {| (Int 11) |}]
end
