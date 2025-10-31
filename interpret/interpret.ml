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
module Simple = struct
  type value =
    | Lambda of var * expr
    | Int of int

  type env = value SMap.t

  let rec interp : env -> expr -> value =
   fun env -> function
    | Int i -> Int i
    | Plus (e1, e2) ->
      (match interp env e1 with
      | Int a1 ->
        (match interp env e2 with
        | Int a2 -> Int (a1 + a2)
        | _ -> failwith "cannot add non-ints")
      | _ -> failwith "cannot add non-ints")
    | Var x -> SMap.find x env
    | Abs (x, e) -> Lambda (x, e)
    | App (e1, e2) ->
      (match interp env e1 with
      | Lambda (x, e3) ->
        let v = interp env e2 in
        let env1 = SMap.add x v env in
        interp env1 e3
      | _ -> failwith "cannot apply non-lambda")
    | Shift (_, _) | Reset _ -> failwith "cannot be implemented"
end

(* A continuation-composing interpreter *)
(* https://ps-tuebingen-courses.github.io/pl1-lecture-notes/19-shift-reset/shift-reset.html *)
module CPS = struct
  type value =
    | Lambda of var * expr
    | Int of int
    | Cont of cont
  [@@deriving show { with_path = false }]

  and cont = value -> ans
  and ans = value

  type env = value SMap.t

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
    | Abs (x, e) -> k (Lambda (x, e))
    | App (e1, e2) ->
      interp env e1 (function
        | Cont k1 -> interp env e2 (fun v2 -> k (k1 v2))
        | Lambda (x, e3) ->
          interp env e2 (fun v2 ->
              let env1 = SMap.add x v2 env in
              interp env1 e3 k)
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
    | Lambda of var * expr
    | Int of int
    | Cont of cont
  [@@deriving show { with_path = false }]

  and metacont = value -> ans
  and ans = value
  and cont = value -> metacont -> ans

  type env = value SMap.t

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
    | Abs (x, e) -> k (Lambda (x, e)) mk
    | App (e1, e2) ->
      interp env e1
        (fun v1 mk ->
          match v1 with
          | Int _ -> failwith "cannot apply non-lambda"
          | Cont k1 ->
            interp env e2 (fun v2 mk1 -> k1 v2 (fun v3 -> k v3 mk1)) mk
          | Lambda (x, e3) ->
            interp env e2 (fun v2 mk1 -> interp (SMap.add x v2 env) e3 k mk1) mk)
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
