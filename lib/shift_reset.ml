(* Based on

  https://okmij.org/ftp/continuations/implementations.html
  https://okmij.org/ftp/Haskell/ShiftResetGenuine.hs
  https://www.cs.tsukuba.ac.jp/~kam/paper/aplas07.pdf *)

(* Parameterised monads *)
module type GM = sig
  type ('i, 'o, 'a) t

  (* pure values are polymorphic in the answer type *)
  val ret : 'tau -> ('a, 'a, 'tau) t

  (* bind composes changes in answer type *)
  val bind :
    ('b, 'g, 'sigma) t -> ('sigma -> ('a, 'b, 'tau) t) -> ('a, 'g, 'tau) t
end

module ShiftReset : sig
  include GM

  (** The type of functions that can cause ATM [sigma/a -> tau/b] *)
  type ('sigma, 'a, 'tau, 'b) fn = 'sigma -> ('a, 'b, 'tau) t

  val reset : ('sigma, 'tau, 'sigma) t -> ('a, 'a, 'tau) t

  (* the captured continuation is not just answer-type polymorphic, but pure *)
  val shift : (('tau -> 'a) -> ('s, 'b, 's) t) -> ('a, 'b, 'tau) t
  val run : ('tau, 'tau, 'tau) t -> 'tau
end = struct
  type ('i, 'o, 'a) t = C of (('a -> 'i) -> 'o) [@@unboxed]
  type ('sigma, 'a, 'tau, 'b) fn = 'sigma -> ('a, 'b, 'tau) t

  let unC (C f) = f
  let ret x = C (fun k -> k x)
  let bind (C f) h = C (fun k -> f (fun s -> unC (h s) k))
  let id = Fun.id
  let reset (C f) = C (fun k -> k (f id))
  let shift f = C (fun k -> unC (f k) id)
  let run (C f) = f id
end
