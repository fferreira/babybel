(* fun with singletons! *)

type z = Z
type 'a s = S

type _ nat
  = Z : z nat
  | S : 'n nat -> ('n s) nat

type lftm = T
type lftp = T

type _ base
  = (* Bid : 'a nat -> 'a base *)
  | LFtm : lftm base
  | LFtp : lftp base

type (_, _) arr = A

type _ tp
  = Base : ('a base) tp
  | Arr : (('a, 'b) arr) tp

(* let rec to_int : type a. a nat -> int = *)
(*   function *)
(*   | Z -> 0 *)
(*   | S n -> 1 + to_int n *)

(* let rec of_int_0 : int -> z nat = *)
(*   fun n -> Z *)

type name = string

(* second order types *)
type tp1
  = Base of name
  | Arr1 of name * tp1

type tp2
  = Base of name
  | Arr2 of tp1 * tp2
