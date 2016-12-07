open Usf
open Parsetree

type var = string

type shift_spec
  = ShiftBy of int
  | SomeShift

type term
  = Lam of var * term
  | App of term * (term list)
  | AppS of term * sub
  | Var of var
  | MVar of var
  | PVar of var * int
  | Box of term

 (* a shift and a list of terms to substitute for variables *)
 and sub = shift_spec * term list

(* the context in the contextual types *)
type ctx_tp
  = Empty
  | CtxVar of var
  | Cons of ctx_tp * var * Usf.tp

(* the context in the contextual terms *)
type ctx_tm
  = Rest
  | TCons of ctx_tm * var

type ctx_term = ctx_tm * term
