open Sf

(* type constant = string *)

(* type tp *)
(*   = TConst of constant *)
(*   | Arr of tp * tp *)


(* type decl = string * type_or_kind *)

(* type decls = decl list *)

type var = string

type term
  = Lam of var * term
  | App of term * (term list)
  | Var of var
  | MVar of var
  | Subst of term * sub

 and sub
   = term * int

type ctx = (var * tp) list

type ctx_term = ctx * term

(* examples *)

let tp = "tp", Is_kind
let nat = "nat", Is_type (TConst "tp")
let arr = "arr", Is_type (Arr (TConst "tp", TConst "tp"))
