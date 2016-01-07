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
  | AppS of term * sub
  | Var of var
  | MVar of var

 and sub
   = term * int

type ctx = (var * tp) list

type ctx_term = ctx * term

type typ_ann
  = BVars of var list * typ_ann
  | Arr of typ_ann * typ_ann
  | TAny
  | CType of var

(* examples *)

let tp = "tp", Is_kind
let nat = "nat", Is_type (TConst "tp")
let arr = "arr", Is_type (Arr (TConst "tp", TConst "tp"))
