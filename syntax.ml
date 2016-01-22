open Usf

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

 (* a shift and a list of terms to substitute for variables *)
 and sub = int * term list
 (* and sub *)
 (*   = Shift of int *)
 (*   | Dot of term * sub *)

type ctx
  = Empty
  | CtxVar of var
  | Cons of ctx * var * Usf.tp

type ctx_term = ctx * term

(* A type annotation with some free variables *)
type typ_ann_body
  = Arr of typ_ann_body * typ_ann_body
  | TAny of var option
  | CType of ctx * var

(* type annotation with a list of quatified
   variables on the outside *)
type typ_ann = var list * typ_ann_body

(* examples *)

let tp = "tp", Is_kind
let nat = "nat", Is_type (TConst "tp")
let arr = "arr", Is_type (Arr (TConst "tp", TConst "tp"))
