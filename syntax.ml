open Usf
open Parsetree

type var = string

type term
  = Lam of var * term
  | App of term * (term list)
  | AppS of term * sub
  | Var of var
  | MVar of var
  | PVar of var * int

 (* a shift and a list of terms to substitute for variables *)
 and sub = int * term list

type ctx
  = Empty
  | CtxVar of var
  | Cons of ctx * var * Usf.tp option

type ctx_term = ctx * term

(* A type annotation with some free variables *)
type typ_ann_body
  = Arr of typ_ann_body * typ_ann_body
  | CType of ctx * var
	(* the first one has type vars and the second one has type constructors *)
	| CoreType of Parsetree.core_type * Parsetree.core_type

(* type annotation with a list of quatified
   variables on the outside *)
type typ_ann = var list * typ_ann_body

(* examples *)

let tp = "tp", Is_kind
let nat = "nat", Is_type (TConst "tp")
let arr = "arr", Is_type (Arr (TConst "tp", TConst "tp"))
