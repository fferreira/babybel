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

(* A type annotation with some free variables *)
type typ_ann_body
  = Arr of typ_ann_body * typ_ann_body
  | CType of ctx_tp * var
	(* the first one has type vars and the second one has type constructors *)
	| CoreType of Parsetree.core_type * Parsetree.core_type

(* type annotation with a list of quatified
   variables on the outside *)
type typ_ann = var list * typ_ann_body
