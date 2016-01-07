open Sf
open Parsetree
open Asttypes
open Ast_convenience

exception AST_gen_error of string

let rec tp_to_ast = function
  | TConst c -> [%expr TConst [%e str c]]
  | Arr (s, t) -> [%expr Arr([%e tp_to_ast s], [%e tp_to_ast t])]

let decl_to_ast = function
  | c, Is_kind -> [%expr [%e str c], Is_kind]
  | c, Is_type t -> let ta = tp_to_ast t in [%expr [%e str c], Is_type [%e ta]]

let decls_to_ast ds = list (List.map decl_to_ast ds)

let rec nor_to_ast = function
  | Lam m ->  [%expr Lam [%e nor_to_ast m]]
  | Neu r -> [%expr Neu [%e neu_to_ast r ]]
  | AppS (m, s) -> [%expr hsub_nor [%e sub_to_ast s] [%e nor_to_ast m]]
  | Meta (u, s) ->
     { pexp_desc = Pexp_ident { txt = Longident.parse u
			      ; loc = Location.none
			      }
     ; pexp_loc = Location.none
     ; pexp_attributes = []
     }

and neu_to_ast = function
  | App (h, sp) -> [%expr App ([%e hd_to_ast h], [%e sp_to_ast sp])]

and hd_to_ast = function
  | Const c -> [%expr Const [%e str c]]
  | Var x -> [%expr Var [%e int x]]

and sp_to_ast = function
  | Empty -> [%expr Empty]
  | Cons (m, sp) -> [%expr Cons ([%e nor_to_ast m], [%e sp_to_ast sp])]

and sub_to_ast = function
  | Shift n -> [%expr Shift [%e int n]]
  | Dot (s, m) -> [%expr Dot ([%e sub_to_ast s], [%e nor_to_ast m])]

let rec nor_to_pat_ast = function
  | Lam m ->  [%pat? Lam [%p nor_to_pat_ast m]]
  | Meta (u, s) ->
     { ppat_desc = Ppat_var {txt = u ; loc = Location.none }
     ; ppat_loc = Location.none
     ; ppat_attributes = []
     }
  | AppS _ -> raise (AST_gen_error "No explicit substitutions in patterns")
  | Neu r -> [%pat? Neu [%p neu_to_pat_ast r ]]

and neu_to_pat_ast = function
  | App (h, sp) -> [%pat? App ([%p hd_to_pat_ast h], [%p sp_to_pat_ast sp])]

and hd_to_pat_ast = function
  | Const c -> [%pat? Const [%p pstr c]]
  | Var x -> [%pat? Var [%p pint x]]

and sp_to_pat_ast = function
  | Empty -> [%pat? Empty]
  | Cons (m, sp) -> [%pat? Cons ([%p nor_to_pat_ast m], [%p sp_to_pat_ast sp])]

and sub_to_pat_ast = function
  | Shift n -> [%pat? Shift [%p pint n]]
  | Dot (s, m) -> [%pat? Dot ([%p sub_to_pat_ast s], [%p nor_to_pat_ast m])]

let rec typ_ann_to_ast = function
  | Syntax.BVars (vs, t) -> assert false
  | Syntax.Arr (t1, t2) -> [%type: [%t typ_ann_to_ast t1] -> [%t typ_ann_to_ast t2]]
  | Syntax.TAny -> [%type: _]
  | Syntax.CType _ -> [%type: Sf.nor]
