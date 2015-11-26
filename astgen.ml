open Sf
open Parsetree
open Ast_convenience

let rec tp_to_ast = function
  | TConst c -> [%expr TConst [%e str c]]
  | Arr (s, t) -> [%expr Arr([%e tp_to_ast s], [%e tp_to_ast t])]

let decl_to_ast = function
  | c, Is_kind -> [%expr [%e str c], Is_kind]
  | c, Is_type t -> let ta = tp_to_ast t in [%expr [%e str c], Is_type [%e ta]]

let decls_to_ast ds = list (List.map decl_to_ast ds)

let rec nor_to_ast = function
  | Lam (x, m) ->  [%expr Lam ([%e str x], [%e nor_to_ast m])]
  | Neu r -> [%expr Neu [%e neu_to_ast r ]]

and neu_to_ast = function
  | App (h, sp) -> [%expr App ([%e hd_to_ast h], [%e sp_to_ast sp])]

and hd_to_ast = function
  | Const c -> [%expr Const [%e str c]]
  | Var x -> [%expr Var [%e int x]]
  | Meta (u, s) -> [%expr Meta ([%e str u], [%e sub_to_ast s])]

and sp_to_ast = function
  | Empty -> [%expr Empty]
  | Cons (m, sp) -> [%expr Cons ([%e nor_to_ast m], [%e sp_to_ast sp])]

and sub_to_ast = function
  | Shift n -> [%expr Shift [%e int n]]
  | Dot (s, m) -> [%expr Dot ([%e sub_to_ast s], [%e nor_to_ast m])]



let rec nor_to_pat_ast = function
  | Lam (x, m) ->  [%pat? Lam ([%p pstr x], [%p nor_to_pat_ast m])]
  | Neu r -> [%pat? Neu [%p neu_to_pat_ast r ]]

and neu_to_pat_ast = function
  | App (h, sp) -> [%pat? App ([%p hd_to_pat_ast h], [%p sp_to_pat_ast sp])]

and hd_to_pat_ast = function
  | Const c -> [%pat? Const [%p pstr c]]
  | Var x -> [%pat? Var [%p pint x]]
  | Meta (u, s) ->		(* MMM this ignores s *)
     {ppat_desc = Ppat_var {txt = u ; loc = Location.none } ; ppat_loc = Location.none ; ppat_attributes = []}

and sp_to_pat_ast = function
  | Empty -> [%pat? Empty]
  | Cons (m, sp) -> [%pat? Cons ([%p nor_to_pat_ast m], [%p sp_to_pat_ast sp])]

and sub_to_pat_ast = function
  | Shift n -> [%pat? Shift [%p pint n]]
  | Dot (s, m) -> [%pat? Dot ([%p sub_to_pat_ast s], [%p nor_to_pat_ast m])]
