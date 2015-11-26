open Syntax
open Ast_convenience

let rec tp_to_ast = function
  | TConst c -> [%expr TConst [%e str c]]
  | Arr (s, t) -> [%expr Arr([%e tp_to_ast s], [%e tp_to_ast t])]

let decl_to_ast = function
  | c, Is_kind -> [%expr [%e str c], Is_kind]
  | c, Is_type t -> let ta = tp_to_ast t in [%expr [%e str c], Is_type [%e ta]]

let decls_to_ast ds = list (List.map decl_to_ast ds)

let rec term_to_ast = function
  | Lam (x, m) -> [%expr Lam ([%e str x], [%e term_to_ast m])]
  | App (h, sp) -> [%expr App ([%e term_to_ast h], [%e list (List.map term_to_ast sp)])]
  | Var x -> [%expr Var [%e str x]]
  | MVar x -> [%expr MVar [%e str x]]

let rec term_to_pat_ast = function
  | Lam (x, m) -> [%pat? Lam ([%p pstr x], [%p term_to_pat_ast m])]
  | App (h, sp) -> [%pat? App ([%p term_to_pat_ast h], [%p plist (List.map term_to_pat_ast sp)])]
  | Var x -> [%pat? Var [%p pstr x]]
  | MVar x -> {ppat_desc = Ppat_var {txt = x ; loc = Location.none } ; ppat_loc = Location.none ; ppat_attributes = []}
