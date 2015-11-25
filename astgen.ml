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
