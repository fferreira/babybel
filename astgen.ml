open Syntax
open Ast_convenience

let rec tp_to_ast = function
  | TConst c -> [%expr TConst [%e str c]]
  | Arr (s, t) -> [%expr Arr([%e tp_to_ast s], [%e tp_to_ast t])]

let decl_to_ast = function
  | c, Is_kind -> [%expr [%e str c], Is_kind]
  | c, Is_type t -> let ta = tp_to_ast t in [%expr [%e str c], Is_type [%e ta]]

let decls_to_ast ds = list (List.map decl_to_ast ds)
