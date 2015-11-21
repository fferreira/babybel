type constant = string

type tp
  = TConst of constant
  | Arr of tp * tp

type type_or_kind =
  | Is_kind
  | Is_type of tp

type decl = string * type_or_kind

type decls = decl list

let rec to_string _ = "some string"

(* examples *)

let tp = "tp", Is_kind
let nat = "nat", Is_type (TConst "tp")
let arr = "arr", Is_type (Arr (TConst "tp", TConst "tp"))
