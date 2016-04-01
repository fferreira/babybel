(* Untyped 2nd order syntactical framework *)

type var = int
type name = string

type tp
  = TConst of name
  | Arr of tp * tp
  | TBox of tp

type type_or_kind
  = Is_kind
  | Is_type of tp

type signature = (string * type_or_kind) list

type sp
   = Empty
   | Cons of tm * sp

 and tm
   = Lam of tm
   | Meta of name
   | Par of name * int
   | AppS of tm * sub
   | Box of tm
   | Var of int
   | C of name * sp

 and sub = int * tm list
