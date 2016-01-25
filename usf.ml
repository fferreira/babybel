(* Untyped 2nd order syntactical framework *)

type var = int
type name = string

type tp
  = TConst of name
  | Arr of tp * tp

type type_or_kind
  = Is_kind
  | Is_type of tp

type signature = (string * type_or_kind) list

type tm0
  = Var of int
  | C of name * sp

 and sp
   = Empty
   | Cons of tm1 * sp

 and tm1
   = Lam of tm1
   | Tm0 of tm0
   | Meta of name
   | Par of name
   | AppS of tm1 * sub

 and sub = int * tm1 list
