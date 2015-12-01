open Sf


type hat_ctx = string list

exception Lookup_failure of string

let rec lookup_var x = function
  | [] -> raise (Lookup_failure x)
  | y::_ when x = y -> 0
  | _::ys -> 1+ lookup_var x ys

let rec lookup_var_const s c x =
  try Var (lookup_var x c)
  with Lookup_failure _ ->
    if List.mem_assoc x s
    then Const x
    else raise (Lookup_failure x)

exception Indexing_failure of string

let rec index (s : signature) (c : hat_ctx) (m : Syntax.term) : nor =
  match m with
  | Syntax.Lam (x, m) -> Lam (x, index s (x :: c) m)
  | Syntax.App (Syntax.Var x, sp) -> Neu(App (lookup_var_const s c x, index_sp s c sp))
  | Syntax.App (Syntax.MVar x, sp) -> assert false
  | Syntax.Var x -> Neu(App (lookup_var_const s c x, Empty))
  | Syntax.MVar x -> Meta (x, Shift 0)
  | _ -> raise (Indexing_failure "non-normal term while indexing")

and index_sp s c = function
  | [] -> Empty
  | m::ms -> Cons (index s c m, index_sp s c ms)
