open Usf

type hat_ctx = string list

exception Lookup_failure of string

let rec lookup_var x = function
  | [] -> raise (Lookup_failure x)
  | y::_ when x = y -> 0
  | _::ys -> 1+ lookup_var x ys

let is_var x c =
  try let _ = lookup_var x c in true
  with Lookup_failure _ -> false

let is_con x c sg = (not (is_var x c)) && (List.mem_assoc x sg)

exception Indexing_failure of string

let rec index_term (sg : signature) (c : hat_ctx) (m : Syntax.term) : tm1 =
  match m with
  | Syntax.Lam (x, m) -> Lam (index_term sg (x :: c) m)
  | Syntax.App (Syntax.Var x, []) when is_var x c -> Tm0 (Var (lookup_var x c))
  | Syntax.App (Syntax.Var x, sp) when is_con x c sg -> Tm0 (C (x, index_sp sg c sp))
  (* | Syntax.App (Syntax.Var _, _) -> raise (Indexign_failure "Higher order term not accepted!") *)
  (* | Syntax.App (Syntax.MVar x, sp) -> assert false *)
  | Syntax.Var x when is_var x c -> Tm0 (Var (lookup_var x c))
  | Syntax.Var x when is_con x c sg -> Tm0 (C (x, Empty))
  | Syntax.MVar x -> Meta x
  | Syntax.AppS (m, s') -> AppS(index_term sg c m, index_sub sg c s')
  | _ -> raise (Indexing_failure "non-normal 2nd order term while indexing")

and index_sp sg c = function
  | [] -> Empty
  | m::ms -> Cons (index_term sg c m, index_sp sg c ms)

and index_sub sg c (sh, s) = sh, List.map (index_term sg c) s

let index (sg : signature) (g, m) : tm1 =
  let rec ctx_to_hat = function
    | Syntax.CtxVar _
    | Syntax.Empty -> []
    | Syntax.Cons (g, x, _) -> x :: ctx_to_hat g
  in
  index_term sg (ctx_to_hat g) m
