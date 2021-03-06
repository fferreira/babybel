open Usf

open Syntax

exception Lookup_failure of string

let rec lookup_var x = function
  | Rest -> raise (Lookup_failure x)
  | TCons (_, y) when x = y -> 0
  | TCons (g, _) -> 1 + lookup_var x g

let is_var x c =
  try let _ = lookup_var x c in true
  with Lookup_failure _ -> false

let is_con x c sg = (not (is_var x c)) && (List.mem_assoc x sg)

exception Indexing_failure of string

let rec len = function
  | Rest -> 0
  | TCons (g, _) -> 1 + (len g)

let rec index_term (sg : signature) (c : ctx_tm) (m : term) : tm =
  match m with
  | Lam (x, m) -> Lam (index_term sg (TCons (c, x)) m)
  | App (Var x, []) when is_var x c -> Var (lookup_var x c)
  | App (Var x, sp) when is_con x c sg -> C (x, index_sp sg c sp)
  (* | App (Var _, _) -> raise (Indexing_failure "Higher order term not accepted!") *)
  (* | App (MVar x, sp) -> assert false *)
  | Var x when is_var x c -> Var (lookup_var x c)
  | Var x when is_con x c sg -> C (x, Empty)
  | Var x -> raise (Indexing_failure ("Unknown var/constructor: "^x))
  | MVar x -> Meta x
  | PVar (x, n) -> Par (x, n)
  | AppS (m, s') -> AppS(index_term sg c m, index_sub sg c s')
  (* terms inside boxed should be closed, so the
  recursive call to index_term should pass an empty context instead of
  c, but we get nicer errors if we let that fail in typecheckin *)
  | Box m -> Box(index_term sg c m)
  | _ -> raise (Indexing_failure "non-normal 2nd order term while indexing")

and index_sp sg c = function
  | [] -> Empty
  | m::ms -> Cons (index_term sg c m, index_sp sg c ms)

and index_sub sg c (sh, s) =
  match sh with
  | ShiftBy sh -> sh, List.map (index_term sg c) s
  | SomeShift -> len c, List.map (index_term sg c) s (* shift over everything in the context *)

let index (sg : signature) (g, m) : tm =
  index_term sg g m
