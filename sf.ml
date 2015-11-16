(* Syntactical framework *)

type constant = string

type tp
  = TConst of constant
  | Arr of tp * tp

type name = string

type var = int

type nor
  = Lam of name * nor
  | App of hd * sp  (* if we get more neutral terms, perhaps we should add a type for neutrals *)
and hd
   = Const of constant
   | Var of var
   | Meta of var * sub
and sp
  = Cons of nor * sp
  | Empty

and sub
  = Shift of int
  | Dot of sub * nor

type sign = (constant * tp) list (* signature for constantructos *)
type ctx = (name * tp) list (* contexts *)
type ctp = ctx * tp (* contextual type *)
type mctx = (name * ctp) list (* meta contexts *)

exception Lookup_failure

let rec lookup x c =
  try List.nth c x
  with Invalid_argument _ -> raise Lookup_failure

let nor_of_var x = App (Var x, Empty)
let top : nor = nor_of_var 0 (* The top variable in the context *)

let lookup_ctx x c = snd (lookup x c)

let rec append_sp (sp : sp) (m : nor) =
  match sp with
  | Empty -> Cons (m, Empty)
  | Cons (n, sp) -> Cons (n, append_sp sp m)

(* Type checking *)

exception Type_checking_failure

let rec check (si : sign) (cD : mctx) (c : ctx) (m : nor) (t: tp) : tp =
  match m, t with
  | Lam (x, m), Arr (s, t) ->
     let _ = check si cD ((x, s)::c) m t in
     Arr (s, t)
  | _ , _ -> if t = infer si cD c m then t else raise Type_checking_failure

and check_spine (si : sign) (cD : mctx) (c : ctx) (sp : sp) (t: tp) : tp =
  match sp, t with
  | Empty, _ -> t
  | Cons (m, sp'), Arr(s, t) ->
     let _ = check si cD c m s in
     check_spine si cD c sp' t
  | Cons _, _ -> raise Type_checking_failure

and check_sub  (si : sign) (cD : mctx) (c : ctx) (s : sub) (c' : ctx) : unit =
  match s, c' with
  | Shift 0, c' -> if c = c' then () else raise Type_checking_failure
  | Shift n, _::c' -> check_sub si cD c s c'
  | Dot (s, m), (_, t)::c' ->
     check si cD c m t ; check_sub si cD c s c'

and infer si cD c m =
  match m with
  | App (h, sp) ->
     let t = infer_head si cD c h in
     check_spine si cD c sp t
  (* if we get more neutral terms and a neutral type this case would disappear *)
  | Lam _ -> raise Type_checking_failure

and infer_head si cD c h =
  try match h with
  | Const a -> List.assoc a si
  | Var x -> lookup_ctx x c
  | Meta (u, s) ->
     let (c', t) = lookup_ctx u cD in
     check_sub si cD c s c' ; t
  with Not_found -> raise Type_checking_failure

let rec above (x : var) (y : var) : bool = x >= y

(* Simultaneous hereditary substitution *)

exception Violation (* this is an impossible case *)

let rec hsub_nor (s : sub) (n : nor) : nor =
  match n with
  | Lam (y, n) ->
     Lam (y, hsub_nor (Dot (shift_sub s, top)) n)
  | App (Var y, sp) -> app_spine (lookup_sub y s) (hsub_sp s sp)
  | App (Const a, sp) -> App (Const a, hsub_sp s sp)
  | App (Meta (u, s'), sp) -> App (Meta (u, comp_sub s s'), hsub_sp s sp)

and hsub_sp (s : sub) (sp : sp) : sp =
  match sp with
  | Empty -> Empty
  | Cons (n, sp) -> Cons(hsub_nor s n, hsub_sp s sp)

and app_spine (m : nor) (sp : sp) : nor =
  match sp with
  | Empty -> m
  | Cons (n, sp) -> app_spine (app_nor_to_nor m n) sp

and app_nor_to_nor (m : nor)(n : nor) : nor =
  match m with
  | Lam (z, m) -> hsub_nor (Dot (Shift 0, n)) m
  | App (m, sp) -> App(m, append_sp sp n)

and shift_nor (m : nor) = hsub_nor (Shift 1) m

and shift_sub (s : sub) =
  match s with
  | Shift n -> Shift (n + 1)
  | Dot (s, m) -> Dot (shift_sub s, shift_nor m)

and comp_sub (s : sub) (s' : sub) : sub =
  match s, s' with
  | Shift 0, _ -> s'
  | s, Shift 0 -> s
  | Shift n, Shift m -> Shift (n + m)
  | Shift n, Dot(s', _) -> comp_sub (Shift (n - 1)) s'
  | s, Dot(s', m) -> Dot(comp_sub s s', hsub_nor s m)
  | Dot (s, m), Shift n -> Dot(comp_sub s (Shift (n - 1)), shift_nor m) (* MMMM *)


and lookup_sub x s =
  match x, s with
  | _ , Shift n -> nor_of_var (x + n)
  | 0 , Dot (_, m) -> m
  | x , Dot(s, _) -> lookup_sub (x - 1) s

(* Some simple examples *)

let id = Lam ("x", App (Var 0, Empty)) ;;
let id_tp = Arr (TConst "T", TConst "T");;
let id_tc = check [] [] [] id id_tp

let f =  Lam ("x", App (Var 1, Cons (App (Var 0, Empty), Empty))) ;;
let f_tp = id_tp
let t_tc = check [] [] ["_", id_tp] f f_tp
let f' = hsub_nor (Shift 0) f
let res = f = f'
let _ = assert res

let f'' = hsub_nor (Dot (Shift 0, id)) f
let f''_tc = check [] [] [] f'' f_tp

(* Unification *)

type constr
  = Top
  | Bottom
  | UNor of ctx * nor * nor * tp
  | USp of unit
  | Sol of ctx * unit * nor * tp
