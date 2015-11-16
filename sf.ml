(* Syntactical framework *)

type const = string

type tp =
  TConst of const
  | Arr of tp * tp

type name = string

type var = Top
	 | Pop of var

type nor =
  | Lam of name * nor
  | App of hd * sp  (* if we get more neutral terms, perhaps we should add a type for neutrals *)
and hd =
   | Const of const
   | Var of var
and sp =
  | Cons of nor * sp
  | Empty

type sub =
  | Id
  | Shift
  | Dot of sub * nor
  | Comp of sub * sub

type sign = (const * tp) list (* signature for constructos *)
type ctx = (name * tp) list (* contexts *)

exception Lookup_failure

let rec lookup x c =
  match x, c with
  | Top, c :: _ -> c
  | Pop x, _ :: cs -> lookup x cs
  | _ -> raise Lookup_failure

let nor_of_var x = App (Var x, Empty)
let top : nor = nor_of_var Top (* The top variable in the context *)

let lookup_ctx x c = snd (lookup x c)

let rec append_sp (sp : sp) (m : nor) =
  match sp with
  | Empty -> Cons (m, Empty)
  | Cons (n, sp) -> Cons (n, append_sp sp m)

(* Type checking *)

exception Type_checking_failure

let rec check (si : sign) (c : ctx) (m : nor) (t: tp) : tp =
  match m, t with
  | Lam (x, m), Arr (s, t) ->
     let _ = check si ((x, s)::c) m t in
     Arr (s, t)
  | _ , _ -> if t = infer si c m then t else raise Type_checking_failure

and check_spine (si : sign) (c : ctx) (sp : sp) (t: tp) : tp =
  match sp, t with
  | Empty, _ -> t
  | Cons (m, sp'), Arr(s, t) ->
     let _ = check si c m s in
     check_spine si c sp' t
  | Cons _, _ -> raise Type_checking_failure

and infer si c m =
  match m with
  | App (h, sp) ->
     let t = infer_head si c h in
     check_spine si c sp t
  (* if we get more neutral terms and a neutral type this case would disappear *)
  | Lam _ -> raise Type_checking_failure

and infer_head si c h =
  try match h with
  | Const a -> List.assoc a si
  | Var x -> lookup_ctx x c
  with Not_found -> raise Type_checking_failure

let rec above (x : var) (y : var) : bool = x >= y

(* Simultaneous hereditary substitution *)

exception Violation (* this is an impossible case *)

let rec hsub_nor (s : sub) (n : nor) : nor =
  match n with
  | Lam (y, n) ->
     Lam (y, hsub_nor (Dot (Comp(Shift, s), top)) n)
  | App (Const a, sp) -> App (Const a, hsub_sp s sp)
  | App (Var y, sp) -> app_spine (lookup_sub y s) (hsub_sp s sp)

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
  | Lam (z, m) -> hsub_nor (Dot (Id, n)) m
  | App (m, sp) -> App(m, append_sp sp n)

and lookup_sub x s =
  match x, s with
  | _ , Id -> nor_of_var x
  | _ , Shift -> nor_of_var (Pop x)
  | Top , Dot (_, m) -> m
  | Pop x , Dot(s, _) -> lookup_sub x s
  | _ , Comp(s, s') -> hsub_nor s (lookup_sub x s')

(* Some simple examples *)

let id = Lam ("x", App (Var Top, Empty)) ;;
let id_tp = Arr (TConst "T", TConst "T");;
let id_tc = check [] [] id id_tp

let f =  Lam ("x", App (Var (Pop Top), Cons (App (Var Top, Empty), Empty))) ;;
let f_tp = id_tp
let t_tc = check [] ["_", id_tp] f f_tp
let f' = hsub_nor Id f
let res = f = f'
let f'' = hsub_nor (Dot (Id, id)) f
let f''_tc = check [] [] f'' f_tp
