(* Syntactical framework *)

type const = string

type tp =
  TConst of const
  | Arr of tp * tp

type var = string

type nor =
  | Lam of var * nor
  | App of hd * sp  (* if we get more neutral terms, perhaps we should add a type for neutrals *)
and hd =
   | Const of const
   | Var of var
and sp =
  | Cons of nor * sp
  | Empty

type sign = (const * tp) list (* signature for constructos *)
(* MMM t_sign is not really needed... *)
type t_sign = const list (* signature for types (i.e: list of types) *)
type ctx = (var * tp) list (* contexts *)

let gen_sym =
  let x = ref 0 in
  fun () -> x := !x +1 ; "$" ^ string_of_int !x

let rec fv (m : nor) : var list =
  match m with
  | Lam (y, m) -> List.filter (fun x -> x <> y) (fv m)
  | App (Var x, sp) -> "x" :: fv_sp sp
  | App (_, sp) -> fv_sp sp

and fv_sp (sp : sp) : var list =
  match sp with
  | Empty -> []
  | Cons (m, sp) -> fv m @ fv_sp sp

(* Type checking *)

exception TypeCheckingFailure

let rec check (st : t_sign) (si : sign) (c : ctx) (m : nor) (t: tp) : tp =
  match m, t with
  | Lam (x, m), Arr (s, t) -> check st si ((x, s)::c) m t
  | _ , _ -> if t = infer st si c m then t else raise TypeCheckingFailure

and check_spine st si c sp t =
  match sp, t with
  | Empty, _ -> t
  | Cons (m, sp'), Arr(s, t) ->
     let _ = check st si c m s in
     check_spine st si c sp' t

and infer st si c m =
  match m with
  | App (h, sp) ->
     let t = infer_head st si c h in
     check_spine st si c sp t

and infer_head st si c h =
  try match h with
  | Const a -> List.assoc a si
  | Var x -> List.assoc x c
  with Not_found -> raise TypeCheckingFailure

(* Hereditary substitution *)

exception Violation (* this is an impossible case *)

(* rename free variable x to y in m *)
let rec ren (x, y : var * var) (m : nor) : nor =
  match m with
  | Lam (z, m) when z = x -> Lam (z, m)
  | Lam (z, m) -> Lam (z, ren (x, y) m)
  | App (Var z, sp) when z = x -> App(Var y, ren_sp (x, y) sp)
  | App (h, sp) -> App(h, ren_sp (x, y) sp)

and ren_sp (s : var * var) (sp : sp) : sp =
  match sp with
  | Empty -> Empty
  | Cons (m, sp) -> Cons (ren s m, ren_sp s sp)

(* substitute m for x in n *)
let rec hsub_nor (x , m : var * nor) (n : nor) : nor =
  match n with
  | Lam (y, n) ->
     if List.mem y (fv m)
     then let z = gen_sym() in hsub_nor (x, m) (Lam (z, ren (y, z) n))
     else if (x = y)
     then Lam (y, n)
     else Lam (y, hsub_nor (x, m) n)
  | App (Const a, sp) -> App (Const a, hsub_sp (x, m) sp)
  | App (Var y, sp) when x = y -> app_spine m (hsub_sp (x, m) sp)
  | App (Var y, sp) ->  App (Var y, hsub_sp (x, m) sp)

and hsub_sp (x, m  : var * nor) (sp : sp) : sp =
  match sp with
  | Empty -> Empty
  | Cons (n, sp) -> Cons(hsub_nor (x, m) n, hsub_sp (x, m) sp)

and app_spine (m : nor) (sp : sp) : nor =
  match sp with
  | Empty -> m
  | Cons (n, sp) -> app_spine (app_nor_to_nor m n) sp

and app_nor_to_nor (m : nor)(n : nor) : nor =
  match m with
  | Lam (z, m) -> hsub_nor (z, n) m
  (* MMM still thinking whether this is a violation (aka impossible)
     what about non eta long constructors *)
  | _ -> raise Violation

(* Some simple examples *)

let id = Lam ("x", App (Var "x", Empty)) ;;
let id_tp = Arr (TConst "T", TConst "T");;
let id_tc = check ["T"] [] [] id id_tp

let f =  Lam ("x", App (Var "f", Cons (App (Var "x", Empty), Empty))) ;;
let f' = hsub_nor ("f", id) f
