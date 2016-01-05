(* The intrinsically typed syntactical framework *)

let a _ = assert false

type tp
  = Unit
  | Arr of tp * tp

type (_, _) arr = Arr
type (_, _) cons = Cons
type nil = Nil

type (_, _) var =
  | Top : (('g , 't) cons, 't) var
  | Pop : ('g, 't) var -> (('g, 's) cons, 't) var

type (_, _) nor
  = Lam : (('g,  's) cons, 't) nor -> ('g, ('s ,'t) arr) nor
  | Neu : ('g, 't) neu -> ('g, 't) nor

 and (_,_) neu
   = App : ('g, 's) hd * ('g, 's, 't) sp -> ('g, 't) neu (* TODO we need to force 't to be a base type to be eta long *)

 and (_,_) hd
   = Var : ('g, 't) var -> ('g, 't) hd
   | C : ('g, unit) hd

 (* the indices are: the context, the type that needs to produce the final type *)
 and (_,_,_) sp
   = Cons : ('g, 's) nor * ('g, 't, 'w) sp -> ('g, ('s , 't) arr, 'w) sp
   | Empty : ('g, 't, 't) sp

(* type _ ctx *)
(*   = Empty : unit ctx *)
(*   | Dec : 'a ctx * 't -> (('a, 't) cons) ctx *)

type (_, _) shift
  = Id : ('g, 'g) shift
  | Suc : ('g, 'd) shift  -> ('g, ('d , 't) cons) shift


let rec shift_var : type g d t. (g, d) shift -> (g, t) var -> (d, t) var =
  fun sh v -> match sh with
	| Id -> v
	| Suc sh -> Pop (shift_var sh v)

let rec compose_shift : type g d e. (g, d) shift -> (d, e) shift -> (g, e) shift =
  fun sh -> function
	 | Id -> sh
	 | Suc shh -> Suc (compose_shift sh shh)

type (_, _) ren
  = ShiftR : ('g, 'd) shift-> ('g, 'd) ren
  | DotR : ('g, 'd) ren * ('d, 't) var -> (('g, 't)cons, 'd) ren

let rec lookup_ren : type g d t. ((g, t) var * (g, d) ren) -> (d, t) var =
  function
  | Top, DotR (_, v') -> v'
  | Pop v, DotR (r, _) -> lookup_ren (v, r)
  | v, ShiftR sh -> (shift_var sh v)

let rec shift_ren : type g d e. (d, e) shift -> (g, d) ren -> (g , e) ren =
  fun sh -> function
	 | ShiftR sh' -> ShiftR (compose_shift sh' sh)
	 | DotR (r, v) -> DotR(shift_ren sh r, shift_var sh v)

let wkn_ren : type g d t. (g, d) ren -> ((g, t) cons, (d, t) cons) ren =
  fun s -> DotR(shift_ren (Suc Id) s, Top)

let rec ren : type g d t. (g, d) ren -> (g, t) nor -> (d, t) nor =
  fun r -> function
	| Lam m -> Lam (ren (wkn_ren r) m)
	| Neu n -> Neu (ren_neu r n)

and ren_neu : type g d t. (g, d) ren -> (g, t) neu -> (d, t) neu =
  fun r -> function
	| App (h, sp) -> App(ren_hd r h, ren_sp r sp)

and ren_hd : type g d t. (g, d) ren -> (g, t) hd -> (d, t) hd =
  fun r -> function
	| Var v -> Var (lookup_ren (v, r))
	| C -> C

and ren_sp : type g d s t. (g, d) ren -> (g, s, t) sp -> (d, s, t) sp =
  fun r -> function
	| Empty -> Empty
	| Cons (m, sp) -> Cons (ren r m, ren_sp r sp)

type (_, _) sub
  = Shift : ('g, 'd) shift-> ('g, 'd) sub
  | Dot : ('g, 'd) sub * ('d, 't) nor -> (('g, 't)cons, 'd) sub

let rec shift_nor : type g d t. (g, d) shift -> (g, t) nor -> (d, t) nor =
  fun sh -> function
	 | Lam m -> Lam (ren (DotR (ShiftR (Suc sh), Top)) m)
	 | Neu n -> Neu (shift_neu sh n)

and shift_neu : type g d t. (g, d) shift -> (g, t) neu -> (d, t) neu =
  fun sh -> function
	 | App (h, sp) -> App (shift_hd sh h, shift_sp sh sp)

and shift_hd : type g d t. (g, d) shift -> (g, t) hd -> (d, t) hd =
  fun sh -> function
	 | Var v -> Var (shift_var sh v)
	 | C -> C

and shift_sp : type g d s t. (g, d) shift -> (g, s, t) sp -> (d, s, t) sp =
  fun sh -> function
	 | Cons (m, sp) -> Cons (shift_nor sh m, shift_sp sh sp)
	 | Empty -> Empty

let rec shift_sub : type g d e. (d, e) shift -> (g, d) sub -> (g , e) sub =
  fun sh -> function
	 | Shift sh' -> Shift (compose_shift sh' sh)
	 | Dot (s, m) -> Dot(shift_sub sh s, shift_nor sh m)

let wkn_sub : type g d t. (g, d) sub -> ((g, t) cons, (d, t) cons) sub =
  fun s -> Dot(shift_sub (Suc Id) s, Neu(App (Var Top, Empty)))

let rec lookup : type g d t. ((g, t) var * (g, d) sub) -> (d, t) nor =
  function
  | Top, Dot (_, m) -> m
  | Pop v, Dot (s, _) -> lookup (v, s)
  | v, Shift sh -> Neu(App(Var (shift_var sh v), Empty))

let rec sub_nor : type g d t. (g, d) sub -> (g, t) nor -> (d, t) nor =
  fun s -> function
	| Lam m -> Lam (sub_nor (wkn_sub s) m)
	| Neu(App (Var v, sp)) -> app_sp (lookup (v, s)) (a 1)
	| Neu(App (C, sp)) -> Neu(App (C, sub_sp s sp))

and sub_sp : type g d s t. (g, d) sub -> (g, s, t) sp -> (d, s, t) sp =
  fun s -> function
	| Empty -> Empty
	| Cons(m, sp) -> Cons(sub_nor s m, sub_sp s sp)

and app_sp : type g d s t. (g, s) nor -> (g, s, t) sp -> (g, t) nor =
  fun m -> function
	| Empty -> m
	| Cons (n, sp) -> app_sp (app_nor_nor m n) sp

and app_nor_nor : type g d s t. (g, (s, t) arr) nor -> (g, s) nor -> (g, t) nor =
  fun m n -> match m with
	     | Lam m -> sub_nor (Dot (Shift Id, n)) m
	     | Neu(App(m, sp)) -> Neu (App (m, append_sp sp n))

		   (* MMM this looks not eta long... *)
and append_sp : type g d s t w. (g, w, (s, t) arr) sp -> (g, s) nor -> (g, w, t) sp =
  fun sp m -> match sp with
	      | Empty -> Cons (m, Empty)
	      | Cons(n, sp) -> Cons (n, append_sp sp m)
