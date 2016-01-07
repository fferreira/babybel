(* The intrinsically typed second order syntactical framework *)

let a _ = assert false

(* Type level and singleton contexts *)
type (_, _) cons = Cons
type nil = Nil

type _ ctx
  = Empty : nil ctx
  | Dec : 'a ctx * 't -> (('a, 't) cons) ctx

(* Types *)

(* type name = string *)

(* type tp1 *)
(*   = Base of name *)
(*   | Arr1 of name * tp1 *)

(* type tp2 *)
(*   = Base of name *)
(*   | Arr2 of tp1 * tp2 *)

type _ base = B
type (_,_) arr = A

(* Terms *)

type (_,_) var =
  | Top : (('g , 'a base) cons, 'a base) var
  | Pop : ('g, 'a base) var -> (('g, 'b base) cons, 'a base) var

type (_,_,_) tm0
  = Var : ('g, 'a base) var -> ('s, 'g, 'a base) tm0
  | C : ('s, 't) var * ('s, 'g, 't,  'a base) sp -> ('s, 'g, 'a base) tm0

and (_,_,_,_) sp
  = Empty : ('s, 'g, 't, 't) sp
  | Cons : ('s, 'g, 't) tm1 * ('s, 'g, 't2, 't3) sp -> ('s, 'g, ('t1, 't2) arr, 't3) sp

and (_,_,_) tm1
  = Lam : ('s, ('g, 'a base) cons, 't) tm1 -> ('s, 'g, ('a base, 't) arr) tm1
  | Tm0 : ('s, 'g, 'a base) tm0 -> ('s, 'g, 'a base) tm1

(* Shifts of indices *)

type (_, _) shift
  = Id : ('g, 'g) shift
  | Suc : ('g, 'd) shift  -> ('g, ('d , 'a base) cons) shift

let rec shift_var : type g d a. (g, d) shift -> (g, a base) var -> (d, a base) var =
  fun sh v -> match sh with
	| Id -> v
	| Suc sh -> Pop (shift_var sh v)

let rec compose_shift : type g d e. (g, d) shift -> (d, e) shift -> (g, e) shift =
  fun sh -> function
	 | Id -> sh
	 | Suc shh -> Suc (compose_shift sh shh)

(* Renamings *)

type (_, _) ren
  = ShiftR : ('g, 'd) shift-> ('g, 'd) ren
  | DotR : ('g, 'd) ren * ('d, 'a base) var -> (('g, 'a base)cons, 'd) ren

let rec lookup_ren : type g d a. ((g, a base) var * (g, d) ren) -> (d, a base) var =
  function
  | Top, DotR (_, v') -> v'
  | Pop v, DotR (r, _) -> lookup_ren (v, r)
  | v, ShiftR sh -> shift_var sh v

let rec shift_ren : type g d e. (d, e) shift -> (g, d) ren -> (g , e) ren =
  fun sh -> function
	 | ShiftR sh' -> ShiftR (compose_shift sh' sh)
	 | DotR (r, v) -> DotR(shift_ren sh r, shift_var sh v)

let wkn_ren : type g d a. (g, d) ren -> ((g, a base) cons, (d, a base) cons) ren =
  fun s -> DotR(shift_ren (Suc Id) s, Top)

let rec ren_tm0 : type s g d t. (g, d) ren -> (s, g, t) tm0 -> (s, d, t) tm0 =
  fun r -> function
	| Var v -> Var (lookup_ren (v, r))
	| C (c, sp) -> C (c, ren_sp r sp)

and ren_sp : type s g d t t'. (g, d) ren -> (s, g, t, t') sp -> (s, d, t, t') sp =
  fun r -> function
	| Empty -> Empty
	| Cons (m, sp) -> Cons(ren_tm1 r m, ren_sp r sp)

and ren_tm1 : type s g d t. (g, d) ren -> (s, g, t) tm1 -> (s, d, t) tm1 =
  fun r -> function
	| Lam m -> Lam (ren_tm1 (wkn_ren r) m)
	| Tm0 n -> Tm0 (ren_tm0 r n)

let rec shift_tm0 : type s g d t. (g, d) shift -> (s, g, t) tm0 -> (s, d, t) tm0 =
  fun sh -> function
	 | Var v -> Var (shift_var sh v)
	 | C (c, sp) -> C (c, shift_sp sh sp)

and shift_sp : type s g d t t1. (g, d) shift -> (s, g, t, t1) sp -> (s, d, t, t1) sp =
  fun sh -> function
	 | Empty -> Empty
	 | Cons (m, sp) -> Cons (shift_tm1 sh m, shift_sp sh sp)

and shift_tm1 : type s g d t. (g, d) shift -> (s, g, t) tm1 -> (s, d, t) tm1 =
  fun sh -> function
	 | Lam m -> Lam (ren_tm1 (DotR (ShiftR (Suc sh), Top)) m)
	 | Tm0 n -> Tm0 (shift_tm0 sh n)

(* Substitutions *)

type (_,_,_) sub
  = Shift : ('g, 'd) shift-> ('s, 'g, 'd) sub
  | Dot : ('s, 'g, 'd) sub * ('s, 'd, 't) tm0 -> ('s, ('g, 't)cons, 'd) sub

let rec lookup : type s g d a. ((g, a base) var * (s, g, d) sub) -> (s, d, a base) tm0 =
  function
  | Top, Dot (_, n) -> n
  | Pop v, Dot (s, _) -> lookup (v, s)
  | v, Shift sh -> Var (shift_var sh v)

let rec shift_sub : type s g d e. (d, e) shift -> (s, g, d) sub -> (s, g , e) sub =
  fun sh -> function
	 | Shift sh' -> Shift (compose_shift sh' sh)
	 | Dot (s, n) -> Dot(shift_sub sh s, shift_tm0 sh n)

let wkn_sub : type s g d a. (s, g, d) sub -> (s, (g, a base) cons, (d, a base) cons) sub =
  fun s -> Dot(shift_sub (Suc Id) s, Var Top)

let rec sub_tm0 : type s g d t. (s, g, d) sub -> (s, g, t) tm0 -> (s, d, t) tm0 =
  fun s -> function
	| Var v -> lookup (v, s)
	| C (c, sp) -> C (c, sub_sp s sp)

and sub_sp : type s g d t t1. (s, g, d) sub -> (s, g, t, t1) sp -> (s, d, t, t1) sp =
  fun s -> function
	| Empty -> Empty
	| Cons (m, sp) -> Cons(sub_tm1 s m, sub_sp s sp)

and sub_tm1 : type s g d t. (s, g, d) sub -> (s, g, t) tm1 -> (s, d, t) tm1 =
  fun s -> function
	| Lam m -> Lam (sub_tm1 (wkn_sub s) m)
	| Tm0 n -> Tm0 (sub_tm0 s n)

(* Examples *)

let term_unit : ( (nil, unit base) cons , nil, unit base) tm0 = C (Top, Empty)
