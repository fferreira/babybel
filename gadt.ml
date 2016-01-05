(* let a _ = assert false *)

type tp
  = Unit
  | Arr of tp * tp

(* type unitI *) (* we use the ocaml unit type for this *)

type (_, _) arr = Arr
type (_, _) cons = Cons
type nil = Nil

type (_, _) var =
  | Top : (('g , 't) cons, 't) var
  | Pop : ('g, 't) var -> (('g, 's) cons, 't) var

type (_, _) term
  = Lam : (('g,  's) cons, 't) term -> ('g, ('s ,'t) arr) term
  | App : ('g , ('a ,'b) arr) term * ('g , 'a) term -> ('g , 'b) term
  | Var : ('g, 't) var -> ('g, 't) term
  | C : ('g, unit) term

(* type _ ctx *)
(*   = Empty : unit ctx *)
(*   | Dec : 'a ctx * 't -> (('a, 't) cons) ctx *)

type (_, _) shift
  = Id : ('g, 'g) shift
  | Suc : ('g, 'd) shift  -> ('g, ('d , 't) cons) shift

let rec shift : type g d t. (g, t) var -> (g, d) shift -> (d, t) var =
  fun v -> function
	| Id -> v
	| Suc sh -> Pop (shift v sh)

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
  | v, ShiftR sh -> (shift v sh)

let rec shift_ren : type g d e. (d, e) shift -> (g, d) ren -> (g , e) ren =
  fun sh -> function
	 | ShiftR sh' -> ShiftR (compose_shift sh' sh)
	 | DotR (r, v) -> DotR(shift_ren sh r, shift v sh)

let wkn_ren : type g d t. (g, d) ren -> ((g, t) cons, (d, t) cons) ren =
  fun s -> DotR(shift_ren (Suc Id) s, Top)

let rec ren : type g d t. (g, t) term -> (g, d) ren -> (d, t) term =
  fun m r -> match m with
  | Lam e -> Lam (ren e (wkn_ren r))
  | App (f, e) -> App (ren f r, ren e r)
  | Var v -> Var(lookup_ren (v, r))
  | C -> C

type (_, _) sub
  = Shift : ('g, 'd) shift-> ('g, 'd) sub
  | Dot : ('g, 'd) sub * ('d, 't) term -> (('g, 't)cons, 'd) sub

let rec shift_term : type g d t. (g, d) shift -> (g, t) term -> (d, t) term =
  fun sh -> function
	    | Lam e -> Lam (ren e (DotR (ShiftR (Suc sh), Top)))
	    | App (f, e) -> App (shift_term sh f, shift_term sh e)
	    | Var v -> Var (shift v sh)
	    | C -> C

let rec shift_sub : type g d e. (d, e) shift -> (g, d) sub -> (g , e) sub =
  fun sh -> function
	 | Shift sh' -> Shift (compose_shift sh' sh)
	 | Dot (s, m) -> Dot(shift_sub sh s, shift_term sh m)

let wkn_sub : type g d t. (g, d) sub -> ((g, t) cons, (d, t) cons) sub =
  fun s -> Dot(shift_sub (Suc Id) s, Var Top)

let rec lookup : type g d t. ((g, t) var * (g, d) sub) -> (d, t) term =
  function
  | Top, Dot (_, m) -> m
  | Pop v, Dot (s, _) -> lookup (v, s)
  | v, Shift sh -> Var (shift v sh)

let rec sub : type g d t. (g, t) term -> (g, d) sub -> (d, t) term =
  fun m s -> match m with
  | Lam e -> Lam (sub e (wkn_sub s))
  | App (f, e) -> App (sub f s, sub e s)
  | Var v -> lookup (v, s)
  | C -> C
