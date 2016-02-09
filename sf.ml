(* The intrinsically typed second order syntactical framework *)

type _ base = B
type (_,_) arr = A

(* Type level and singleton contexts *)
type (_, _) cons = Cons
type nil = Nil

type _ ctx
  = Empty : nil ctx
  | Dec : 'a ctx * 't -> (('a, 't) cons) ctx

(* The module for the syntactic framework *)

module SyntacticFramework (S : sig type _ constructor  val to_string : 'a constructor -> string end) = struct

    (* Terms *)
    type (_,_) var =
      | Top : (('g , 'a base) cons, 'a base) var
      | Pop : ('g, 'a base) var -> (('g, 'b base) cons, 'a base) var

    type (_,_) tm0
      = Var : ('g, 'a base) var -> ('g, 'a base) tm0
      | C : 't S.constructor * ('g, 't,  'a base) sp -> ('g, 'a base) tm0

     and (_,_,_) sp
       = Empty : ('g, 't, 't) sp
       | Cons : ('g, 't1) tm1 * ('g, 't2, 't3) sp -> ('g, ('t1, 't2) arr, 't3) sp

     and (_,_) tm1
       = Lam : (('g, 'a base) cons, 't) tm1 -> ('g, ('a base, 't) arr) tm1
       | Tm0 : ('g, 'a base) tm0 -> ('g, 'a base) tm1

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

    let rec ren_tm0 : type g d t. (g, d) ren -> (g, t) tm0 -> (d, t) tm0 =
      fun r -> function
	    | Var v -> Var (lookup_ren (v, r))
	    | C (c, sp) -> C (c, ren_sp r sp)

    and ren_sp : type g d t t'. (g, d) ren -> (g, t, t') sp -> (d, t, t') sp =
      fun r -> function
	    | Empty -> Empty
	    | Cons (m, sp) -> Cons(ren_tm1 r m, ren_sp r sp)

    and ren_tm1 : type g d t. (g, d) ren -> (g, t) tm1 -> (d, t) tm1 =
      fun r -> function
	    | Lam m -> Lam (ren_tm1 (wkn_ren r) m)
	    | Tm0 n -> Tm0 (ren_tm0 r n)

    let rec shift_tm0 : type g d t. (g, d) shift -> (g, t) tm0 -> (d, t) tm0 =
      fun sh -> function
	     | Var v -> Var (shift_var sh v)
	     | C (c, sp) -> C (c, shift_sp sh sp)

    and shift_sp : type g d t t1. (g, d) shift -> (g, t, t1) sp -> (d, t, t1) sp =
      fun sh -> function
	     | Empty -> Empty
	     | Cons (m, sp) -> Cons (shift_tm1 sh m, shift_sp sh sp)

    and shift_tm1 : type g d t. (g, d) shift -> (g, t) tm1 -> (d, t) tm1 =
      fun sh -> function
	     | Lam m -> Lam (ren_tm1 (DotR (ShiftR (Suc sh), Top)) m)
	     | Tm0 n -> Tm0 (shift_tm0 sh n)

    (* Substitutions *)

    type (_,_) sub
      = Shift : ('g, 'd) shift-> ('g, 'd) sub
      | Dot : ('g, 'd) sub * ('d, 't) tm1 -> (('g, 't)cons, 'd) sub

    let rec lookup : type g d a. ((g, a base) var * (g, d) sub) -> (d, a base) tm1 =
      function
      | Top, Dot (_, n) -> n
      | Pop v, Dot (s, _) -> lookup (v, s)
      | v, Shift sh -> Tm0 (Var (shift_var sh v))

    let rec shift_sub : type g d e. (d, e) shift -> (g, d) sub -> (g , e) sub =
      fun sh -> function
	     | Shift sh' -> Shift (compose_shift sh' sh)
	     | Dot (s, n) -> Dot(shift_sub sh s, shift_tm1 sh n)

    let wkn_sub : type g d a. (g, d) sub -> ((g, a base) cons, (d, a base) cons) sub =
      fun s -> Dot(shift_sub (Suc Id) s, Tm0 (Var Top))

    let rec sub_tm0 : type g d t. (g, d) sub -> (g, t) tm0 -> (d, t) tm1 =
      fun s -> function
	    | Var v -> lookup (v, s)
	    | C (c, sp) -> Tm0 (C (c, sub_sp s sp))

    and sub_sp : type g d t t1. (g, d) sub -> (g, t, t1) sp -> (d, t, t1) sp =
      fun s -> function
	    | Empty -> Empty
	    | Cons (m, sp) -> Cons(sub_tm1 s m, sub_sp s sp)

    and sub_tm1 : type g d t. (g, d) sub -> (g, t) tm1 -> (d, t) tm1 =
      fun s -> function
	    | Lam m -> Lam (sub_tm1 (wkn_sub s) m)
	    | Tm0 n -> sub_tm0 s n

    let single_subst : type g d s t. ((g, s) cons, t) tm1 -> (g, s) tm1 -> (g, t) tm1 =
      fun m n -> sub_tm1 (Dot (Shift Id, n)) m

     (* Pretty printer  *)

    let rec pp_tm1 : type g t . Format.formatter -> (g, t) tm1 -> unit =
      fun f t -> match t with
		 | Lam m -> Format.fprintf f "\\x. %a" pp_tm1 m
		 | Tm0 m -> pp_tm0 f m

    and pp_tm0 : type g t . Format.formatter -> (g, t) tm0 -> unit =
      fun f t -> match t with
		 | Var v -> pp_var f v
		 | C (c, sp) -> Format.fprintf f "%s %a" (S.to_string c) pp_sp sp
   and pp_sp : type g s t . Format.formatter -> (g, s, t) sp -> unit =
      fun f sp -> match sp with
		  | Empty -> ()
		  | Cons (m, Empty) -> Format.fprintf f "%a" pp_tm1 m
		  | Cons (m, sp) -> Format.fprintf f "(%a %a)" pp_tm1 m pp_sp sp
   and pp_var : type g t . Format.formatter -> (g, t) var -> unit =
      let rec var_to_int : type g t. (g, t) var -> int = function
	| Top -> 0
	| Pop v' -> 1 + var_to_int v'
      in
      fun f v -> Format.fprintf f "%d" (var_to_int v)
  end
