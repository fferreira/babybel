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

type _ ctx
  = Empty : unit ctx
  | Dec : 'a ctx * 't -> (('a, 't) cons) ctx

type (_, _) ren
  = EmR : (nil, 'd) ren
  | DotR : ('g, 'd) ren * ('d, 't) var -> (('g, 't)cons, 'd) ren

let rec wkn_ren_im : type g d t. (g, d) ren -> (g, (d, t) cons) ren =
  function
  | EmR -> EmR
  | DotR (r, v) -> DotR (wkn_ren_im r, Pop v)

let wkn_ren : type g d t. (g, d) ren -> ((g, t) cons, (d, t) cons) ren =
  fun r -> DotR (wkn_ren_im r, Top)

let ren : type g d t. (g, t) term -> (g, d) ren -> (d, t) term =
  fun m r -> assert false

let wkn_term : type g s t. (g, t) term -> ((g, s) cons, t) term =
  fun m -> assert false

type (_, _) sub
  = Em : (nil, 'd) sub (* Optionally: | Em : (nil, 'd) sub *)
  | Dot : ('g, 'd) sub * ('d, 't) term -> (('g, 't)cons, 'd) sub

let rec wkn_sub_im : type g d t. (g, d) sub -> (g, (d, t) cons) sub =
  function
  | Em -> Em
  | Dot (s, m) -> Dot(wkn_sub_im s, wkn_term m)

let wkn_sub : type g d t. (g, d) sub -> ((g, t) cons, (d, t) cons) sub =
  fun s -> Dot (wkn_sub_im s, Var Top)

let rec size : type g t. (g, t) term -> int =
  function
  | Lam e -> 1 + size e
  | App (f, e) -> size f + size e
  | Var _ -> 1
  | C -> 1

let rec lookup : type g d t. ((g, t) var * (g, d) sub) -> (d, t) term =
  function
  | Top, Dot (_, m) -> m
  | Pop v, Dot (s, _) -> lookup (v, s)

let rec sub : type g d t. g ctx -> (g, t) term -> (g, d) sub -> (d, t) term =
  fun g m s -> match m with
  | Lam e -> Lam (sub (assert false) e (wkn_sub s))
  | App (f, e) -> App (sub g f s, sub g e s)
  | Var v -> lookup (v, s)
  | C -> C
