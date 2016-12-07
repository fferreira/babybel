open Sf

[@@@signature {def|
tm: type.
app: tm -> tm -> tm.
lam: (tm -> tm) -> tm.

(* closure conversion *)

ctm: type.
btm: type.

capp: ctm -> ctm -> ctm.

let: {btm} -> (ctm -> ctm) -> ctm. (* lambdas are no longer in line in the term, they are always in let expressions *)

e: (ctm -> ctm) -> btm.
c: (ctm -> btm) -> btm.

sub : type.
empty: sub.
dot: sub -> ctm -> sub.

clo: ctm -> sub -> ctm.

|def}]

type (_, _) rel
  = Empty : (nil, nil) rel
  | Both : ('g, 'd) rel -> (('g, tp_tm base) cons, ('d, tp_ctm base) cons) rel

let rec lookup [@type "g d . [g |- tm] -> (g, d) rel -> [d |- ctm]"] =
  fun t -> function
	| Empty -> assert false (* cannot lookup in an empty context *)
	| Both r' ->
	   begin match t with
		 | {p| *,x |- x |p} -> {t| *,x |- x |t}
		 | {p| ##v |p} ->
		    let v1 =  lookup {t| #v |t} r'
		    in {t| *, x |- 'v1 [_] |t}
	   end



let rec close [@type "g d. (g, d) rel -> [d |- btm] -> [btm]"] =
  fun r m -> match r with
	     | Empty -> m
	     | Both r ->
	     	close r {t| c (\x. 'm) |t}

let rec envr [@type "g d. (g, d)rel -> [d |- sub]"] =
  fun r -> match r with
	   | Empty -> {t| empty |t}
	   | Both r ->
	      let s = envr r in
	      {t| *, x |- dot ('s[_]) x|t}

let rec conv [@type "g d. (g, d) rel -> [g |- tm] -> [d |- ctm]"] =
  fun r m -> match m with
	     | {p| lam (\x. 'm)  |p} ->
	     	let mc = conv (Both r) m in
	     	let mb = close r {t| e (\x. 'mc[_ ; x]) |t} in
	     	let s = envr r in
	     	{t| let {'mb} (\f. clo f ('s[_])) |t}
	     | {p| #x |p} ->
		lookup {t| #x |t} r
	     | {p| app 'm 'n |p} ->
		let mm = conv r m in
		let nn = conv r n in
		{t| capp 'mm 'nn |t}

type _ ctx
  = Em : nil ctx
  | Co : 'g ctx -> (('g, tp_ctm base) cons) ctx

let rec up [@type "d. d ctx -> [d |- ctm] -> [d |- ctm]"] =
  fun r -> function
	| {p| let 'b (\x. 'm) |p} ->
	   let mm = up (Co r) m in
	   {t| let 'b (\x. 'mm) |t}
