open Sf

[@@@signature {def|
tm: type.
app: tm -> tm -> tm.
lam: (tm -> tm) -> tm.


ctm: type.
btm: type.

capp: ctm -> ctm -> ctm.
clam: {btm} -> ctm.

embed: ctm -> btm.
bind: (ctm -> btm) -> btm.

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
		    in {t| *, x |- 'v1 [^1 ;] |t}
	   end



let rec close [@type "g d. (g, d) rel -> [d |- btm] -> [btm]"] =
  fun r m -> match r with
	     | Empty -> m
	     | Both r ->
	     	close r {t| bind (\x. 'm) |t}

let rec envr [@type "g d. (g, d)rel -> [d |- sub]"] =
  fun r -> match r with
	   | Empty -> {t| empty |t}
	   | Both r ->
	      let s = envr r in
	      {t| *, x |- dot ('s[^1 ;]) x|t}


let rec conv [@type "g d. (g, d) rel -> [g |- tm] -> [d |- ctm]"] =
  fun r m -> match m with
	     | {p| lam (\x. 'm)  |p} ->
		let mc = conv (Both r) m in
		let mb = close r {t| bind (\x. embed 'mc) |t} in
		let s = envr r in
		{t| clo (clam {'mb}) 's |t}
	     | {p| #x |p} ->
		lookup {t| #x |t} r
	     | {p| app 'm 'n |p} ->
		let mm = conv r m in
		let nn = conv r n in
		{t| capp 'mm 'nn |t}

let t0 = {t| lam (\x. x)  |t}
let r0 = conv Empty t0

let t1 = {t| lam (\x. lam (\y. app x y)) |t}
let r1 = conv Empty t1
