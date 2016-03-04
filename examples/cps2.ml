open Sf

[@@@signature {def|

exp   : type.
value : type.

app   : exp -> exp -> exp.
lam   : (value -> exp) -> value.
ret   : value -> exp.

(* CPS representation *)

contra : type.
cvalue : type.
kont: type.

capp   : cvalue -> cvalue -> kont -> contra.
clam   : (cvalue -> kont -> contra) -> cvalue.

kk: (cvalue -> contra) -> kont.
adm: kont -> cvalue -> contra.

|def}]

type (_, _) rel
  = Empty : (nil, nil) rel
  | Both : ('g, 'd) rel -> (('g, tp_value base) cons, ('d, tp_cvalue base) cons) rel


let rec lookup [@type "g d . [g |- value] -> (g, d) rel -> [d |- cvalue]"] =
  fun t -> function
	| Empty -> assert false (* cannot lookup in an empty context *)
	| Both r' ->
	   begin match t with
		 | {p| *, x |- x |p} -> {t| *,x |- x |t}
		 | {p| *, x |- ##v |p} ->
		    let v1 =  lookup {t| #v |t} r'
		    in {t|*, x |- 'v1 [^1 ;] |t}
	   end


let rec cps [@type "g d . (g, d) rel -> [g |- value] -> [d |- cvalue]"] =
  fun r -> function
	| {p| #x |p} -> lookup {t| #x |t} r
	| {p| lam (\x. 'e) |p} ->
	   let ce = cpse (Both r) {t|g, x |-  'e  |t} in
	   {t| clam (\cv. \cc. 'ce[^2 ; cv ; cc]) |t}


and cpse [@type "g d. (g, d) rel -> [g |- exp] -> [d, k: kont |- contra]"] =
  fun r -> function
	| {p| ret 'v |p} ->
	   let vv = cps r {t| 'v |t} in
	   {t| *, k |- adm k ('vv[^1 ;]) |t}

	| {p| app 'm 'n |p} ->
	   let mm = cpse r m in
	   let nn = cpse r n in
	   {t| *, k |- 'mm [^1 ; (kk (\f. 'nn [^2 ; (kk (\x. capp f x k))]))] |t}
	| _ -> assert false

let id_fun = {t| lam (\x. ret x) |t}

let id_fun_k = cps Empty id_fun
