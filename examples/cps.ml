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
ccont  : type.

capp   : cvalue -> cvalue -> ccont -> contra.
clam   : (cvalue -> ccont -> contra) -> cvalue.
cconti : (cvalue -> contra) -> ccont.
cthrow : ccont -> cvalue -> contra.

|def}]

type (_, _) rel
  = Empty : (nil, nil) rel
  | Both : ('g, 'd) rel -> (('g, tp_value base) cons, ('d, tp_cvalue base) cons) rel


let rec lookup [@type "g d . [g |- value] -> (g, d) rel -> [d |- cvalue]"] =
  fun t -> function
	| Empty -> assert false (* cannot lookup in an empty context *)
	| Both r' ->
	   begin match t with
		 | {p| _, x |- x |p} -> {t| _, x |- x |t}
		 | {p| _, x |- ##v |p} ->
		    let v1 =  lookup {t| #v |t} r'
		    in {t|_, x |- 'v1 [_] |t}
	   end

let rec cps [@type "g d . (g, d) rel -> [g |- value] -> [d |- cvalue]"] =
  fun r -> function
	| {p| #x |p} -> lookup {t| #x |t} r
	| {p| lam (\x. 'e) |p} ->
	   let ce = cpse (Both r) {t|_, x |-  'e  |t} in
	   {t| _ |- clam (\cv. \cc. 'ce[_; cv ; cc]) |t}

and cpse [@type "g d. (g, d) rel -> [g |- exp] -> [d, k:ccont |- contra]"] =
  fun r -> function
	| {p| ret 'v |p} ->
	   let v1 = cps r {t| 'v |t} in
	   {t| _, k |- cthrow k ('v1 [_]) |t}
	| {p| app 'm 'n |p} ->
	   let m1 = cpse r m in
	   let n1 = cpse r n in
	   {t| _, k |- 'm1 [_ ; (cconti (\f. 'n1[_ ;(cconti (\x. capp f x k))]))] |t}

let id_fun = {t| lam (\x. app (ret x) (ret x)) |t}

let id_fun_k = cps Empty id_fun
