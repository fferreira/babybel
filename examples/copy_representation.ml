(* copy open terms in heterogeneous representations *)
open Sf

[@@@signature {def|
tm : type.
c : tm.
app : tm -> tm -> tm.
lam : (tm -> tm) -> tm.

tmc : type.
cc : tmc.
appc : tmc -> tmc -> tmc.
lamc : (tmc -> tmc) -> tmc.

|def}]

type (_, _) rel
  = Empty : (nil, nil) rel
  | Both : ('g, 'd) rel -> (('g, tp_tm base) cons, ('d, tp_tmc base) cons) rel


let rec lookup [@type "g d . [g |- tm] -> (g, d) rel -> [d |- tmc]"] =
  fun t -> function
	| Empty -> assert false (* cannot lookup in an empty context *)
	| Both r' ->
	   begin match t with
		 | {p| _,x |- x |p} -> {t| _,x |- x |t}
		 | {p| ##v |p} ->
		    let v1 =  lookup {t| #v |t} r'
		    in {t| _, x |- 'v1 [_] |t}
	   end

let rec copy [@type "g d . [g |- tm] -> (g, d) rel -> [d |- tmc]"] =
  fun x -> fun rel -> match x with
  | {p| #x |p} -> lookup {t| #x |t} rel
  | {p| c |p} -> {t| cc |t}
  | {p| app 'm 'n |p} ->
     let mc = copy m rel in
     let nc = copy n rel in
     {t| appc 'mc 'nc |t}
  | {p| lam (\x. 'm)  |p} ->
     let mc = copy m (Both rel) in
     {t| lamc (\x. 'mc)  |t}
