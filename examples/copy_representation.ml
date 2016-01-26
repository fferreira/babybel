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

type (_, _) rel =
  | Empty : (nil, nil) rel
  | Both : ('g, 'd) rel -> (('g, tp_tm base) cons, ('d, tp_tmc base) cons) rel


let rec copy [@type "g d . {|g |- tm|} -> (g, d) rel -> {|d |- tmc|}"] =
  fun x -> fun rel ->

					 match x with
  (* | {p| #x |p} -> {t| #x |t} *)
  | {p| c |p} -> {t| cc |t}
  | {p| app 'm 'n |p} ->
     let mc = copy m rel in
     let nc = copy n rel in
     {t| appc 'mc 'nc |t}
  (* | {p| lam (\x. 'm)  |p} -> *)
  (*    let mc = copy m rel y in *)
  (*    {t| lamc (\x. 'mc)  |t} *)
