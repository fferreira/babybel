open Sf

[@@@signature {def|
tp: type.
nat : tp.
arr : tp -> tp -> tp.

tm : type.
z : tm.
s : tm -> tm.
cas : tm -> tm -> (tm -> tm) -> tm.
app : tm -> tm -> tm.
lam : tp -> (tm -> tm) -> tm.
fix : tp -> (tm -> tm) -> tm.
|def}]

type _ ctx
  = Empty : nil ctx
  (*       V-- this *)
  | Cons : ('g, tp_tp base) tm1  * 'g ctx -> (('g, tp_tm base) cons) ctx

let rec tp_check [@type "g. g ctx -> [g |- tm] -> [tp]"] = fun g ->
  function
  | {p| z |p} -> {t| nat |t}
  | {p| s 'n |p} -> assert (tp_check g n = {t| nat |t}) ; {t| nat |t}
  | {p| cas 'm 'nz (\p. 'ns) |p} ->
     let {p| nat |p} = tp_check g m in
     let tz = tp_check g nz in
     let ts = tp_check (Cons ({t| nat |t}, g)) ns in
     assert (tz = ts) ; ts
  | {p| app 'm 'n |p} ->
     let {p| arr 't1 't2 |p} = tp_check g m in
     let tn = tp_check g n in
     assert (t1 = tn) ; t2
  | {p| lam 't (\x. 'm) |p} -> tp_check (Cons (t, g)) m

  | {p| fix 't (\f. 'm) |p} -> tp_check (Cons (t, g)) m
