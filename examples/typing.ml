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
lam : {tp} -> (tm -> tm) -> tm.
fix : {tp} -> (tm -> tm) -> tm.
|def}]

type _ ctx
  = Empty : nil ctx
  | Cons : (nil, tp_tp base) tm  * 'g ctx -> (('g, tp_tm base) cons) ctx

let rec lookup [@type "g. g ctx -> [g |- tm] -> [tp]"] = fun g ->
  function
  | {p| *,x |-  x |p} -> let Cons (t,_) = g in t
  | {p| ##x |p} ->
     let Cons (_, g1) = g in
     lookup g1 {t| #x |t}


let rec tp_check [@type "g. g ctx -> [g |- tm] -> [tp]"] = fun g ->
  function
  | {p| z |p} -> {t| nat |t}
  | {p| s 'n |p} -> assert (tp_check g n = {t| nat |t}) ; {t| nat |t}
  | {p| cas 'm 'nz (\p. 'ns) |p} ->
     let {p| nat |p} = tp_check g m in
     let tz = tp_check g nz in
     let ts = tp_check (Cons ({t| nat |t}, g)) ns in
     let ts1 = {t| 'ts |t} in
     assert (tz = ts1) ; ts1
  | {p| app 'm 'n |p} ->
     let {p| arr 't1 't2 |p} = tp_check g m in
     let tn = tp_check g n in
     assert (t1 = tn) ; t2
  | {p| lam {'t} (\x. 'm) |p} ->
     let t1 = tp_check (Cons (t, g)) m in
     {t| arr 't ('t1) |t}

  | {p| fix {'t} (\f. 'm) |p} ->
     tp_check (Cons (t, g)) m

  | {p| #x |p} -> lookup g {t| #x |t}
