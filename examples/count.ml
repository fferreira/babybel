open Sf

[@@@signature {def|
tm : type.
c : tm.
app : tm -> tm -> tm.
lam : (tm -> tm) -> tm.
|def}]

(* open terms *)

let rec count [@type "g. [g, x : tm |- tm] -> int"] =
  function
  | {p| _, x |- c |p} -> 0
  | {p| _, x |- app 'm 'n |p} -> count m + count n
  | {p| _, x |- lam (\y. 'm) |p} -> count {t| _, x, y |- 'm [_ ; y ; x] |t}
  | {p| _, x |- x |p} -> 1
  | {p| #x |p} -> 0

let t0 = {t| x |- x |t}
let t1 = {t| x |- c |t}
let t2 = {t| x |- lam (\y. app x y) |t}
let t3 = {t| x |- lam (\x. app x x) |t}
let t4 [@type "[x |- tm]"] = {t| x |- lam (\y. app (lam (\z. app(app (app x z) y) x)) x) |t}
let t5 = {t| x |- app x x |t}
let t6 = {t| _, x, y |- x |t}

let c0 = assert (count t0 = 1) (* 1 *)
let c1 = assert (count t1 = 0) (* 0 *)
let c2 = assert (count t2 = 1) (* 1 *)
let c3 = assert (count t3 = 0) (* 0 *)
let c4 = assert (count t4 = 3) (* 3 *)
let c5 = assert (count t5 = 2) (* 2 *)
let c6 = assert (count t6 = 0) (* 0 *)
