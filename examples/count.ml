open Sf

[@@@signature {def|
tm : type.
c : tm.
app : tm -> tm -> tm.
lam : (tm -> tm) -> tm.
|def}]

(* open terms *)

(* More careful generation of type annotations is needed as this does
   not work for applications
 *)

let rec count [@type "g. {|g, x : tm |- tm|} -> int"] =
  function
  | {p| g, x : tm |- c |p} -> 0
  | {p| g, x : tm |- app 'm 'n |p} -> count m + count n
  | {p| g, x : tm |- lam (\y. 'm) |p} -> count {t| g,x:tm, y:tm |- 'm [^2; y ; x] |t}
  | {p| g, x : tm |- x |p} -> 1
  | _ -> 0 (* this cases matches variables that are not the top one *)

let t0 = {t| x : tm |- x |t}
let t1 = {t| x : tm |- c |t}
let t2 = {t| x : tm |- lam (\y. app x y) |t}
let t3 = {t| x : tm |- lam (\x. app x x) |t}
let t4 [@type "{|x : tm |- tm|}"] = {t| x : tm |- lam (\y. app (lam (\z. app(app (app x z) y) x)) x) |t}
let t5 = {t| x: tm |- app x x |t}
let t6 = {t| ., x:tm, y:ym |- x |t}

let c0 = assert (count t0 = 1) (* 1 *)
let c1 = assert (count t1 = 0) (* 0 *)
let c2 = assert (count t2 = 1) (* 1 *)
let c3 = assert (count t3 = 0) (* 0 *)
let c4 = assert (count t4 = 3) (* 3 *)
let c5 = assert (count t5 = 2) (* 2 *)
let c6 = assert (count t6 = 0) (* 0 *)
