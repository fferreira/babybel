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

let count [@type "g. {|g, x : tm |- tm|} -> int"] = function
  (* | {p| g, x : tm |- app 'm 'n |p} -> count m + count n *)
  | {p| g, x : tm |- x |p} -> 1
  | _ -> 0

let t0 = {t| x : tm |- x |t}
let t1  = {t| x : tm |- c |t}
let t2 = {t| x : tm |- lam (\y. app x y) |t}
let t3 = {t| x : tm |- lam (\x. app x x) |t}
(* let t4 [@type "{|tm|}"]  = {t| x : tm |- lam (\y. app (lam (\z . app(app (app x z) y) x))) |t} *)

let c0 = count t0
let c1 = count t1
let c2 = count t2
let c3 = count t3
(* let c4 = count t4 *)
