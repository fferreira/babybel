open Sf

[@@@signature {def|
tm : type.
z : tm.
s : tm -> tm.
cas : tm -> tm -> (tm -> tm) -> tm.
app : tm -> tm -> tm.
lam : (tm -> tm) -> tm.
fix : (tm -> tm) -> tm.
|def}]

(* open terms *)

let t0 = {t| x : tm |- x |t}
let t1  = {t| |- s z |t}
let t2  = {t| z |t}
let t3 = {t| ., x : tm, y : tm |- x |t}

let is_top [@type "d. {| d , x : tm |- tm |} -> bool"] = function
  | {p| g, x : tm |- x |p} -> true
  |  _ -> false

let tt0 = is_top t0
let tt1 = is_top t1
let tt3 = is_top t3

(* multiple term substitution *)

let e = {t| lam (\x. lam (\y. app x y )) |t}

let multiple [@type "{|tm|} -> {|tm|}"]  = function
  | {p| lam (\x. lam (\y. 'm)) |p} -> {t| 'm [(s z) ;  z] |t}
  | e -> e

let e = {t| lam (\x. lam (\y. app x y))  |t}
let e' = multiple e
