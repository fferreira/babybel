open Sf

exception Debug

[@@@signature {def|

tm : type.
z : tm.
s : tm -> tm.
cas : tm -> tm -> (tm -> tm) -> tm.
app : tm -> tm -> tm.
lam : (tm -> tm) -> tm.
fix : (tm -> tm) -> tm.

|def}]

let size [@type "{|tm|} -> int"] = function
  | {p| z |p} -> 0
  | {p| lam (\x. 'm) |p} -> 1
  | _ -> raise Debug

let dis [@type "{|tm|} -> bool"] = function
  | {p| lam (\x. lam (\y. app x y)) |p} -> true
  | {p| lam (\x. lam (\y. app y x)) |p} -> false
  | e -> raise Debug

let t1 = dis {t| lam (\z. lam (\w. app z w)) |t}
let t2 = dis {t| lam (\w. lam (\z. app z w)) |t}
