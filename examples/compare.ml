open Sf

exception Debug of Sf.nor

let _ = {def|

tm : type.
z : tm.
s : tm -> tm.
cas : tm -> tm -> (tm -> tm) -> tm.
app : tm -> tm -> tm.
lam : (tm -> tm) -> tm.
fix : (tm -> tm) -> tm.

|def}

let f e = match e with
  | {p| z |p} -> 0
  | {p| lam (\x. 'm) |p} -> 1
  | _ -> raise (Debug e)

let dis = function
  | {p| lam (\x. lam (\y. x y)) |p} -> true
  | {p| lam (\x. lam (\y. y x)) |p} -> false
  | e -> raise (Debug e)

let t1 = dis {term| lam (\z. lam (\w. z w))  |term}
let t2 = dis {term| lam (\w. lam (\z. z w))  |term}
