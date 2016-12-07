open Sf

[@@@signature {def|
tm : type.
c : tm.
app : tm -> tm -> tm.
lam : (tm -> tm) -> tm.
|def}]

exception Not_found

type step
  = Here
  | AppL
  | AppR
  | InLam

type path = step list

let rec helper [@type "g. [g, x : tm |- tm] -> path"] =
function
| {p| _, x |- c |p} -> raise Not_found
| {p| _, x |- lam (\y. 'm) |p} -> InLam::(helper {t| _, x, y |- 'm [_ ; y ; x] |t})
| {p| _, x |- x |p} -> [Here]
| {p| #x |p} -> raise Not_found
| {p| _, x |- app 'm 'n |p} ->
   try AppL::(helper m)
   with _ -> AppR::(helper n)

let get_path [@type "g. [g, x : tm |- tm] -> path"] = fun t ->
  try helper t
  with _ -> []

let t0 = {t| x |- x |t}
let t1 = {t| x |- c |t}
let t2 = {t| x |- lam (\y. app x y) |t}
let t3 = {t| x |- lam (\x. app x x) |t}
let t4 [@type "[x |- tm]"] = {t| x |- lam (\y. app (lam (\z. app(app (app z x) y) z)) x) |t}
let t5 = {t| x |- app x x |t}
let t6 = {t| _, x, y |- x |t}

let c0 = assert (get_path t0 = [Here])
let c1 = assert (get_path t1 = [])
let c2 = assert (get_path t2 = [InLam ; AppL ; Here])
let c3 = assert (get_path t3 = [])
let c4 = assert (get_path t4 = [InLam ; AppL ; InLam ; AppL ; AppL ; AppR ; Here])
let c5 = assert (get_path t5 = [AppL ; Here])
let c6 = assert (get_path t6 = [])
