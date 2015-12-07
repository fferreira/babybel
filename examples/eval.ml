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

let rec eval e = match e with
  | {p| z |p} -> {t| z |t}
  | {p| s 'n |p} -> let nv = eval n in {t| s 'nv |t}
  | {p| lam (\x. 'm) |p} -> e
  | {p| cas 'm 'n (\p. 'o) |p} ->
     begin match eval m with
	   | {p| z |p} -> eval n
 	   | {p| s 'm |p} -> eval {t| 'o ['m] |t}
	   | _ -> raise (Debug e)
     end
  | {p| app 'm 'n |p} ->
     let {p| lam (\x. 'q) |p} = eval m
     in eval {t| 'q ['n] |t}
  | {p| fix (\f. 'f) |p} -> {t| 'f [fix (\f. 'f)] |t}
  | _ -> raise (Debug e)

let test =  eval {t| app (app (lam (\x. x)) (lam (\y. y))) z |t}
