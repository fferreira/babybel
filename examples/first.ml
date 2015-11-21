let sigma = {def|

tp: type.
nat : tp.
arr : tp -> tp -> tp.

tm : type.
z : tm.
s : tm -> tm.
cas : tm -> tm -> (tm -> tm) -> tm.
app : tm -> tm -> tm.
lam : (tm -> tm) -> tm.
fix : (tm -> tm) -> tm.

(* schema ctx = tm; *)

|def}


(* a function on these *)

(* let rec eval e = *)
(*   match e with *)
(*   | {| g |- z |} -> {| g |- z |} *)
(*   | {| g|- app (lam (\x. 'm)) 'n |} -> eval {|g |- m' 'n|} *)

(* let res = eval {| app (lam (\x. x)) z |} *)
