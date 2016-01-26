(* copy open terms *)
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

let rec copy [@type "g . {|g |- tm|} -> {|g |- tm|}"] =
  function
  | {p| #x |p} -> {t| #x |t}
  | {p| z |p} -> {t| z|t}
  | {p| s 'n  |p} -> let nc = copy n in {t| s 'nc |t}
  | {p| cas 'm 'n (\x. 'o)  |p} ->
     let mc = copy m in
     let nc = copy n in
     let oc = copy o in
     {t| cas 'mc 'nc (\x. 'oc) |t}
  | {p| app 'm 'n |p} ->
     let mc = copy m in
     let nc = copy n in
     {t| app 'mc 'nc |t}
  | {p| lam (\x. 'm)  |p} ->
     let mc = copy m in
     {t| lam (\x. 'mc)  |t}
  | {p| fix (\f. 'm)  |p} ->
     let mc = copy m in
     {t| fix (\x. 'mc) |t}
