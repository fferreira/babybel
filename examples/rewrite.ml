open Sf

[@@@signature {def|
tm : type.
i : tm.
pair : tm -> tm -> tm.
fst : tm -> tm.
snd : tm -> tm.
letpair : tm -> (tm -> tm -> tm) -> tm.
app : tm -> tm -> tm.
lam : (tm -> tm) -> tm.

|def}]

let rec rewrite [@type "g. [g |- tm] -> [g |- tm]"] = function
| {p| i |p} -> {t| i |t}
| {p| pair 'm 'n |p} ->
   let mm = rewrite m in
   let nn = rewrite n in
   {t| pair 'mm 'nn |t}
| {p| fst 'm |p} ->
   let mm = rewrite m in
   {t| fst 'mm |t}
| {p| snd 'm |p} ->
   let mm = rewrite m in
   {t| snd 'mm |t}
| {p| app 'm 'n |p} ->
   let mm = rewrite m in
   let nn = rewrite n in
   {t| app 'mm 'nn |t}
| {p| lam (\x. 'm) |p} ->
   let mm = rewrite m in
   {t| lam (\x. 'mm) |t}
| {p| #x |p} -> {t| #x |t}
| {p| letpair 'm (\x.\y. 'n) |p} ->
   let mm = rewrite m in
   rewrite {t| 'n [fst 'mm ; snd 'mm] |t}

let t0 = rewrite {t| lam (\x. x) |t}
let t1 = rewrite {t| lam (\x. letpair x (\y.\z. app y z)) |t}
