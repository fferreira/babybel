open Sf

[@@@signature {def|
tm : type.
app : tm -> tm -> tm.
lam : (tm -> tm) -> tm.

nat: type.
z: nat.
s: nat -> nat.

envr: type.
ctm: type.

nil: envr.
snoc: envr -> ctm -> envr.

clam: {envr -> ctm} -> ctm.
capp: ctm -> ctm -> ctm.
proj: envr -> {nat} -> ctm.
close: ctm -> envr -> ctm.
open: ctm -> (envr -> ctm -> ctm) -> ctm.
create: envr -> ctm.
|def}]

type _ ctx
  = Empty : nil ctx
  | Cons : 'g ctx -> (('g, tp_tm base) cons) ctx

type _ cctx
  = Empty : nil cctx
  | Cons : 'g cctx -> (('g, tp_ctm base) cons) cctx

let rec add_projs [@type "h . h cctx -> [nat] -> [h, e:envr |- ctm] -> [e:envr |- ctm]"] = fun g n m ->
  match g with
  | Empty -> m
  | Cons g' ->
     let succ = {t| s 'n |t} in
     let m1 = {t| e |-  'm [^1 ; (proj e {'n}) ; e] |t} in
     add_projs g' succ m1

let rec ctx_to_env [@type "h. h cctx -> [h |- envr]"] =
  function
  | Empty -> {t| nil |t}
  | Cons g' ->
     let e = ctx_to_env g' in
     {t| _, x |- snoc ('e [^1 ;]) x |t}

type (_, _) rel
  = Void : (nil, nil) rel
  | Both : ('g, 'd) rel -> (('g, tp_tm base) cons, ('d, tp_ctm base) cons) rel

let rec conv [@type "g h . h cctx -> (g, h) rel -> [g |- tm] -> [h |- ctm]"] = fun h r ->
  function
  | {p| _,x |- x |p} ->
     let Both _ = r in
     {t| _, x |- x |t}

  | {p| ##x |p} ->
     let Both r' = r in
     let Cons h' = h in
     let m1 = conv h' r' {t| #x |t} in
     {t| 'm1 [^1 ;] |t}

  | {p| g |- lam (\x. 'm) |p} ->
     let m1 = conv (Cons h) (Both r) m in
     let n = add_projs (Cons h) {t| z |t} {t| _, x, e |- 'm1 [^2 ; x] |t} in
     let e = ctx_to_env h in
     {t| close (clam {\e. 'n[^1 ; e]}) 'e |t}

  | {p| app 'm 'n |p} ->
     let m1 = conv h r m in
     let n1 = conv h r n in
     {t| open 'm1 (\e. \f. capp f (create (snoc e ('n1[^2 ;])))) |t}
