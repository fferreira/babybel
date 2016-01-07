open Sf

exception Debug of Sf.nor

let signature = {def| nat : type.  z : nat. s : nat -> nat. |def}

let t0 [@type "{|nat|}"] = {t| s s z |t}

let t1 = {t| z |t}

let rec to_nat [@ type "{|nat|} -> int"] = function
  | {p| z |p} -> 0
  | {p| s 'n |p} -> 1 + to_nat {t| 'n |t}
  | e -> raise (Debug e) 	(* Prints the term that was not matched by the previous two *)

let n = to_nat {t| s (s (s (s (s (s (s z)))))) |t}
