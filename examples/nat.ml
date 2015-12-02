open Sf

exception Debug of Sf.nor

let x = {def| nat : type.  z : nat. s : nat -> nat. |def}

let t0 = {t| s s z |t}

let t1 = {t| z |t}

let rec to_nat e = match e with
  | {p| z |p} -> 0
  | {p| s 'n |p} -> 1 + to_nat {t| 'n |t}
  | _ -> raise (Debug e) 	(* Prints the term that was not matched by the previous two *)

let n = to_nat {t| s (s (s (s (s (s (s z)))))) |t}
