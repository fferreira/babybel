open Sf

exception Debug of Sf.nor

let x = {def| nat : type.  z : nat. s : nat -> nat. |def}

let t0 = {term| s s z |term}

let t1 = {term| z |term}


let rec to_nat e = match e with
  (* | {p| 'm |p} -> -1 *)
  | {p| z |p} -> 0
  | {p| s 'n |p} -> 1 + to_nat {term| 'n |term}
  | _ -> raise (Debug e) 	(* Prints the term that was not matched by the previous two *)

let n = to_nat {term| s (s (s (s (s (s (s z)))))) |term}
