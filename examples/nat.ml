open Sf

[@@@signature "nat : type.  z : nat. s : nat -> nat. not : type."]

exception Debug

let t1 = {t| z |t}
let t2 [@type "{|nat|}"] = {t| z |t}

let t3 = {t| s (s z) |t}
let t4 [@type "{|nat|}"] = {t| s (s z) |t}

let rec to_nat [@type "{| . |- nat|} -> int"] = function
  | {p| z |p} -> 0
  | {p| s 'n |p} -> 1 + to_nat {t| 'n |t}
  | e -> raise Debug

let n = to_nat {t| s (s (s (s (s (s (s z)))))) |t}
