open Sf

[@@@signature {def|
foo : type.
z : foo.

bar : type.
w : bar.

|def}]


let t0 [@type "[x : bar |-  foo]"] = {t| z |t}

(* let t0' [@type "[x : bar |-  foo]"] = {t| x |- x |t} *) (* this can't work x is a bar not a foo *)

let t1 [@type "[x : bar |- bar]"] = {t| x |- x |t}
