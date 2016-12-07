# Babybel

This is an experimental implementation of a syntax extension to Ocaml that adds support for contextual objects. Because it uses OCaml's own internal AST reprseentation it is somewhat fuzzy about the compiler version. Babybel works at least with OCaml 4.03.0 and 4.04.0.

## Examples

* nat.ml -- Converts SF natural numbers to int values
* compare.ml -- compares two lambda terms up to alpha renaming
* eval.ml -- a small evaluator for an untyped miniML
* cps.ml -- a translation to a CPS calculus
* and more, check the examples directory!

## Running

After building with ```make```:

1. ```./run```
2. ```#use "examples/nat.ml";;```


### Note:

You need to have rlwrap installed to use ```./run```. If you don't have it or want to use it inside of an emacs shell, use instead ```./rune```.
