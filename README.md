# Babybel

This is an experimental implementation of a syntax extension to Ocaml that adds support for contextual objects. Because it uses OCaml's own internal AST reprseentation it is somewhat fuzzy about the compiler version. Babybel works at least with OCaml 4.03.0

## Examples

* nat.ml -- Converts SF natural numbers to int values
* compare.ml -- compares two lambda terms up to alpha renaming
* eval.ml -- a small evaluator for an untyped miniML

## Running

After building with ```make```:

1. ```./run```
2. ```#use "example/nat.ml";;```
