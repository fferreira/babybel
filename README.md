# Babybel

This is an experimental implementation of a syntax extension to Ocaml that adds support for contextual objects.

## Examples

* nat.ml -- Converts SF natural numbers to int values
* compare.ml -- compares two lambda terms up to alpha renaming
* eval.ml -- a small evaluator for an untyped miniML

## Running

After building with ```make```:

1. ```rlwrap ocaml -ppx ./babybel.native -I ./_build/```
2. ```#load "sf.cmo";;```
3. ```#use "example/nat.ml";;```
