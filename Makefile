default: native

native:
	ocamlbuild -use-ocamlfind -yaccflags --explain babybel.native

byte:
	ocamlbuild -use-ocamlfind -yaccflags --explain babybel.byte

clean:
	ocamlbuild -clean

# doc:
# 	ocamlbuild -use-menhir -docflag -keep-code -lib unix tt.docdir/index.html
