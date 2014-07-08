all:
	ocamlbuild -use-ocamlfind -byte-plugin toploop/nativerepl.native

clean:
	ocamlbuild -clean
	rm -f nativerepl.native

