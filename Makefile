OCAMLBUILD=ocamlbuild -use-ocamlfind -byte-plugin -plugin-tag "package(js_of_ocaml.ocamlbuild)"
MAKAMFILES=$(foreach file, $(shell find . -name \*.makam), -file $(file):/)
.PHONY: all clean js

all:
	$(OCAMLBUILD) toploop/nativerepl.native

js:
	$(OCAMLBUILD) -no-links js/browser.byte
	js_of_ocaml -I ./ $(MAKAMFILES) -noruntime +js_of_ocaml/runtime.js +weak.js +toplevel.js js/myruntime.js _build/js/browser.byte -o js/makam.js

clean:
	ocamlbuild -clean
	rm -f nativerepl.native js/makam.js




