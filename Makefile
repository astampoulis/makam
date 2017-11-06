# OASIS_START
# DO NOT EDIT (digest: a3c674b4239234cbbe53afe090018954)

SETUP = ocaml setup.ml

build: setup.data
	$(SETUP) -build $(BUILDFLAGS)

doc: setup.data build
	$(SETUP) -doc $(DOCFLAGS)

test: setup.data build
	$(SETUP) -test $(TESTFLAGS)

all:
	$(SETUP) -all $(ALLFLAGS)

install: setup.data
	$(SETUP) -install $(INSTALLFLAGS)

uninstall: setup.data
	$(SETUP) -uninstall $(UNINSTALLFLAGS)

reinstall: setup.data
	$(SETUP) -reinstall $(REINSTALLFLAGS)

clean:
	$(SETUP) -clean $(CLEANFLAGS)

distclean:
	$(SETUP) -distclean $(DISTCLEANFLAGS)

setup.data:
	$(SETUP) -configure $(CONFIGUREFLAGS)

configure:
	$(SETUP) -configure $(CONFIGUREFLAGS)

.PHONY: build doc test all install uninstall reinstall clean distclean configure

# OASIS_STOP

OCAMLBUILD=ocamlbuild -use-ocamlfind -byte-plugin
MAKAMFILES=$(foreach file, $(shell find . -name \*.makam), --file $(file):/$(file))
MAKAM_MARKDOWN_FILES=$(foreach file, $(shell find examples -name \*.md), --file $(file):/$(file))

.PHONY: js md2makam md2makam-watch

js:
	$(OCAMLBUILD) -plugin-tag "package(js_of_ocaml.ocamlbuild)" -no-links js/browser.byte
	js_of_ocaml -I ./ $(MAKAMFILES) $(MAKAM_MARKDOWN_FILES) --noruntime +js_of_ocaml/runtime.js +weak.js +toplevel.js js/myruntime.js _build/js/browser.byte -o js/makam.js

md2makam:
	find -name \*.md -exec grep -l "^\`\`\`makam" {} \; | xargs -n 1 -r awk -f scripts/generate-makam.awk

md2makam-watch:
	while true; do inotifywait -e modify `git ls-files --cached --others */*.md` && find -name \*.md -exec grep -l "^\`\`\`makam" {} \; | xargs -n 1 -r awk -f scripts/generate-makam.awk; done
