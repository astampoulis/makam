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

TESTS= \
tests/core_tests \
stdlib/tests \
stdlib/concrete_bind.tests \
stdlib/parsing/tests \
stdlib/parsing/tests_opt \
stdlib/parsing/peg_grammar \
stdlib/parsing/layout_grammar.tests \
stdlib/pretty/tests \
stdlib/syntax/tests \
stdlib/syntax/makam_syntax.tests \
stdlib/syntax/syntax_syntax.tests \
stdlib/syntax/layout_syntax.tests \
stdlib/syntax/constructor_syntax.tests \
stdlib/dyn_expansion \
new/testocaml \
new/testcases_ocaml \
small/systemf \
big/testocaml \
big/testveriml \
big/testurweb \
big/testf2tal

MAKAM ?= ./makam

cache-clean:
	rm -rf .makam-cache

makam-tests:
	bash -c "set -e; for i in $(TESTS); do ($(MAKAM) --run-tests \$$i || (echo -e \"\nTest failure for: \$$i\n\n\"; exit 1)); done"

makam-timing-tests:
	./scripts/timing-test.sh

makam-js-tests:
	echo '%use "all_tests_js". (verbose_run_tests -> run_tests X) ?' | node --stack-size=65536 js/ | tee output
	bash -c "grep SUCCESSFUL output; RES=\$$?; rm output; exit \$$RES"

# version stuff
check-version:
	./scripts/makam-version.sh check-if-updated

# publishing to npm
prepare-npm-package: check-version build
	./scripts/prepare-npm-package.sh

prepare-test-npm-package: check-version build
	bash -c "set -e; \
	         export MACOS_BINARY_OPTIONAL=true; \
	         export TEST_VERSION=\$$(./scripts/makam-version.sh npm-test-version); \
	         ./scripts/prepare-npm-package.sh \$$TEST_VERSION"

npm-test-publish: prepare-test-npm-package
	bash -c "./scripts/publish-npm-package.sh makam-\$$(./scripts/makam-version.sh npm-test-version).tgz"

npm-prod-publish: prepare-npm-package
	bash -c "./scripts/publish-npm-package.sh makam-\$$(./scripts/makam-version.sh).tgz"

webservice-test-deploy:
	bash -c "./scripts/webservice-deploy.sh"

webservice-prod-deploy:
	bash -c "./scripts/webservice-deploy.sh prod"

# js_of_ocaml compilation

OCAMLBUILD=ocamlbuild -use-ocamlfind -byte-plugin
MAKAMFILES=$(foreach file, $(shell find . -name \*.makam), --file $(file):/$(file))
MAKAM_MARKDOWN_FILES=$(foreach file, $(shell find examples -name \*.md), --file $(file):/$(file))

js:
	$(OCAMLBUILD) -plugin-tag "package(js_of_ocaml.ocamlbuild)" -no-links js/browser.byte
	js_of_ocaml -I ./ $(MAKAMFILES) $(MAKAM_MARKDOWN_FILES) --noruntime +js_of_ocaml/runtime.js +weak.js +toplevel.js js/myruntime.js _build/js/browser.byte -o js/makam.js

md2makam:
	find -name \*.md -exec grep -l "^\`\`\`makam" {} \; | xargs -n 1 -r awk -f scripts/generate-makam.awk

md2makam-watch:
	while true; do inotifywait -e modify `git ls-files --cached --others */*.md` && find -name \*.md -exec grep -l "^\`\`\`makam" {} \; | xargs -n 1 -r awk -f scripts/generate-makam.awk; done

.PHONY: js md2makam md2makam-watch makam-tests makam-js-tests cache-clean npm-test-publish check-version

