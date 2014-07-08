# ----------------------------------------------------------------------
# How to build the package syntax_xtype:
# ----------------------------------------------------------------------
# 
# make:                Same as "make all"
# make all:            Normally "make byte", but can also be set to "make opt"
# make byte:           Makes the bytecode archive and the bytecode executables
# make opt:            Makes the native archive and the native executable
# make install:        Install all installable files as package
# make uninstall:      Uninstall the package
# make clean:          Delete all files that can be remade
#
# The usual order of invocation is:
# - make byte
# - (optionally) make opt
# - make install
# - make clean
#
# You may want to give the -s option if you do not want to see the details
# of the build process (e.g. make -s all).
#
# ----------------------------------------------------------------------
# Important for developers
# ----------------------------------------------------------------------
# 
# This Makefile writes a copy of itself with appended dependencies.
# The copy is usually stored in the file .make-wizard.Makefile.
# If you want to invoke "make" for targets where the dependencies are
# involved, you have to specify -f .make-wizard.Makefile on
# the command line, e.g.
#
# make -f .make-wizard.Makefile sample.cmo
#
# Otherwise, the dependencies are ignored, and you get errors that are
# hard to explain.
#
# If you want to modify this Makefile, it is a good idea to put the
# modifications into a second file, and to enable the local Makefile
# extension in the wizard. This effects that the modifications are appended
# to this Makefile, so you can add rules and override variables without
# coming into conflict with the wizard.

# ----------------------------------------------------------------------
# Definitions
# ----------------------------------------------------------------------

NAME = syntax_xtype
# The name of the package. 

MFNAME = Makefile
# The name of this Makefile. (You must change this definition if you rename
# the Makefile!)

MF2NAME = .make-wizard.$(MFNAME)
# The name of the generated Makefile (a copy of this Makefile plus the
# dependencies)

TEMPNAME = .make-wizard.temps
# The name of a file containing the names of temporary files

VERSION = 0.1
# The version of this package

DESCRIPTION = Extensible datatypes
# The description of this package

GENERATOR_EXTS = .mll .mly
# These suffixes indicate that a generator must be called for them

MAKE_META = #_meta
# Make the META file by this rule. (An empty definition turns META generation
# off.)

INSTALL = _findlib_install
# Which rule to use for installation

UNINSTALL = _findlib_uninstall
# Which rule to use for deinstallation

MAKEMAKE_HOOK =
# Set this to the name of a rule to add your own definitions to $(MF2NAME)



BYTE_ARCHIVE = $(NAME).cma
# The name of the resulting bytecode archive.

BYTE_OBJECTS = syntax_xtype.cmo
# The cmo objects that are linked together, and are put into the byte archive.

BYTE_FILES = $(BYTE_OBJECTS) $(BYTE_OBJECTS:.cmo=.cmi) $(BYTE_ARCHIVE)
# The files that are generated in order to make the byte archive. Note
# that .ml and .mli files are missing that are generated from 
# .mly and .mll files. 

BYTE_INST = $(BYTE_OBJECTS:cmo=cmi) $(BYTE_OBJECTS:.cmo=.mli) $(BYTE_ARCHIVE)
# The files that will be installed after the byte archive is made. Not
# every file exists.



BYTE_EXEC_TARGETS = 
# The list of bytecode executables.

BYTE_EXEC_OBJECTS = 
# The list of cmo modules that are linked into bytecode executables

BYTE_EXEC_FILES = $(BYTE_EXEC_OBJECTS) $(BYTE_EXEC_OBJECTS:.cmo=.cmi) \
    $(BYTE_EXEC_TARGETS)
# The list of files that are generated in order to make the bytecode
# executables. Note that .ml and .mli files are missing that are generated 
# from .mly and .mll files. 

BYTE_EXEC_INST = $(BYTE_EXEC_TARGETS)
# The files to install as bytecode executables.


NAT_EXEC_TARGETS = 
# The list of native executables.

NAT_EXEC_OBJECTS = 
# The list of cmx modules that are linked into native executables

NAT_EXEC_FILES = $(NAT_EXEC_OBJECTS) $(NAT_EXEC_OBJECTS:.cmx=.cmi) \
    $(NAT_EXEC_OBJECTS:.cmx=.o) $(NAT_EXEC_TARGETS)
# The list of files that are generated in order to make the native
# executables. Note that .ml and .mli files are missing that are generated 
# from .mly and .mll files. 

NAT_EXEC_INST = $(NAT_EXEC_TARGETS)
# The files to install as native executables.


PREREQUISITES = camlp4 camlp4.extend camlp4.macro camlp4.quotations camlp4.quotations.o camlp4.fulllib
# The required packages.

PPOPTS = -syntax camlp4o
# Preprocessor options.

MTOPTS = 
# Multi-threading options

INCOPTS = 
# -I options (currently unused, but this may change in the future)

OTHER_INST = META
# Files to install that are not mentioned in the other XXX_INST variables

#TASKBYTELINKOPTS = -custom
# Uncomment this line to create stand-alone executables

# Tools and tasks: "Tools" are the commands to call, and "tasks" are the tools
# to use for certain situations.

OCAMLFIND = ocamlfind
OCAMLLEX  = ocamllex
OCAMLYACC = ocamlyacc
OCAMLDEP  = $(OCAMLFIND) ocamldep
OCAMLC    = $(OCAMLFIND) ocamlc
OCAMLCP   = $(OCAMLFIND) ocamlcp
OCAMLOPT  = $(OCAMLFIND) ocamlopt
#
# These are the tools.

TASKLEX      = $(OCAMLLEX) $(TASKLEXOPTS)
TASKYACC     = $(OCAMLYACC) $(TASKYACCOPTS)
TASKDEP      = $(OCAMLDEP) $(INCOPTS) $(PPOPTS) -package "$(PREREQUISITES)" $(TASKDEPOPTS)
TASKCI       = $(OCAMLC) $(INCOPTS) $(PPOPTS) -package "$(PREREQUISITES)" -c $(TASKCIOPTS)
TASKBYTECO   = $(OCAMLC) $(INCOPTS) $(PPOPTS) $(MTOPTS) -package "$(PREREQUISITES)" -c -g $(TASKBYTECOOPTS)
TASKBYTELINK = $(OCAMLC) $(INCOPTS) $(PPOPTS) $(MTOPTS) -package "$(PREREQUISITES)" -linkpkg $(TASKBYTELINKOPTS)
TASKBYTEAR   = $(OCAMLC) -a $(TASKBYTEAROPTS)
TASKNATCO    = $(OCAMLOPT) $(INCOPTS) $(PPOPTS) $(MTOPTS) -package "$(PREREQUISITES)" -c $(TASKNATCOOPTS)
TASKNATLINK  = $(OCAMLOPT) $(INCOPTS) $(PPOPTS) $(MTOPTS) -package "$(PREREQUISITES)" -linkpkg $(TASKNATLINKOPTS)
TASKNATAR    = $(OCAMLOPT) -a $(TASKNATAROPTS)
TASKINSTALL  = $(OCAMLFIND) install $(NAME) $(TASKINSTALLOPTS)
TASKREMOVE   = $(OCAMLFIND) remove $(NAME) $(TASKREMOVEOPTS)
#
# These are the tasks. The names mean the following:
#                   TASKLEX: Used to create a lexer
#                  TASKYACC: Used to create a parser
#                   TASKDEP: Used to analyze the dependencies
#                    TASKCI: Used to compile interface files
#     TASKBYTECO, TASKNATCO: Used to compile implementation files
# TASKBYTELINK, TASKNATLINK: Used to create executables
#     TASKBYTEAR, TASKNATAR: Used to create archives
#               TASKINSTALL: Used to install the package
#                TASKREMOVE: Used to remove the package
#                   INCOPTS: -I options
#                    PPOPTS: Options to specify the preprocessor
#                    MTOPTS: -thread (if necessary)
#                   NATONLY: -native (if necessary)
# For every task <T>, there is a variable for task-specific options <T>OPTS.


# ----------------------------------------------------------------------
# Rules
# ----------------------------------------------------------------------


.PHONY: all
all: byte


# The suffix rules: They specify how to make a file ending in suffix X from
# a source file ending in suffix Y. For every suffix rule, there is a task
# defining what to do.

.SUFFIXES: .ml .mli .cmo .cmx .cmi .mll .mly

.mli.cmi:
	@echo "<Making $@>"
	$(TASKCI) $<

.ml.cmo:
	@echo "<Making $@>"
	$(TASKBYTECO) $<

.ml.cmx:
	@echo "<Making $@>"
	$(TASKNATCO) $<

# The generator rules record the generated files: The "grep" checks whether
# the filename already occurs in $(TEMPNAME), and the "echo" appends the
# filename when missing.

.mll.ml:
	@echo "<Making $@>"
	$(TASKLEX) $<
	touch $(TEMPNAME)
	grep -F -x -q -e "$@" $(TEMPNAME) || echo "$@" >>$(TEMPNAME)

.mly.ml:
	@echo "<Making $@>"
	$(TASKYACC) $<
	touch $(TEMPNAME)
	grep -F -x -q -e "$@" $(TEMPNAME) || echo "$@" >>$(TEMPNAME)

# The _dummy rule does nothing:

_dummy:
	:

# The following rule checks which lex and yacc targets exist, and calls
# MAKE recursively.

.PHONY: _meta
_meta:
	@echo "<Updating META>"
	echo "name = \"$(NAME)\"" >META
	echo "version = \"$(VERSION)\"" >>META
	echo "description = \"$(DESCRIPTION)\"" >>META
	echo "requires = \"$(PREREQUISITES)\"" >>META
	test -z "$(BYTE_ARCHIVE)" || \
	    echo "archive(byte) = \"$(BYTE_ARCHIVE)\"" >>META
	test -z "$(NAT_ARCHIVE)" || \
	    echo "archive(native) = \"$(NAT_ARCHIVE)\"" >>META

.PHONY: _generator
_generator: $(MAKE_META)
	@echo "<Checking for generator targets>"
	targets=$$( \
	    { \
		for obj in _dummy $(BYTE_OBJECTS) $(BYTE_EXEC_OBJECTS); do \
		    test "_dummy" != "$$obj" || continue; \
		    for ext in $(GENERATOR_EXTS); do \
		    	if [ -f "$${obj%.cmo}$$ext" ]; then \
				echo "$${obj%.cmo}.ml"; \
		    	fi; \
	            done; \
		done && \
		for obj in _dummy $(NAT_OBJECTS) $(NAT_EXEC_OBJECTS); do \
		    test "_dummy" != "$$obj" || continue; \
		    for ext in $(GENERATOR_EXTS); do \
		    	if [ -f "$${obj%.cmx}$$ext" ]; then \
				echo "$${obj%.cmx}.ml"; \
		    	fi; \
	            done; \
		done; \
	    } | sort | uniq \
        ) && \
        { test -z "$$targets" || $(MAKE) -f $(MFNAME) $$targets; }

# The following rule calls ocamldep for the right files, and creates 
# a file that consists of the contents of this Makefile, and of the output
# of ocamldep.

.PHONY: _makemake
_makemake: _generator
	@echo "<Analyzing dependencies and creating $(MF2NAME)>"
	cat $(MFNAME) >$(MF2NAME)
	test -z "$(MAKEMAKE_HOOK)" || $(MAKE) -f $(MFNAME) $(MAKEMAKE_HOOK)
	echo "# ---------------------------------------- dependencies:" >>$(MF2NAME)
	targets=$$( \
	    { \
		nat=-native-filter && \
		byte=-bytecode-filter && \
		for obj in _dummy $(BYTE_OBJECTS); do \
		    test "_dummy" != "$$obj" || continue; \
		    echo "$${obj%.cmo}.ml"; \
		    echo "$${obj%.cmo}.mli"; \
		    nat=""; \
		done && \
		for obj in _dummy $(NAT_OBJECTS); do \
		    test "_dummy" != "$$obj" || continue; \
		    echo "$${obj%.cmx}.ml"; \
		    echo "$${obj%.cmx}.mli"; \
		    byte=""; \
		done; \
		echo "$$byte $$nat"; \
	    } | sort | uniq \
        ) && \
	$(TASKDEP) $$targets >>$(MF2NAME)


.PHONY: byte
byte: _byte

.PHONY: _byte
_byte: _makemake
	@echo "<Starting with bytecode targets>"
	if [ -n "$(BYTE_ARCHIVE)" ]; then \
	    $(MAKE) -f $(MF2NAME) $(BYTE_ARCHIVE); \
	fi
	if [ -n "$(BYTE_EXEC_TARGETS)" ]; then \
	    $(MAKE) -f $(MF2NAME) $(BYTE_EXEC_TARGETS); \
	fi
	@echo "<Done bytecode targets>"


.PHONY: opt
opt: _opt

.PHONY: _opt
_opt: _makemake
	@echo "<Starting with native targets>"
	if [ -n "$(NAT_ARCHIVE)" ]; then \
	    $(MAKE) -f $(MF2NAME) $(NAT_ARCHIVE); \
	fi
	if [ -n "$(NAT_EXEC_TARGETS)" ]; then \
	    $(MAKE) -f $(MF2NAME) $(NAT_EXEC_TARGETS); \
	fi
	@echo "<Done native targets>"


$(BYTE_ARCHIVE): $(BYTE_OBJECTS)
	@echo "<Making $(BYTE_ARCHIVE)>"
	$(TASKBYTEAR) -o $(BYTE_ARCHIVE) $(BYTE_OBJECTS)


.PHONY: clean
clean:
	@echo "<Cleaning up>"
	touch $(TEMPNAME)
	rm -f $(BYTE_FILES) $(NAT_FILES) $(BYTE_EXEC_FILES) $(NAT_EXEC_FILES)
	rm -f $(MF2NAME)
	cat $(TEMPNAME) | xargs rm -f
	rm -f $(TEMPNAME)

.PHONY: CLEAN
CLEAN: clean

.PHONY: distclean
distclean: clean


.PHONY: install
install: $(INSTALL)

.PHONY: _findlib_install
_findlib_install:
	@echo "<Installing>"
	files=$$( \
	    for f in $(BYTE_INST) $(NAT_INST) $(BYTE_EXEC_INST) $(NAT_EXEC_INST) $(OTHER_INST); do \
	        if [ -f "$$f" ]; then echo $$f; fi; \
	    done; \
        ) && \
	$(TASKINSTALL) $$files

.PHONY: uninstall
uninstall: $(UNINSTALL)

.PHONY: _findlib_uninstall
_findlib_uninstall:
	@echo "<Uninstalling>"
	$(TASKREMOVE)

# The following rules just print some variables.

.PHONY: _print_name
_print_name:
	echo "$(NAME)"

.PHONY: _print_version
_print_version:
	echo "$(VERSION)"

