open Ocamlbuild_plugin;;
open Command;;

dispatch begin function

  | After_rules ->

    Ocamlbuild_js_of_ocaml.dispatcher After_rules ;

    let parsers = [ A"-I"; A"+camlp4/Camlp4Parsers"] in
    flag ["ocaml"; "compile"; "parsers"] (S parsers);

    rule "Bootstrap PEG parser generation (Stage 1)"
      ~prod:"bootPegParser.ml"
      ~deps:["bootstrap/dumpBootParser.byte"]
      begin fun env _build ->
	let ml = env "bootPegParser.ml" in
	let dump = env "bootstrap/dumpBootParser.byte" in
	let tags = tags_of_pathname ml in
	Cmd(S[A dump; T tags; Px ml])
      end;

    rule "Bootstrap PEG parser generation (Stage 2)"
      ~prod:"boot2PegParser.ml"
      ~deps:["grammars/pegGrammar.peg"; "bootstrap/bootPegParserGen.byte"]
      begin fun env _build ->
	let ml = env "boot2PegParser.ml" in
	let peg = env "grammars/pegGrammar.peg" in
	let dump = env "bootstrap/bootPegParserGen.byte" in
	let tags = tags_of_pathname ml in
	Cmd(S[A dump; T tags; P peg; Px ml])
      end;

    rule "Bootstrap PEG parser generation (Stage 3)"
      ~prod:"pegGrammar.ml"
      ~deps:["grammars/pegGrammar.peg"; "bootstrap/boot2PegParserGen.byte"]
      begin fun env _build ->
	let ml = env "pegGrammar.ml" in
	let peg = env "grammars/pegGrammar.peg" in
	let dump = env "bootstrap/boot2PegParserGen.byte" in
	let tags = tags_of_pathname ml in
	Cmd(S[A dump; T tags; P peg; Px ml])
      end;

    rule "PEG parser generation"
      ~prod:"%.ml"
      ~deps:["%.peg";"parsing/pegParserGen.byte"]
      begin fun env _build ->
	let peg = env "%.peg" in
	let ml = env "%.ml" in
	let dump = env "parsing/pegParserGen.byte" in
	let tags = tags_of_pathname ml in
	Cmd(S[A dump; T tags; P peg; Px ml])
      end;



(*
      rule "Bootstrap PEG parser generation"
        ~prod:"BootPegParser.ml"
        ~deps:["bootPegGrammar.ml",
        begin fun env _build ->

          (*c The action is a function that receive two arguments:
               [env] is a conversion function that substitutes `\%' occurrences
               according to the targets to which the rule applies.
               [_build] can be called to build new things (dynamic dependencies). *)
          let tex = env "%.tex" and _pdf = env "%.pdf" in

          (*c Here we say: ``We compile the file tex form \LaTeX\xspace to PDF''.
              Note that in fact that is a set of tags, thus the order does not
              matter. But you got the idea. *)
          let tags = tags_of_pathname tex++"compile"++"LaTeX"++"pdf" in

          (*c Here we produce the command to run.
              [S]  is for giving a sequence of command pieces.
              [A]  is for atoms.
              [P]  is for pathnames.
              [Px] is a special pathname that should be the main product of the
                   rule (for display purposes).
              [T]  is for tags.

              The other constructors are given in the documentation of the
              [Command] module in [Signatures.COMMAND]. *)
          let cmd = Cmd(S[!pdflatex; T tags; P tex; Sh"< /dev/null"]) in
          (*c Hoping that \LaTeX will converge in two iterations *)
          Seq[cmd; cmd]
        end;

      (*c Here we make an extension of any rule that produces a command
          containing these tags. *)
      flag ["compile"; "LaTeX"; "pdf"; "safe"] (A"-halt-on-error");

      (*c Here we give an exception: the file ``manual.tex'' is tagged ``safe''.\ocweol
          With this tag we add the -halt-on-error flag during the \LaTeX
          compilation. *)
      tag_file "manual.tex" ["safe"];

      (*c The generic \LaTeX rule could look at the file searching for some
          \verb'\input{}' command, but \LaTeX is so complex that it will
          be hard to make this solution complete.
          Here we manually inject some dependencies at one particular point. *)

      (*c The [dep] function takes tags and pathnames. This will build pathnames
          if a command contains these tags. Note that every file [some_file_name] is
          tagged [file:some_file_name]. *)
      dep ["compile"; "LaTeX"; "pdf"; "file:manual.tex"]
          ["ocamlweb.sty"; "myocamlbuild.tex"];

      rule "OCaml to LaTeX conversion rule (using ocamlweb)"
        ~prod:"%.tex"
        ~dep:"%.ml"
        begin fun env _build ->
          let tex = env "%.tex" and ml = env "%.ml" in
          let tags = tags_of_pathname ml++"ocamlweb"++"LaTeX" in
          Cmd(S[!ocamlweb; T tags; P ml; A"-o"; Px tex])
        end;
*)
  | hook ->

    Ocamlbuild_js_of_ocaml.dispatcher hook

end;;
