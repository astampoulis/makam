(* OASIS_START *)
(* OASIS_STOP *)

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

  | hook ->

    Ocamlbuild_js_of_ocaml.dispatcher hook

end;;
