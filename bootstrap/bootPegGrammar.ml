open Peg;;
open Batteries;;
open ToploopTools;;

open Camlp4.PreCast;;
let _loc = Loc.ghost;;

let pegGrammar =
  let open PEGshort in peg

(Some <:str_item<
  open Peg ;;
  open Batteries ;;
>>)

[

"commentchar", "", [ [ neg (s "*)"); wild ], "_ _", `A <:expr< () >> ];
"white", "", [ [ test wild <:expr< UString.is_whitespace >>; wild ], "_ _", `A <:expr< () >> ;
	      [ s "(*"; nP "repV" [n "commentchar"]; s "*)" ], "_ _ _", `A <:expr< () >> ] ;
"latin1char", "", [ [ test wild <:expr< fun c -> try ignore(UChar.char_of c); true with _ -> false >>; wild ], "_ a", `A <:expr< a >> ] ;
"letterchar", "", [ [ test wild <:expr< fun c -> match UString.category c with `Ll | `Lm | `Lo | `Lt | `Lu -> true | _ -> false >>; wild ], "_ a", `A <:expr< a >> ] ;
"symnumchar", "", [ [ test wild <:expr< fun c -> match UString.category c with `Mc | `Me | `Mn | `Nd | `Nl | `No | `Pc | `Pd | `Pe | `Pf | `Pi | `Po | `Sc | `Sk | `Sm | `So -> true | _ -> false >>; wild ], "_ a", `A <:expr< a >> ] ;
"alphanumchar", "", [ [ (n "letterchar") // (n "symnumchar") ], "a", `A <:expr< a >> ] ;
"digitchar", "", [ [ c "0123456789" ], "a", `A <:expr< a >> ] ;
"hexdigitchar", "", [ [ c "0123456789abcdefABCDEF" ], "a", `A <:expr< a >> ] ;
"eof", "", [ [ neg wild ], "_", `V ];

"repplus", "p", [ [ n "p"; nP "repplus" [n "p"] ], "hd tl", `A <:expr< hd :: tl >> ;
		[ n "p" ], "hd", `A <:expr< [hd] >> ] ;
"repplusV", "p", [ [ n "p"; nP "repplusV" [n "p"] ], "_ _", `A <:expr< () >> ;
		 [ n "p" ], "_", `A <:expr< () >> ] ;
"rep", "p", [ [ n "p"; nP "rep" [n "p"] ], "hd tl", `A <:expr< hd :: tl >> ;
            [ epsilon ], "_", `A <:expr< [ ] >> ] ;
"repV", "p", [ [ n "p"; nP "repV" [n "p"] ], "_ _", `A <:expr< () >> ;
	     [ epsilon ], "_", `A <:expr< () >> ] ;

"token", "p",   [ [ nPM "repV" [ n "white" ]; n "p" ], "_ _", `A <:expr< () >> ] ;
"keyword", "p", [ [ nPM "repV" [ n "white" ]; n "p" ], "_ a", `A <:expr< a >> ] ;

"identfstchar", "", [ [ ahd (n "latin1char"); n "letterchar" ], "_ c", `A <:expr< c >> ];
"identrstchar", "", [ [ ahd (n "latin1char"); (n "letterchar") // (n "digitchar") // (c "_'") ],
		       "_ c", `A <:expr< c >> ];
"ident", "", [ [ n "identfstchar"; nP "rep" [ n "identrstchar" ] ], "c cs", `A <:expr< (c :: cs) |> UString.implode |> UString.to_string >> ];

"escapechar", "",
            [ [ c "\\"; c "\\\"'ntbr" ], "s c", `A <:expr< [s;c] |> UString.implode |> UString.to_string>>;
	      [ c "\\"; n "digitchar"; n "digitchar"; n "digitchar" ], "s n1 n2 n3", `A <:expr< [s;n1;n2;n3] |> UString.implode |> UString.to_string >> ;
	      [ c "\\"; c "x"; n "hexdigitchar"; n "hexdigitchar"; n "hexdigitchar" ], "s x n1 n2 n3", `A <:expr< [s;x;n1;n2;n3] |> UString.implode |> UString.to_string >> ];

"strchar", "", [ [ n "escapechar" ], "s", `A <:expr< Utils.unescape s >> ;
		[ neg (s "\""); wild ], "_ c", `A <:expr< [ c ] |> UString.implode |> UString.to_string >> ];
"classchar", "", [ [ neg (s "]"); n "strchar" ], "_ s", `A <:expr< s >>;
		  [ s "\"" ], "_", `A <:expr< "\"" >>;
		  [ s "]"; ahd (s "]") ], "_ _", `A <:expr< "]" >> ];

"str", "", [ [ nP "repplus" [ n "strchar" ] ], "cs", `A <:expr< cs |> String.concat "" >> ];

"repSEP", "p sep", [ [ nM "p"; nP "token" [ n "sep" ] ; nP "repV" [ n "white" ]; nP "repSEP" [ n "p"; n "sep" ] ], "hd _ _ tl", `A <:expr< hd :: tl >> ;
		       [ nM "p" ], "hd", `A <:expr< [ hd ] >> ];

"repSEPnowhite", "p sep", [ [ nM "p"; nM "sep" ; nPM "repV" [ n "white" ]; nP "repSEPnowhite" [n "p"; n "sep"] ], "hd _ _ tl", `A <:expr< hd :: tl >> ;
		       [ nM "p"; opt (concats ( [ nM "sep" ; nPM "repV" [ n "white" ] ], "_ _", `A <:expr< () >> )) ], "hd _", `A <:expr< [ hd ] >> ];

"repWHITE", "p", [ [ nM "p"; nP "repplusV" [ n "white" ]; nP "repWHITE" [ n "p" ] ], "hd _ tl", `A <:expr< hd :: tl >> ;
		 [ nM "p"; nP "repV" [ n "white" ] ], "hd _", `A <:expr< [ hd ] >> ;
		 [ epsilon ], "_", `A <:expr< [] >> ];

"to", "", [ [ s "->" ], "_", `A <:expr< () >> ;
	   [ s "→" ], "_", `A <:expr< () >> ] ;
"parenthesized", "p", [ [ nP "token" [ s "(" ]; n "p"; nP "token" [ s ")" ] ], "_ p _", `A <:expr< p >> ];

"ocamlchar", "", [ [ neg (s ">>"); wild ], "_ c", `A <:expr< c >> ];
"ocamltext", "", [ [ nP "repplus" [ n "ocamlchar" ] ], "cs", `A <:expr< cs |> UString.implode |> UString.to_string >> ];

"peg", "", [ [ opt (n "ocamltopquote"); nP "repSEPnowhite" [ n "def"; n "defsep" ]; opt(n "ocamltopquote") ], "preamble defs postamble", `A <:expr< PEGshort.pegNoDefProds preamble defs postamble >> ] ;

"whiteNoNewline", "", [ [ neg (c "\n"); n "white" ], "_ _", `A <:expr< () >> ] ;
"defsep", "", [ [ nPM "repV" [ n "whiteNoNewline" ]; nP "token" [ s ";" ] ], "_ _", `A <:expr< () >> ;
	       [ nPM "repV" [ n "whiteNoNewline" ]; s "\n";
		 ahd (
		   concats ( [ nPM "keyword" [n "ident"]; nM "paramdef"; nPM "token" [n "to"] ], "_ _ _", `V ) 
		 // nPM "token" [ n "eof" ] ) ], "_ _ _", `A <:expr< () >> ] ;

"choices", "", [ [ nP "repSEP" [ n "production"; s "/" ] ], "productions", `A <:expr< PEGshort.choices productions >> ];
"def", "", [ [ nPM "keyword" [n "ident"] ; nM "paramdef"; nPM "token" [ n "to" ] ; n "choices" ], "nt params _ prod", 
	     `A <:expr< nt, params, prod >> ];

"paramdef", "", [ [ nP "token" [ s "(" ]; nP "repSEP" [n "ident"; s ","] ; nP "token" [ s ")" ] ], "_ params _", `A <:expr< params |> String.concat " " >> ;
	        [ epsilon ], "_", `A <:expr< "" >> ];

"params", "", [ [ nP "token" [ s "(" ]; nP "repSEP" [n "prim"; s ","]; nP "token" [ s ")" ] ], "_ params _", `A <:expr< params >> ;
	        [ epsilon ], "_", `A <:expr< [] >> ];

"ocamlquote", "", [ [ nP "token" [ s "<<" ]; n "ocamltext"; nP "token" [ s ">>" ] ], "_ ocamltext _", 
		    `A <:expr< ToploopTools.parseAST ocamltext >> ];

"ocamltopquote", "", [ [ nP "token" [ s "<<" ]; n "ocamltext"; nP "token" [ s ">>" ] ], "_ ocamltext _", 
		    `A <:expr< ToploopTools.parseAST_stritem ocamltext >> ];

"innerchoice", "", [ [ nP "repSEP" [ n "prim"; s "/" ] ], "primlist", `A <:expr< PEGshort.choices primlist >> ];

"production", "", [ [ nPM "repWHITE" [ n "namedprim" ]; n "ocamlquote" ], "namedprim ocamlaction",
		    `A <:expr< let names, primlist = List.split namedprim in
		               PEGshort.concats (primlist, String.concat " " names, `A ocamlaction) >>;
		   [ nPM "repWHITE" [ n "namedprim" ] ], "namedprim", 
		    `A <:expr< let names, primlist = List.split namedprim in
                               PEGshort.concats (primlist, String.concat " " names, `V) >>
		  ];

"namedprim", "", [ [ nPM "keyword" [n "ident"]; nP "token" [s ":"]; n "prim"],
		    "name _ prim", `A <:expr< (name, prim) >> ;
		  [ n "prim" ], "prim", `A <:expr< ("_", prim) >> ];

"prim", "", [ 
  [ nP "token" [s "."] ], "_", `A <:expr< PEGshort.wild >> ;
  [ nP "token" [s "\""]; nP "rep" [n "strchar"]; s "\"" ], "_ str _", `A <:expr< PEGshort.s ( str |> String.concat "" ) >> ;
  [ nP "token" [s "["]; nP "rep" [n "classchar"]; s "]" ], "_ str _", `A <:expr< PEGshort.c ( str |> String.concat "" ) >> ;
  [ nP "token" [s "!"]; n "prim" ], "_ p", `A <:expr< PEGshort.neg p >> ;
  [ nP "token" [s "&&"]; nP "token" [s "("]; n "prim"; n "ocamlquote"; nP "token" [s ")"] ],
    "_ _ p test _", `A <:expr< PEGshort.test p test >> ;
  [ nP "token" [s "&"]; n "prim" ], "_ p", `A <:expr< PEGshort.ahd p >> ;
  [ nP "token" [s "?"]; n "prim" ], "_ p", `A <:expr< PEGshort.opt p >> ;
  [ nP "token" [s "#"]; n "number"; opt (nP "token" [ s"^"])], "_ p mem", `A <:expr< match mem with Some _ -> PEGshort.memo (PEGshort.p p) | None -> PEGshort.p p >> ;
  [ nP "token" [s "fail"] ], "_", `A <:expr< PEGshort.void >> ;

  [ nP "keyword" [n "ident"]; n "params"; opt (nP "token" [ s"^"]) ], "id params mem", `A <:expr< let open PEGshort in match mem with Some _ -> memo (nP id params) | None -> nP id params >> ;
  [ nP "token" [s "\""]; n "str"; nP "token" [s "\""] ],
	      "_ str _", `A <:expr< let open PEGshort in s str >> ;
  [ nP "parenthesized" [nM "innerchoice"]; opt (nP "token" [ s"^"]) ], "p mem", `A <:expr< match mem with Some _ -> PEGshort.memo p | None -> p >> ;
  [ nP "parenthesized" [nM "choices"]; opt (nP "token" [ s"^"]) ], "p mem", `A <:expr< match mem with Some _ -> PEGshort.memo p | None -> p >> ];

"number", "", [ [ nP "keyword" [ nP "repplus" [ n "digitchar" ] ] ], "i", `A <:expr< i |> UString.implode |> UString.to_string |> int_of_string >> ]

]

None

;;


(* useAST (parseGen pegGrammar) "test_gen_peg.ml";; *)
(* printAST (parseGen pegGrammar);; *)
(* defAST (parseGen pegGrammar);; *)
