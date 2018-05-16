(function(mod) {
  if (typeof exports == "object" && typeof module == "object")
    // CommonJS
    mod(require("codemirror/lib/codemirror"));
  else mod(CodeMirror);
})(function(CodeMirror) {
  "use strict";

  const comment = { regex: /\(\*/, push: "comment", token: "comment" };
  const base = [
    { regex: /"(?:[^\\]|\\.)*?(?:"|$)/, token: "string" },
    { regex: /`\(/, sol: true, token: "builtin strong", next: "staging" },
    { regex: /`/, token: "string", push: "expansion" },
    { regex: /[1-9][0-9]*/, token: "number" },
    { regex: /\{[a-z]+\|/, token: "string strong", push: "freequote_brpp" },
    { regex: /\{\{/, token: "string strong", push: "freequote_brbr" },
    { regex: /\<\</, token: "string strong", push: "freequote_abab" },
    { regex: /\{/, token: "string strong", push: "freequote_br" },
    { regex: /\%[a-z]+/, token: "builtin" },
    comment,
    {
      regex: /(Yes(:|\.)|Impossible\.)/
    },
    {
      regex: /\>\>/,
      sol: true,
      token: "builtin"
    },
    { regex: /[A-Z_][A-Za-z_\\'0-9]*/, token: "variable-2" }, //metavars
    {
      regex: /(if|then|else|when|fun|pfun)\b/,
      token: "keyword"
    },
    {
      regex: /[a-z][a-zA-Z0-9_\']*/,
      sol: true,
      token: "def",
      push: "definition"
    },
    {
      regex: /[a-z][a-zA-Z0-9_\']*/
    },
    { regex: /(\<-|:-)/, token: "builtin", indent: true },
    { regex: /(:=|-\>)/, token: "builtin" },
    { regex: /=\>/, token: "keyword" },
    {
      regex: /(\.|\?)(\s|$)/,
      dedent: true,
      dedentIfLineStart: true
    }
  ];

  CodeMirror.defineSimpleMode("makam", {
    start: base,
    staging: [].concat(
      [{ regex: /\)\./, token: "builtin strong", next: "start" }],
      base
    ),
    const_definition: [
      {
        regex: /[a-z][a-zA-Z0-9_\']*/,
        token: "def"
      },
      { regex: /:/, next: "type_in_definition" }
    ],
    definition: [
      { regex: /\s*,\s*/, next: "const_definition" },
      { regex: /\s*:\s*/, next: "type_in_definition" },
      { regex: /\s/, pop: true }
    ],
    type_in_definition: [
      { regex: /(type|prop)\b/, token: "keyword" },
      { regex: /[a-z][a-zA-Z0-9_\']*/, token: "type" },
      { regex: /-\>/, token: "meta" },
      { regex: /[A-Z_][A-Za-z_\\'0-9]*/, token: "variable-2" }, //metavars
      { regex: /\./, pop: true }
    ],
    expansion: [
      { regex: /\$\{/, push: "expansion_quote", token: "meta" },
      { regex: /\$\`/, pop: true, token: "string" },
      { regex: /\$[^\{]/, token: "string" },
      { regex: /(?:[^\\`\$]|\\.)+/, token: "string" },
      { regex: /\`/, pop: true, token: "string" }
    ],
    expansion_quote: [].concat(
      [{ regex: /\}/, pop: true, token: "meta" }],
      base
    ),
    freequote_brpp: [
      { regex: /\|\}/, token: "string strong", pop: true },
      { regex: /[^\|]+/, token: "string" },
      { regex: /\|/, token: "string" },
    ],
    freequote_brbr: [
      { regex: /\}\}/, token: "string strong", pop: true },
      { regex: /[^\}]+/, token: "string" },
      { regex: /\}/, token: "string" }
    ],
    freequote_abab: [
      { regex: /\>\>/, token: "string strong", pop: true },
      { regex: /[^\>]+/, token: "string" },
      { regex: /\>/, token: "string" }
    ],
    freequote_br: [
      { regex: /\}/, token: "string strong", pop: true },
      { regex: /[^\}]+/, token: "string" }
    ],
    comment: [
      // { regex: /\(\*/, token: "comment", push: "comment" },
      { regex: /.*\*\)/, token: "comment", pop: true },
      { regex: /.*/, token: "comment" }
    ]
  });

  CodeMirror.defineSimpleMode("makam-query-results", {
    start: [
      { regex: /^(Yes(:|\.)|Impossible\.)/, mode: { spec: "makam" } }
    ]
  });
});
