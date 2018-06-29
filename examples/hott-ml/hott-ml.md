# Experiment: Extending an ML-like language with higher-inductive types

This is an experiment to see what an extension to ML and ML pattern matching
with higher-inductive types would look like (actually just quotients, so just
one level up of non-trivial equalities).

The example we will try to encode is the following definition of bags:

```
data bag =
  nil
| cons of int * bag
with
| swap : forall A B Rest, cons A (cons B Rest) == cons B (cons A rest)
```

Functions defined by pattern matching need to respect the extra equality
constructors. Mostly want to find a good way to write the pattern match.

But first, let's define a base ML-like language. This will take a while.

```makam
tests : testsuite. %testsuite tests.

expr : type.
typ : type.

etuple : list expr -> expr.

letrec : bindone expr (expr * expr) -> expr.
let : expr -> bindone expr expr -> expr.
lam : bindmany expr expr -> expr.
app : expr -> list expr -> expr.

patt : type.
branch : type.
branch : patt * bindmany expr expr -> branch.
match : expr -> list branch -> expr.

ptuple : list patt -> patt.
pvar : patt.

program : type.
main : expr -> program.

constructor : type.

datadef : type -> type.
datadef : bindone typ (list typ * bindmany constructor T) -> datadef T.
data : datadef program -> program.

constr : constructor -> expr -> expr.
pconstr : constructor -> patt -> patt.

product : list typ -> typ.
arrowmany : list typ -> typ -> typ.
eint : int -> expr.
tint : typ.

sig : type.
smain : typ -> sig.
sdata : datadef sig -> sig.
```

Now let's write syntax for this:

```makam
expr, baseexpr : syntax expr.
patt : syntax patt.
typ : syntax typ.
constructor : syntax constructor.
branch : syntax branch.
id : syntax (concrete.name expr).
def : syntax (concrete.name expr * expr).
program : syntax program.
program_concrete : syntax (concrete program).

%open syntax.

exprvar : concrete.namespace expr.

clet : (concrete.name expr * expr) -> expr -> expr.
cletrec : (concrete.name expr * expr) -> expr -> expr.
cpvar : concrete.name expr -> patt.
cbranch : patt -> expr -> branch.

`( syntax_rules {{

program_concrete -> concrete { <program> }

expr -> etuple nil
        { "()" }
      / (fun hd => fun tl => etuple (cons hd tl))
        { "(" <expr> "," <list_sep (token ",") expr> ")" }
      / match
        { "match" <expr> "{" <list_sep (token "|") branch> "}" }
      / cletrec
        { "let" "rec" <def> "in" <expr> }
      / clet
        { "let" <def> "in" <expr> }
      / (fun ids => fun body => lam (concrete.bindmany ids body))
        { "fun" <once_or_many id> "=>" <expr> }
      / app
        { <baseexpr> "(" <list_sep_plus (token ",") expr> ")" }
      / { <baseexpr> }

baseexpr ->
        concrete.var
        { <id> }
      / { "(" <expr> ")" }

patt -> ptuple nil
        { "()" }
      / (fun hd => fun tl => ptuple (cons hd tl))
        { "(" <patt> "," <list_sep (token ",") patt> ")" }
      / cpvar
        { <id> }

def -> tuple
        { <id> "=" <expr> }

id -> concrete.name exprvar
        { <makam.ident> }

branch -> cbranch
        { <patt> "=>" <expr> }

}} ).


(* now let's add datatype definitions and constructors *)

constrvar : concrete.namespace constructor.
typvar : concrete.namespace typ.

cdatadef : concrete.name typ -> list (concrete.name constructor * typ) -> program -> datadef program.
cdatadef_sig : concrete.name typ -> list (concrete.name constructor * typ) -> sig -> datadef sig.

datadef : syntax (datadef program).
datadef_sig : syntax (datadef sig).
constrdef : syntax (concrete.name constructor * typ).
typ, prodtyp, basetyp : syntax typ.
typid : syntax (concrete.name typ).
constrid : syntax (concrete.name constructor).

sig : syntax sig.
sig_concrete : syntax (concrete sig).

`( syntax_rules {{

datadef -> cdatadef
           { "data" <typid> "=" <list_sep (token "|") constrdef> ";" (optunit ws_newline) <program> }

datadef_sig -> cdatadef_sig
           { "data" <typid> "=" <list_sep (token "|") constrdef> ";" (optunit ws_newline) <sig> }

constrdef -> tuple
           { <constrid> "of" <typ> }

typ -> (fun t => fun t2 => arrowmany (cons t nil) t2)  { <basetyp> "->" <typ> }
     / arrowmany { "(" <list_sep (token ",") typ> ")" "->" <typ> }
     / prodtyp ;

prodtyp -> (fun hd => fun tl => product (cons hd tl)) { <basetyp> "*" <list_sep_plus (token "*") basetyp> }
     / basetyp ;

basetyp -> tint { "int" }
         / concrete.var { <typid> }
         / product nil { "()" }
         / { "(" <typ> ")" }

typid -> concrete.name typvar { <makam.ident> }

constrid -> concrete.name constrvar { "`" <makam.ident> }

program -> data { <datadef> } / main { <expr> }

expr -> (fun c => fun e => constr (concrete.var c) e)
        { <constrid> <expr> }
      / eint
        { <makam.int_literal> }

patt -> (fun c => fun p => pconstr (concrete.var c) p)
        { <constrid> <patt> }

sig -> sdata { <datadef_sig> } / smain { "(main)" ":" <typ> }

sig_concrete -> concrete { "sig" <sig> "end" }
}}).

`( syntax.def_toplevel_js sig_concrete ).
`( syntax.def_toplevel_js program_concrete ).
```

```makam
concrete.pick_namespace_userdef (_: expr) exprvar.
concrete.pick_namespace_userdef (_: constructor) constrvar.
concrete.pick_namespace_userdef (_: typ) typvar.

concrete.resolve_conversion
    (clet (Name, Def) Body)
    (let Def (concrete.bindone Name Body)).

concrete.resolve_conversion
    (cletrec (Name, Def) Body)
    (letrec (concrete.bindone Name (Def, Body))).

concrete.resolve_conversion (cpvar N) pvar.

(* TODO: this destroys bidirectionality, so need an inverse too *)
concrete.resolve_conversion
    (cbranch P E)
    (branch (P', concrete.bindmany Names E)) when refl.isunif P' :-
  concrete.names_of exprvar P Names,
  concrete.resolve (concrete P) P'.

concrete.resolve_conversion
    (cbranch P E)
    (branch (P', concrete.bindmany Names E)) when refl.isunif P :-
  concrete.resolve (concrete P) P',
  concrete.names_of exprvar P Names.

concrete.resolve_conversion
    (cdatadef Typ Constrs Body)
    (datadef (concrete.bindone Typ (Typs, (concrete.bindmany Names Body)))) :-
  zip Names Typs Constrs.

concrete.resolve_conversion
    (cdatadef_sig Typ Constrs Body)
    (datadef (concrete.bindone Typ (Typs, (concrete.bindmany Names Body)))) :-
  zip Names Typs Constrs.

>> concrete.names_of exprvar (ptuple [cpvar (concrete.name exprvar "a"), cpvar (concrete.name exprvar "b")]) X ?
>> Yes:
>> X := [concrete.name exprvar "a", concrete.name exprvar "b"].

>> syntax.run program_concrete {{ let x = () in x }} X ?
>> Yes:
>> X := concrete (main (clet (tuple (concrete.name exprvar "x") (etuple nil)) (concrete.var (concrete.name exprvar "x")))).

>> syntax.run program_concrete {{ let x = () in match x { (a, b) => a } }} X ?
>> Yes:
>> X :=concrete (main (clet (tuple (concrete.name exprvar "x") (etuple nil)) (match (concrete.var (concrete.name exprvar "x")) (cons (cbranch (ptuple (cons (cpvar (concrete.name exprvar "a")) (cons (cpvar (concrete.name exprvar "b")) nil))) (concrete.var (concrete.name exprvar "a"))) nil)))).

>> (syntax.run program_concrete {{ let x = () in match x { (a, b) => a } }} _X, concrete.resolve _X Y) ?
>> Yes:
>> Y := main (let (etuple nil) (bind "x" (fun anon10331_0 => match anon10331_0 (cons (branch (tuple (ptuple (cons pvar (cons pvar nil))) (bind "a" (fun anon10316_1 => bind "b" (fun anon9147_2 => body anon10316_1))))) nil)))).

>> (isocast {{
 data tree = `leaf of () | `node of tree * int * tree ;
   letrec map = fun f tree =>
     match tree {
       `leaf() => `leaf()
     | `node(l, i, r) => `node(map(f,l), f(i), map(f,r))
     }
   in map
 }} (_X: concrete program), concrete.resolve _X _Y, concrete.resolve _Z _Y, eq_nounif _Z _X) ?
>> Yes.
```

```makam
typeof : expr -> typ -> prop.
typeof : patt -> typ -> list typ -> list typ -> prop.

typeof (etuple ES) (product TS) :-
  map typeof ES TS.

typeof (lam XS_Body) (arrowmany TS T) :-
  bindmany.open XS_Body (pfun XS Body => assume_many typeof XS TS (typeof Body T)).

typeof (app E ES) T :-
  typeof E (arrowmany TS T), map typeof ES TS.

typeof (let E X_Body) T' :-
  typeof E T,
  bindone.open X_Body (pfun X Body => (typeof X T -> typeof Body T')).

typeof (letrec X_DefBody) T' :-
  bindone.open X_DefBody (pfun X (Def, Body) => (typeof X T -> (typeof Def T, typeof Body T'))).

typeofbranch : typ -> typ -> branch -> prop.
typeofbranch T T' (branch (P, XS_Body)) :-
  typeof P T [] TS,
  bindmany.open XS_Body (pfun XS Body => assume_many typeof XS TS (typeof Body T')).
typeof (match E Branches) T' :- typeof E T, map (typeofbranch T T') Branches.

typeof pvar T VS VS' :- snoc VS T VS'.
typeof (ptuple []) (product []) VS VS.
typeof (ptuple (P :: PS)) (product (T :: TS)) VS VS'' :-
  typeof P T VS VS',
  typeof (ptuple PS) (product TS) VS' VS''.

typeof (eint N) tint.

datadef_constructor : typ -> constructor -> typ -> prop.
datadef_all_constructors : typ -> list constructor -> prop.

typeof (constr C E) T :-
  datadef_constructor T C T_Arg,
  typeof E T_Arg.

typeof (pconstr C P) T VS VS' :-
  datadef_constructor T C T_Arg,
  typeof P T_Arg VS VS'.

>> (a:typ -> b:typ -> typeof (ptuple [pvar, pvar]) (product [a, b]) [] #XS) ?
>> Yes:
>> XS := fun a b => [a, b].

%extend datadef.
open : datadef T -> (typ -> list typ -> list constructor -> T -> prop) -> prop.
open (datadef X) P :-
  bindone.open X (pfun Typ (ConstrTS, CS_Rest) =>
    bindmany.open CS_Rest (pfun CS Rest =>
      P Typ ConstrTS CS Rest)).

apply : datadef T -> typ -> list typ -> list constructor -> T -> prop.
apply (datadef X) T ConstrTS Constrs Body :-
  bindone.apply X T (ConstrTS, CS_Body),
  bindmany.apply CS_Body Constrs Body.
%end.

wfprogram : program -> sig -> prop.
wfprogram (main E) (smain T) :- typeof E T.

wfprogram (data (datadef D)) (sdata (datadef D')) :-
  bindone.openmany [D, D'] (pfun T [(ConstrTS, CS_Rest), (ConstrTS', CS_Rest')] =>
    eq ConstrTS ConstrTS',
    bindmany.openmany [CS_Rest, CS_Rest'] (pfun Constrs [Body, TSig] =>
      (datadef_all_constructors T Constrs ->
      assume_many (datadef_constructor T) Constrs ConstrTS (
        wfprogram Body TSig)))).

typechecker : string -> sig -> prop.

typechecker S Sig :- isocast S (P: program), wfprogram P Sig.

>> typechecker {{
 data tree = `leaf of () | `node of tree * int * tree ;
 `leaf()
}} X ?
>> Yes:
>> X := sdata (datadef (bind "tree" (fun anon10972_0 => tuple (cons (product nil) (cons (product (cons anon10972_0 (cons tint (cons anon10972_0 nil)))) nil)) (bind "leaf" (fun anon10316_1 => bind "node" (fun anon10324_2 => body (smain anon10972_0))))))).

>> typechecker {{
 data tree = `leaf of () | `node of tree * int * tree ;
   letrec map = fun f tree =>
     match tree {
       `leaf() => `leaf()
     | `node(l, i, r) => `node(map(f,l), f(i), map(f,r))
     }
   in map
}} Y ?
>> Yes:
>> Y := sdata (datadef (bind "tree" (fun anon54076_0 => tuple (cons (product nil) (cons (product (cons anon54076_0 (cons tint (cons anon54076_0 nil)))) nil)) (bind "leaf" (fun anon43328_1 => bind "node" (fun anon43336_2 => body (smain (arrowmany (cons (arrowmany (cons tint nil) tint) (cons anon54076_0 nil)) anon54076_0)))))))).

>> (typechecker {{
 data tree = `leaf of () | `node of tree * int * tree ;
   letrec map = fun f tree =>
     match tree {
       `leaf() => `leaf()
     | `node(l, i, r) => `node(map(f,l), f(i), map(f,r))
     }
   in map
}} _Y, concrete.resolve (_X: concrete sig) _Y, syntax.pretty sig_concrete _X S) ?
>> Yes:
>> S := {{sig data tree = ` leaf of () | ` node of tree * int * tree ; 
(main) : ( int -> int , tree ) -> tree end }}.

```

## Annotation framework

First, this is an experimental implementation of *annotation*: it
allows us to annotate each node of a certain type `BaseType` with
extra information of type `AnnotationType`.  This way we can add, for
example, a type `T` alongside each expression node `E` in our
language.  By a careful addition to our typing predicate, the types
that get figured out during typing can be stored as `T`, therefore
allowing us to design (independent) phases that depend on typing.

This is similar to this common trick in compiler design:
```
data expr' = App of expr * expr
           | BinOp of binop * expr * expr
           | ...
and expr = expr' * type
...
```

The nice thing about this is:
- the conversion from a tree without annotated nodes to one that is fully
  annotated (albeit with empty information), does not require any boilerplate.
  This is thanks to `structural` recursion.
- the changes needed to our typing procedure are minimal

This is still experimental, and has no tests, so not making this part of the stdlib just yet.

```makam
annotated : type -> type -> type -> type.
annotated : RootType -> annotated BaseType Annotation RootType.

annotation : BaseType -> Annotation -> BaseType.

annotator : [A]A -> annotated BaseType Annotation A -> prop.
annotator_aux, annotator_cases : [A](BaseType * Annotation) -> A -> A -> prop.

annotator (X: RootType) (annotated Y: annotated BaseType Annotation RootType) :-
  annotator_aux (_: (BaseType * Annotation)) X Y.

annotator_aux TypeProxy X Y :-
  structural (annotator_aux TypeProxy) X X',
  demand.case_otherwise ((annotator_cases TypeProxy) X' Y)
                        (eq X' Y).

annotator_cases (TypeProxy: BaseType * AnnotationType) (X: BaseType) (annotation X (A: AnnotationType)).


deannotator : [A]annotated BaseType Annotation A -> A -> prop.
deannotator_aux, deannotator_cases : [A](BaseType * Annotation) -> A -> A -> prop.

deannotator (annotated Y: annotated BaseType Annotation RootType) (X: RootType) :-
  deannotator_aux (_: (BaseType * Annotation)) X Y.

deannotator_aux TypeProxy X Y :-
  demand.case_otherwise ((annotator_cases TypeProxy) Y' Y)
                        (eq Y' Y),
  structural (deannotator_aux TypeProxy) X Y'.

isocast_def (iso.iso annotator deannotator).
```

(isocast {{
  data list = `nil of () | `cons of int * list ;
   letrec map = fun f list =>
     match list {
       `nil() => `nil()
     | `cons(hd, tl) => `cons(f(hd), map(f, tl))
     }
   in map
}} (_P: program), typer _P P') ?

```

## The actual experiment

