```makam
%use "03-dependent-binding".
```

Let us now proceed to encode more features of a programming language like ML using the
techniques we have seen so far.

First, let's add polymorphism, therefore extending our simply typed lambda calculus to System
F. We will only consider the explicit polymorphism case for the time being, and explore type
inference later.

We need a type for quantification over types, as well as term-level constructs for functions
over types and instantiating a polymorphic function with a specific type.

```makam
forall : (typ -> typ) -> typ.
lamt : (typ -> term) -> term.
appt : term -> typ -> term.
```

The typing rules are similarly straightforward.

```makam
typeof (lamt E) (forall T) :-
  (a:typ -> typeof (E a) (T a)).

typeof (appt E T) (TF T) :-
  typeof E (forall TF).
```

One thing to note is that in a pen-and-paper version we would need to define a new context that
keeps track of type variables that are in scope (typically named $\Delta$), and an auxiliary
judgement of the form $\Delta \vdash \tau \text{wf}$ that checks that all type variables used
in $\tau$ are in scope. Here we get type well-formedness for free. Furthermore, if we had to
keep track of further information about type variables (e.g. their kind), we could have added
an assumption of the form `kindof a K ->`. Since the local assumption context can carry rules
for any predicate, no extra declaration or change to the existing rules would be needed, as
would be required in the pen-and-paper version in order to incorporate the new $\Delta$
context.

With these additions, we can give a polymorphic type to the identity function:

```makam
typeof (lamt (fun a => lam a (fun x => x))) T ?
```

Moving on towards a more ML-like language, we would like to add the option to declare algebraic
datatypes. This requires us to first introduce a notion of top-level programs, composed of a
series of declarations of types and terms, as well as a predicate to check that a program is
well-formed:

```makam
program : type.
wfprogram : program -> prop.
```

Let us add `let` definitions as a first example of a program component. These introduce a term
variable that can be used in the rest of the program:

```makam
let : term -> (term -> program) -> program.

wfprogram (let E P) :-
  typeof E T,
  (x:term -> typeof x T -> wfprogram (P x)).
```

We also need a "last" component for the program -- typically this takes the form of a main
expression:

```makam
main : term -> program.

wfprogram (main E) :-
  typeof E _.
```

Let us now proceed to algebraic datatypes. Datatypes have a name, a number of type parameters,
and a list of constructors; constructors themselves have a name and a list of arguments:

```makam
typeconstructor : type -> type.
constructor : type.

constructor_declaration : type -> type.
nil : constructor_declaration unit.
cons : list typ -> constructor_declaration T -> constructor_declaration (constructor * T).
datatype_declaration : type -> type -> type.
datatype_declaration : 
  (typeconstructor Arity -> dbind typ Arity (constructor_declaration Constructors)) ->
  datatype_declaration Arity Constructors.

datatype :
  datatype_declaration Arity Constructors ->
  (typeconstructor Arity -> dbind constructor Constructors program) ->
  program.
```

The datatype introduces a type constructor, as well as a number of constructors in the rest of
the program. Here we use dependency to carry the arity of the type constructor in its
meta-level type, avoiding the need for a well-formedness predicate for types. Of course, in
situations where object-level types are more complicated, we would need to incorporate kind
checking into our predicates.

Let us now proceed to well-formedness for datatype declarations. We will need two auxiliary
predicates: one that keeps information about a constructor -- which type it belongs to, what
arguments it expects; and another one that "introduces" constructors into the rest of the
program -- similar to the `intromany` predicate we have seen before.

```makam
constructor_info :
  constructor -> typeconstructor Arity -> dbind typ Arity (list typ) -> prop.

intro_constructors : [Arity Constructors]
  typeconstructor Arity -> subst typ Arity ->
  constructor_declaration Constructors -> (subst constructor Constructors -> prop) -> prop.

intro_constructors _ _ [] P :- P [].
intro_constructors TypConstr TypVars (ConstructorType :: Constructors) P :-
  applymany PolyType TypVars ConstructorType,
  (c:constructor ->
   constructor_info c TypConstr PolyType ->
   intro_constructors TypConstr TypVars Constructors (pfun cs => P (c :: cs))).
```

One interesting part in this one is the `applymany`: this is used in the opposite direction
than what we have used it so far, getting `TypVars` and `ConstructorType` as inputs, and
producing `PolyType` as an output. This is done so that we abstract over the type variables
used in the datatype declaration, creating a polymorphic type for the type of the constructor,
that can be instantiated with different types at different places.

```makam
wfprogram (datatype (datatype_declaration ConstructorDecls) Rest) :-
  (dt:(typeconstructor T) ->
    openmany (ConstructorDecls dt) (pfun tvars constructor_decls => 
      intro_constructors dt tvars constructor_decls (pfun constructors => ([Program']
        applymany (Rest dt) constructors Program',
        wfprogram Program')))).
```

In order to be able to refer to datatypes and constructors, we will need type- and term-level
formers.

```makam
tconstr : typeconstructor T -> subst typ T -> typ.
constr : constructor -> list term -> term.

typeof (constr Constructor Args) (tconstr TypConstr TypArgs) :-
  constructor_info Constructor TypConstr PolyType,
  applymany PolyType TypArgs Typs,
  map typeof Args Typs.
```

We will also need pattern matching:

```makam
patt_constr : constructor -> pattlist T T' -> patt T T'.

typeof (patt_constr Constructor Args) S' S (tconstr TypConstr TypArgs) :-
  constructor_info Constructor TypConstr PolyType,
  applymany PolyType TypArgs Typs,
  typeof Args S' S Typs.
```

As an example, we will define lists, and the append function for them:

```makam
%debug+.
wfprogram

  (datatype
    (datatype_declaration (fun llist => dbindnext (fun a => dbindbase (
    [ [] (* nil *) ,
      [a, tconstr llist [a]] (* cons of a * list a *) ]))))
  (fun llist => dbindnext (fun lnil => dbindnext (fun lcons => dbindbase (

  (main (constr lcons [zero, constr lnil []]))
  
))))) ?
```
