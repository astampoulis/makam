```makam
%use "03-dependent-binding".
```

Let us now proceed to encode more features of a programming language like ML using the
techniques we have seen so far.

First, let's add polymorphism, therefore extending our simply typed lambda calculus to
System F. We will only consider the explicit polymorphism case for the time being, and
explore type inference later.

We need a type for quantification over types, as well as term-level constructs for
functions over types and instantiating a polymorphic function with a specific type.

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

One thing to note is that in a pen-and-paper version we would need to define a new
context that keeps track of type variables that are in scope (typically named
$\Delta$), and an auxiliary judgement of the form $\Delta \vdash \tau \text{wf}$ that
checks that all type variables used in $\tau$ are in scope. Here we get type
well-formedness for free. Furthermore, if we had to keep track of further information
about type variables (e.g. their kind), we could have added an assumption of the form
`kindof a K ->`. Since the local assumption context can carry rules for any predicate,
no extra declaration or change to the existing rules would be needed, as would be
required in the pen-and-paper version in order to incorporate the new $\Delta$
context.

With these additions, we can give a polymorphic type to the identity function:

```makam
typeof (lamt (fun a => lam a (fun x => x))) T ?
```

Moving on towards a more ML-like language, we would like to add the option to declare
algebraic datatypes. This requires us to first introduce a notion of top-level
programs, composed of a series of declarations of types and terms, as well as 
a predicate to check that a program is well-formed. In keeping with an
ML-like language, we could do something more general than that: add ML-style modules.
We will need to introduce the ability to create module structures and signatures --
corresponding to the implementation and specification parts of modules. Structures
are composed of a series of declarations, while signatures are composed of a series
of specifications. Therefore:

```makam
declaration, specification : type.
struct, sig : type.

struct : list declaration -> struct.
sig : list specification -> sig.
```

`let` definitions are our first example of a module component:

```makam
let : string -> term -> declaration.
val : string -> typ -> specification.
```

One thing to note is the presence of strings: as opposed to what we've seen so far,
we'll be using concrete strings in the different components of structures and
signatures, as opposed to abstract binders through higher-order abstract syntax. The
reason for this is two-fold: first, matching components between a structure and a
signature is done based on their concrete names; and second, there is not really a
case where we would need substitution for the abstract variables, have we used those
instead. As a result, we do not have to use a higher-order representation for the
variables used in modules, and we can go with a normal first-class representation
instead.

The typing rule of a `let` declaration should make sure that the term matches the type
of the corresponding `val` specification, and also that the corresponding named
variable gets the right type in the rest of the module. In order to be able to capture
the latter part, we will use a list of propositions, representing local assumptions
that should be made in the rest of the module. We will also need a term constructor
for named variables:

```makam
named : string -> term.
specof : declaration -> specification -> list prop -> prop.
specof (let S E) (val S T) [typeof (named S) T] :-
  typeof E T.
```

Let us now move on to datatypes. Datatypes have a name, a number of type parameters,
and a list of constructors; constructors themselves have a name and a list of
arguments. We will only allow transparent datatypes for now, whose specification
matches their declaration.

```makam
datatype_decl, constructor_decl : type.
datatype_decl : string -> dbind typ T (list constructor) -> datatype_decl.
constructor_decl : string -> subst typ T' -> constructor_decl.
struct_datatype : datatype_decl -> declaration.
sig_datatype : datatype_decl -> specification.
```

We will also need type- and term-level constructs for referring to a datatype and
a constructor, respectively:

```makam
d : string -> subst typ T -> typ.
c : string -> subst term T -> term.
```

Typing:

```makam
datatype : datatype_decl -> prop.

wftype : typ -> prop.
wftype (d S Args) :-
  datatype (datatype_decl S Decl),
  intromany Decl (pfun typevars =>
    map (pfun var arg => wftype arg) typevars Args
  ).
```

specof (struct_datatype Datatype) (sig_datatype Datatype)
       ((datatype DataType) : ConstructorAssumptions) :-
  eq Datatype (datatype_decl TypeName Declaration),
  (datatype (datatype_decl TypeName Declaration) ->
    wf_constructors


We will also need predicates that relate definitions to specifications, and structures
to signatures. (We will focus on principal signatures for the time being, 

```makam
specof : string -> declaration -> specification -> list prop -> type.
sigof : struct -> sig -> type.
```

```makam
sigof (struct S) (sig SI) :-
  principal_sigof S SI',
  sigmatch SI' SI.

principal_sigof (struct []) [].
principal_sigof ((S, Decl) :: Decls) ((S, Spec) :: Specs) :-
  principal_sigof S Decl Spec Assumptions,
  assumemany Assumptions (sigof Decls Specs).
  

We need a predicate that relates definitions to specifications:

```makam
