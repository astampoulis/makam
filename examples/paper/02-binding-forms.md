<!--
```makam
%use "01-base-language".
```
-->

As we've seen, single-variable binding as in the lambda abstraction can be handled easily through
higher-order abstract syntax. Let us now explore how to encode other forms of binding.

As a first example, we will introduce multiple-argument functions as a distinct object-level
construct, as opposed to using currying. A first attempt at encoding such a construct could be to
introduce a `list` of term variables at the same time, as follows:

```makam
lammany : (list term -> term) -> term.
```

However, this type does not correspond to the construct we are trying to encode. The type `list term
-> term` introduces a fresh local variable for the `list` type, as opposed to a number of fresh
local variables for the `term` type. Since the HOAS function space is parametric, there is no way to
even refer to the potential elements of the fresh `list` -- we can only refer to the fresh list in
full.

Instead, we would like a type that represents all types of the form:

- `term` (binding no variables)
- `term -> term` (binding a single variable)
- `term -> (term -> term)` (binding two variables)
- `term -> (term -> (term -> term))` (binding three variables) etc.

We can encode such a type inductively in λProlog, as follows:

```makam
bindmanyterms : type.
bindbase : term -> bindmanyterms.
bindnext : (term -> bindmanyterms) -> bindmanyterms.
```

Furthermore, we can generalize the type that we are binding over, and the type of the body, leading
to a polymorphic type of the form:

```makam
bindmany : type -> type -> type.
bindbase : B -> bindmany A B.
bindnext : (A -> bindmany A B) -> bindmany A B.
```

With these, `lammany` can be encoded as: 

```makam
lammany : bindmany term term -> term.
```

(As an aside: here we have allowed binding zero variables for presentation reasons.  We could
disallow binding zero variables by changing the `base` case to require an argument of type `A -> B`
instead of a `B`, similar to how we can specify lists with at least one element inductively by
replacing the `nil` constructor with a constructor that requires an element.)

How do we work with the `bindmany` type? For the built-in single binding type, we used three
operations:

- variable substitution, encoded through HOAS function application
- introducing a fresh variable, through the predicate form `x:term -> ...`
- introducing a new assumption, through the predicate form `P -> ...`

We can define three equivalent operations as predicates, for the multiple binding
case: 

-- *a generalization of application*, for substituting all the variables in a `bindmany` 

```makam
applymany : bindmany A B -> list A -> B -> prop.
applymany (bindbase Body) [] Body.
applymany (bindnext F) (HD :: TL) Body :-
  applymany (F HD) TL Body.
```

-- *local introduction of multiple fresh variables at once* within a predicate P; a list
  of the variables is passed to it 

```makam
intromany : bindmany A B -> (list A -> prop) -> prop.
intromany (bindbase _) P :- P [].
intromany (bindnext F) P :-
  (x:A -> intromany (F x) (fun tl => P (x :: tl))).
```

-- *local introduction of a number of assumptions* of the form `P X Y` within a predicate
   `Q`.
   
This is intended to be used, for example, for introducing assumptions
for predicates such as `typeof`, taking a list of term variables and a
list of types, in the same order.

```makam
assumemany : (A -> B -> prop) -> list A -> list B -> prop -> prop.
assumemany P [] [] Q :- Q.
assumemany P (X :: XS) (Y :: YS) Q :- (P X Y -> assumemany P XS YS Q).
```

These predicates are in exact correspondence with the operations we have available for the built-in
HOAS function type -- save for application being a predicate rather than a term-level construct --
so we are able to reap the benefits of HOAS representations for multiple bindings as well.

For convenience, it is also useful to define another predicate that gives access to both the
variables introduced in a `bindmany` and the body of the construct as well.  This predicate combines
`intromany`, for introducing the variables, with `applymany`, for getting the body of the construct,
and is defined as follows:

```makam
openmany : bindmany A B -> (list A -> B -> prop) -> prop.
openmany F P :-
  intromany F (pfun xs => [Body] applymany F xs Body, P xs Body).
```

Two notational idiosyncrasies here of Makam, the λProlog dialect we are using:

`pfun` is syntactic convenience for anonymous predicate literals, allowing to use the normal syntax
for propositions that we use elsewhere, i.e. in clause premises.  It is otherwise entirely
equivalent to the `fun` construct for anonymous functions.

The square bracket notation, used above in `[Body]`, introduces a new metavariable; it therefore can
be read as existential quantification. Metavariables are allowed to capture all the free variables
in scope at the point where they are introduced.  For most of them, introduced implicitly in each
clause, this means the free variables in scope when the clause is used. In this case however it is
necessary that `Body` can capture the fresh variables introduced by the `intromany` predicate too,
hence the explicit metavariable introduction.

We can now define the typing rule for `lammany` using these predicates, as follows: 

```makam
arrowmany : list typ -> typ -> typ.

typeof (lammany F) (arrowmany TS T') :-
  openmany F (fun xs body =>
    assumemany typeof xs TS (typeof body T')).
```

For example, the following query returns: 

```makam
typeof (lammany (bindnext (fun x => bindnext (fun y => bindbase (tuple [x, y]))))) T ?
>> Yes:
>> T := arrowmany [T1, T2] (product [T1, T2])
```

Adding the corresponding `appmany` construct for simultaneous application is straightforward. We can
use the `applymany` predicate defined above to encode simultaneous substitution for the evaluation
rule.

```makam
appmany : term -> list term -> term.

typeof (appmany E ES) T' :-
  typeof E (arrowmany TS T'),
  map typeof ES TS.

eval (lammany F) (lammany F).

eval (appmany E ES) V' :-
  eval E (lammany F),
  map eval ES VS,
  applymany F VS E',
  eval E' V'.
```

We can use the `bindmany` type to encode other constructs, such as mutually recursive definitions,
like the `let rec` construct of ML. In that case, we can capture the right binding structure by
introducing a number of variables simultaneously, accessible both when giving the (same number of)
definitions and the body of the construct.

We can therefore encode a `let rec` construct of the form:

```
let rec f = f_def and g = g_def in body
```

as

```
letrec (bindnext (fun f => bindnext (fun g => bindbase ([f_def, g_def]))))
       (bindnext (fun f => bindnext (fun g => bindbase body)))
```

The type-checking rule would be as follows:

```makam
letrec : bindmany term (list term) -> bindmany term term -> term.

typeof (letrec XS_Defs XS_Body) T' :-
  openmany XS_Defs (pfun xs defs =>
    assumemany typeof xs TS (map typeof defs TS)
  ),
  openmany XS_Body (pfun xs body =>
    assumemany typeof xs TS (typeof body T')
  ).
```

Still, even though this encoding matches the binding structure correctly, it is unsatisfying, as it
does not guarantee that the same number of variables are introduced in both cases and that the same
number of definitions are given. Though this requirement is enforced at the level of the typing
rules, it would be better if we could enforce it at the syntax level.  This would require some sort
of dependency though, which at first does not seem possible to do in λProlog.
