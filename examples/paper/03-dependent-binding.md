```makam
%use "02-binding-forms".
```

The type system of λProlog can be viewed as a particular subset of System Fω: namely, it is the
simply typed lambda calculus extended with prenex polymorphism and simple type constructors of the
form `type -> type -> ... -> type`. (As an aside, `prop` can be viewed as a separate sort, but we
take the view that it is just a distinguished extensible type.)

As is well-known from Haskell even before the addition of kind definitions, type promotion and
type-in-type, this subset of System Fω is enough to model some form of dependency. For example, we
can introduce two types for modelling natural numbers, and define vectors as a GADT using those:

```makam
natZ : type.
natS : type -> type.

vector : type -> type -> type.
vnil : vector natZ A.
vcons : A -> vector N A -> vector (natS N) A.
```

In fact, λProlog naturally supports pattern-matching over such constructors as well, through *ad-hoc
polymorphism*, where polymorphic type variables are allowed to be instantiated at *runtime* rather
than at type-checking time. The mechanism through which ad-hoc polymorphism works in λProlog is
simple: before performing unification at the term-level, we perform unification at the type level
first, therefore further determining any uninstantiated type variables. Therefore, when we check to
see whether the current goal matches the premise of a rule, type unification can force us to
distinguish between different types. Based on these, the standard example of `map` for vectors is as
follows:

```makam
vmap : {N} (A -> B -> prop) -> vector N A -> vector N B -> prop.
vmap P vnil vnil.
vmap P (vcons X XS) (vcons Y YS) :- P X Y, vmap P XS YS.
```

The notation `{N}` in the type of `vmap` means that the type argument `N` is ad-hoc/not-parametric.
Non-specified type arguments are parametric by default, so as to match standard practice in
languages like ML and Haskell, and to catch type errors that allowing unqualified ad-hoc
polymorphism would permit. For example, consider the following erroneous definition for `fold`,
where the arguments for `P` in the `cons` case are flipped.

```
foldl : (B -> A -> B -> prop) -> B -> list A -> B -> prop.
foldl P S nil S.
foldl P S (cons HD TL) S'' <- P HD S S', foldl P S' TL S''.
```

If ad-hoc polymorphism is allowed for `A` and `B`, this is a well-typed definition. However, the
erroneous call to `P` forces the types `A` and `B` to be unified, and therefore the `fold` predicate
is unnecessarily restricted to only work when the two types are the same. Having to specify ad-hoc
polymorphism explicitly helps us avoid such mistakes.

Though this support for ad-hoc polymorphism was part of the original λProlog design, we have not
found extensive coverage of its implications in the literature. Furthermore, it is not supported
well by standard implementations of λProlog (like Teyjus), which was one of the reasons that
prompted us to work on Makam.

Armed with GADTs of this form, we can now introduce dependently-typed binding forms, where the
number of variables that are being bound is reflected in the type. One way to do this is through
a type of the form `dbind A N B`, standing for a dependently-typed binding of `N` fresh variables
of type `A`'s into a body of type `B`. `N` will be instantiated with `natZ` and `natS` as above. 

```makam
dbind : type -> type -> type -> type. 

dbindbase : B -> dbind A natZ B.
dbindnext : (A -> dbind A N B) -> dbind A (natS N) B.
```

Another possibility, avoiding the need for introducing type-level natural numbers, is to
use a more standard type as the dependent parameter: the type of tuples that would serve
as substitutions for the introduced variables. The type would then become:
```makam
dbind : type -> type -> type -> type.

dbindbase : B -> dbind A unit B.
dbindnext : (A -> dbind A T B) -> dbind A (A * T) B.
```

The definitions for helper predicates, such as `intromany`, `applymany`, etc. follow the case for
`bindmany` closely, only with more precise types.  We first define a helper type `subst A T` that is
equivalent to the type of tuples `T` we expect. This is not strictly necessary but allows for more
precise types: 

```makam
subst : type -> type -> type.
snil : subst A unit.
scons : A -> subst A T -> subst A (A * T).
```

The predicates are now defined as follows. First, their types are: 

```makam
intromany : {T} dbind A T B -> (subst A T -> prop) -> prop.
applymany : {T} dbind A T B -> subst A T -> B -> prop.
openmany : {T} dbind A T B -> (subst A T -> B -> prop) -> prop.
```

Note that we are reusing the same predicate names as before. Makam allows overloading for all
variable names; expected types are taken into account for resolving variables and disambiguating
between them, as has been long known to be possible in the bi-directional type-checking
literature. Type ascription is used when variable resolution is ambiguous.  We also avoid
overloading for constructors; having unambiguous types for constructors means that they can be used
to resolve ambiguity between overloaded predicates easily. 

```makam
intromany (dbindbase F) P :- P snil.
intromany (dbindnext F) P :-
  (x:A -> intromany (F x) (pfun t => P (scons x t))).

applymany (dbindbase Body) snil Body.
applymany (dbindnext F) (scons X XS) Body :-
  applymany (F X) XS Body.

openmany F P :-
  intromany F (pfun xs => [Body] applymany F xs Body, P xs Body).
```

Also, we define predicates analogous to `map` and `assumemany` for the
`subst` type: 

```makam
assumemany : {T T'} (A -> B -> prop) -> subst A T -> subst B T' -> prop -> prop.
assumemany P snil snil Q :- Q.
assumemany P (scons X XS) (scons Y YS) Q :- (P X Y -> assumemany P XS YS Q).

map : {T T'} (A -> B -> prop) -> subst A T -> subst B T' -> prop.
map P snil snil.
map P (scons X XS) (scons Y YS) :- P X Y, map P XS YS.
```

(Here we have not captured the relationship between the type of tuples `T` and `T'` precisely,
namely that one structurally matches the other with `A`s replaced by `B`s. We could capture that by
adding another argument of a dependent type that captures that relationship, but we will elide this
to avoid needlessly complicating the presentation.)
  
Using this type, we can define `letrec` as follows: 

```makam
letrec : dbind term T (subst term T) -> dbind term T term -> term.
```

This encoding captures the binding structure of the construct precisely: we need the same number of
definitions as the number of variables we introduce, and the body of the construct needs exactly the
same number of variables bound.

The typing rule is entirely similar to the one we had previously:

```makam
typeof (letrec Defs Body) T' :-
  openmany Defs (pfun xs defs =>
    assumemany typeof xs TS (map typeof defs TS)
  ),
  openmany Body (pfun xs body =>
    assumemany typeof xs TS (typeof body T')
  ).
```

We can also use the same 'dependency' trick for other, more complicated forms of binding. One such
example which we sketch below is linear ordered binding as in the case of patterns. The point is
that having explicit support in our metalanguage only for single-variable binding, as is standard in
HOAS, together with the two kinds of polymorphism we have shown, is enough. Using them, we can
encode complicated binding forms, that often require explicit support in other meta-linguistic
settings (e.g. Needle + Knot, Unbound, etc.)

At the top level, a single type argument is needed for patterns, representing the list of variables
that it uses in the order that they are used. Each variable can only be used once, so at the level
of patterns, there is not really a notion of binding: pattern variables are "introduced" at their
point of use. However, the list of variables that we build up can be reused in order to be actually
bound into a term -- e.g. the body of a pattern-matching branch.

(Single-variable binding is really a way to introduce a "point" in an AST where we can "refer back
to" from its children; or the means to introduce sharing in the notion of ASTs, allowing to refer to
the same "thing" a number of times. There's no sharing going on inside patterns though; hence no
binding constructs are needed for encoding the patterns themselves.)

Each sub-pattern that makes up a pattern needs to dependent on two arguments, in order to capture
the linearity -- the fact that variables "go away" after their first use. The first argument
represents all the variables that can be used, and initially matches the type argument of the
top-level pattern; the second argument represents the variables that "remain" to be used after this
sub-pattern is traversed. We use "initially" and "after" to refer to the order of visiting the
sub-patterns in a structural, depth-first traversal of the pattern. The "difference" between the
types corresponds to the variables that each particular sub-pattern uses.

To make the presentation cleaner, we will introduce a single type for patterns that has both
arguments, with the requirement that for top-level arguments, no variables remain.

```makam
patt : type -> type -> type.
```

(Probably hidden: add natural numbers so that we can have a simple example of patterns.)

```makam
nat : typ.
zero : term.
succ : term -> term.
typeof zero nat.
typeof (succ N) nat :- typeof N nat.
eval zero zero.
eval (succ E) (succ V) :- eval E V.
```

The pattern for zero does not use any variables; the pattern `succ P` for successor
uses the same variables that `P` does.
```makam
patt_zero : patt T T.
patt_succ : patt T T' -> patt T T'.
```
A single pattern variable declares/uses exactly itself.
```makam
patt_var : patt (term * T) T.
```
A wildcard pattern does not use any variables.
```makam
patt_wild : patt T T.
```
n-ary tuples require a type for pattern lists:
```makam
pattlist : type -> type -> type.
patt_tuple : pattlist T T' -> patt T T'.

patt_nil : pattlist T T.
patt_cons : patt T1 T2 -> pattlist T2 T3 -> pattlist T1 T3.
```

We can now encode a single-branch "case-or-else" statement as follows:

```makam
case_or_else : term -> patt T unit -> dbind term T term -> term -> term.
```

The first argument is the scrutinee; the second is the pattern; the third is the branch body, where
we bind the same number of variables as the ones used in the pattern, and the last argument is the
`else` case.

The typing relation for patterns is defined as follows: given a pattern and a list of types for the
variables that remain after the pattern, yield a list of types for all the variables that are
available, plus the type of the pattern.

```makam
typeof : {T T' Ttyp T'typ} patt T T' -> subst typ T'typ -> subst typ Ttyp -> typ -> prop.

typeof patt_var S' (scons T S') T.
typeof patt_wild S S T.
typeof patt_zero S S nat.
typeof (patt_succ P) S' S nat :-
  typeof P S' S nat.

typeof_pattlist :
  {T T' Ttyp T'typ} pattlist T T' -> subst typ T'typ -> subst typ Ttyp -> list typ -> prop.

typeof (patt_tuple PS) S' S (product TS) :-
  typeof_pattlist PS S' S TS.

typeof_pattlist patt_nil S S [].
typeof_pattlist (patt_cons P PS) S3 S1 (T :: TS) :-
  typeof_pattlist PS S3 S2 TS, typeof P S2 S1 T.

typeof (case_or_else Scrutinee Pattern Body Else) T' :-
  typeof Scrutinee T,
  typeof Pattern snil TS T,
  openmany Body (pfun xs body =>
     (assumemany typeof xs TS (typeof body T'))
  ),
  typeof Else T'.
```
  
In order to define evaluation rules, we could define a predicate that models unification between
patterns and terms. However, we can do better than that: we can re-use the existing support for
unification from the metalanguage! In that case, all we need is a way to convert a pattern into a
term, with pattern variables replaced by *meta-level metavariables*. The metavariables are
introduced at each conversion rule as needed, and will get instantiated to the right terms if
unification with the scrutinee succeeds.

```makam
patt_to_term : {T T'} patt T T' -> term -> subst term T' -> subst term T -> prop.
patt_to_term patt_var X Subst (scons X Subst).
patt_to_term patt_wild _ Subst Subst.
patt_to_term patt_zero zero Subst Subst.
patt_to_term (patt_succ PN) (succ EN) Subst' Subst :- patt_to_term PN EN Subst' Subst.

pattlist_to_termlist : {T T'} pattlist T T' -> list term -> subst term T' -> subst term T -> prop.

patt_to_term (patt_tuple PS) (tuple ES) Subst' Subst :-
  pattlist_to_termlist PS ES Subst' Subst.

pattlist_to_termlist patt_nil [] Subst Subst.
pattlist_to_termlist (patt_cons P PS) (T :: TS) Subst3 Subst1 <-
  pattlist_to_termlist PS TS Subst3 Subst2,
  patt_to_term P T Subst2 Subst1.

eval (case_or_else Scrutinee Pattern Body Else) V :-
  patt_to_term Pattern TermWithUnifvars snil Unifvars,
  if (eq Scrutinee TermWithUnifvars)  (* reuse unification from the meta-language *)
  then (applymany Body Unifvars Body', eval Body' V)
  else (eval Else V).
```

Two new things here: if-then-else has the semantics described in the LogicT monad paper.
`eq` is a predicate that forces its arguments to be unified, defined simply as:

```makam
eq : A -> A -> prop.
eq X X.
```

Example of pattern matching: predecessor for nats.

```makam
(eq _PRED 
  (lam _ (fun n => 
    case_or_else n
      (patt_succ patt_var) (dbindnext (fun pred => dbindbase pred))
      zero
      )),
 typeof _PRED T,
 eval (app _PRED zero) PRED_OF_ZERO,
 eval (app _PRED (succ (succ zero))) PRED_OF_TWO) ?
>> Yes:
>> T := arrow nat nat
>> PRED_OF_ZERO := zero
>> PRED_OF_TWO := succ zero
```
