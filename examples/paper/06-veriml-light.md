<!--
```makam
%use "05-type-synonyms.md".
%testsuite literate_tests.
```
-->

Let us now add one more meta level: make our object language a meta-language as well!
That is, we will add the ability to our object language to manipulate terms of a different
object language, in a type-safe manner. This is similar, for example, to heterogeneous
meta-programming in MetaHaskell; however, the setting we have in mind is closer to
metalanguages where the object language is a logic, similar to Beluga (where the object
language is LF) and VeriML (where the object language is the $\lambda\text{HOL}$ logic).

We will follow the construction of (cite my dissertation), but using a simpler object
language. We will first define the notion of *dependent objects*. These are objects
that are external to the language that we have seen so far, but we will add a standard
dependently typed subsystem to our language over them. (Similar to the DML construction/
the DML generalization by Licata and Harper.) Dependent objects are classified through
*dependent classifiers*:

```makam
depobject, depclassifier : type.
depclassify : depobject -> depclassifier -> prop.
```

We also have a (perhaps non-trivial) substitution operation for terms containing a
variable of type `depobject`:
```makam
depsubst : [A] (depobject -> A) -> depobject -> A -> prop.
```

(In the simple case this could just be the built-in function application:
```
depsubst F X (F X).
```
We could have something more complicated than that though.)

Now let's add the standards: dependent functions and dependent products:

```makam
lamdep : depclassifier -> (depobject -> term) -> term.
appdep : term -> depobject -> term.
packdep : depobject -> term -> (depobject -> typ) -> term.
unpackdep : term -> (depobject -> term -> term) -> term.

pidep : depclassifier -> (depobject -> typ) -> typ.
sigdep : depclassifier -> (depobject -> typ) -> typ.

typeof (lamdep DC EF) (pidep DC TF) :-
  (x:depobject -> depclassify x DC -> typeof (EF x) (TF x)).

typeof (appdep E DO) T' :-
  typeof E (pidep DC TF),
  depclassify DO DC,
  depsubst TF DO T'.

typeof (packdep DO E TYPF) (sigdep DC TYPF) :-
  depclassify DO DC,
  depsubst TYPF DO T',
  typeof E T'.

typeof (unpackdep E F) T' :-
  typeof E (sigdep DC TYPF),
  (do:depobject -> x:term -> depclassify do DC -> typeof x (TYPF do) ->
   typeof (F do x) T').
```

OK, let's now add a very simple object language -- the simply typed lambda
calculus. Let's go again... or actually, let's just import what we have
already in a separate namespace:

```makam
%import "01-base-language.md" as object.

%extend object.
intconst : int -> term.
intplus : term -> term -> term.

tint : typ.

typeof (intconst _) tint.
typeof (intplus E1 E2) tint :- typeof E1 tint, typeof E2 tint.
%end.
```

(Note: we're just importing the previous literate development into a different
namespace. Unfortunately I can't import the further developments right now,
probably some issue with the importing code, but I think it's fine to skip for now.
We could go with just defining a new language anew though.)

Now let's turn these into dependent objects:

```makam
term : object.term -> depobject.
typ : object.typ -> depobject.

typ : object.typ -> depclassifier.
ext : depclassifier.

depclassify (term E) (typ T) :- object.typeof E T.
```

To classify types, we'll need to make sure they're well-formed. For the time
being, all types are well-formed by construction, but let's prepare for the
future:

```makam
%extend object.
wftype : typ -> prop.
wftype_cases : [A] A -> A -> prop.

wftype T :- wftype_cases T T.
wftype_cases T T :- structural wftype_cases T T.
%end.

depclassify (typ T) ext :- object.wftype T.
```

Let's proceed to substitution:

```makam
depsubst_aux, depsubst_cases : [A] depobject -> depobject -> A -> A -> prop.
depsubst F X Res :- (x:depobject -> depsubst_aux x X (F x) Res).
depsubst_aux Var Replace Where Result :-
  if (depsubst_cases Var Replace Where Result)
  then (success)
  else (structural_recursion (depsubst_aux Var Replace) Where Result).
```

Alright. Now let's see what we can do:

```makam
typeof
  (lamdep ext (fun t =>
  (packdep t (tuple []) (fun _ => product [])))) T ?
```

We can only use the dependent variables as they are, so not much use.
The whole point of this though is being able to refer to dependent variables
within the object terms:

```makam
%extend object.
metaterm : depobject -> term.
metatyp : depobject -> typ.

typeof (metaterm E) T :-
  refl.isnvar E,
  depclassify E (typ T).

wftype_cases (metatyp T) (metatyp T) :-
  refl.isnvar T,
  depclassify T ext.
%end.

depsubst_cases Var (term Replace) (object.metaterm Var) Replace.
depsubst_cases Var (typ Replace) (object.metatyp Var) Replace.
```

OK, now let's see if we can do better:

```makam
typeof
  (lamdep ext (fun t =>
  (packdep
     (term (object.lam (object.metatyp t) (fun x => x)))
     (tuple []) (fun _ => product [])))) T ?
```

We can also handle the case of non-closed terms, using contextual types:
```makam
%extend object.
subst : type -> type.
subst : list A -> subst A.

ctx : type -> type.
ctx : subst typ -> bindmany term A -> ctx A.

openctx : ctx A -> (subst term -> subst typ -> A -> prop) -> prop.
applyctx : ctx A -> subst term -> A -> prop.

openctx (ctx Types Binds) P :-
  openmany Binds (pfun vars body =>
    P (subst vars) Types body
  ).

applyctx (ctx _ Binds) (subst Args) Result :-
  applymany Binds Args Result.

map : (A -> B -> prop) -> subst A -> subst B -> prop.
map P (subst L) (subst L') :- map P L L'.
%end.

openterm : object.ctx object.term -> depobject.
ctxtyp : object.subst object.typ -> object.typ -> depclassifier.

depclassify (openterm CtxE) (ctxtyp Typs T) :-
  object.openctx CtxE (pfun vars typs e => [Units]
    object.map (pfun t u => object.wftype t) typs (Units : object.subst unit),
    object.map eq typs Typs,
    object.typeof e T).
```

And one last step: let's reify open terms back into the language:

```makam
%extend object.
metaterm : depobject -> subst term -> term.

typeof (metaterm E ES) T :-
  refl.isnvar E,
  depclassify E (ctxtyp Typs T),
  object.map object.typeof ES Typs.
%end.

depsubst_cases Var (openterm CtxE) (object.metaterm Var Subst) Result :-
  object.applyctx CtxE Subst E,
  depsubst_aux Var (openterm CtxE) E Result.
```

Let's try the final thing:

```makam
(eq _FUNCTION
  (lamdep ext (fun t1 =>
    (lamdep ext (fun t2 =>
    (lamdep (ctxtyp (object.subst [object.metatyp t1]) (object.metatyp t2)) (fun x_e =>
    (packdep (openterm (object.ctx (object.subst []) (bindbase (object.lam _ (fun x =>
      object.tuple [object.metaterm x_e #SUBST, object.intconst 5]
    ))))) (tuple []) (fun _ => product [])))))))),
 typeof _FUNCTION FUNCTION_TYPE,

 typeof
  (appdep (appdep
    _FUNCTION
    (typ object.tint))
    (typ (object.product [object.tint])))
 APPLIED_TYPE) ?
>> Yes:
>> SUBST := fun t1 t2 x_e x => object.subst (cons x nil),
>> FUNCTION_TYPE :=
    pidep ext (fun t1 =>
    pidep ext (fun t2 =>
    pidep (ctxtyp (object.subst (cons (object.metatyp t1) nil)) (object.metatyp t2))
    (fun x_e =>
      sigdep
        (ctxtyp (object.subst nil)
         (object.arrow
           (object.metatyp t1)
           (object.product (cons (object.metatyp t2) (cons object.tint nil)))))
       (fun _ => product nil)))),
>> APPLIED_TYPE :=
    pidep (ctxtyp
      (object.subst (cons object.tint nil))
      (object.product (cons object.tint nil)))
    (fun x_e =>
      sigdep (ctxtyp
        (object.subst nil)
        (object.arrow
          object.tint
          (object.product (cons (object.product (cons object.tint nil)) (cons object.tint nil)))))
      (fun _ => product nil)).
```

Note that we can infer both the type of the lambda abstraction and the substitution
itself. Getting to that point in the VeriML implementation took months!

Mention that adding polymorphic contexts and dependent pattern matching as in VeriML is
also possible, but we won't show it here.
