---
header-includes:
  <link rel="stylesheet" href="makam-highlight/css/highlight-default.css">
  <link rel="stylesheet" href="makam-highlight/css/highlight-makam.css">
  <script src="makam-highlight/js/highlight.pack.js"></script>
  <script>hljs.initHighlightingOnLoad();</script>
  <script src="livereload-js/dist/livereload.js?host=localhost"></script>
---

<!--
```makam
assume_reset : A -> prop -> prop.
assume_reset T P :- refl.assume_reset T P.
```
-->

# Sorts

We first create the sorts.

The sort of terms of $\vdash_I$:

```makam
iterm : sort. (* M *)
```

The sort of types of $\vdash_I$ :

```makam
itype : sort. (* A *)
```

The sort of terms of $\vdash_J$ (justifications):

```makam
just : sort. (* J *)
```

The sort of types of $\vdash_J$:

```makam
jtype : sort.  (* [[ A ]] *)
```

We are now done with sorts.

Now, `bracket` is a (computational) function from $\textsf{Prop}_0$ to $\textsf{Prop}_J$:

```makam
bracket : itype -> jtype -> prop.
```

# Constructors for terms

Let's now add some term formers:

This is $M = \lambda x.N$:

```makam
lam : (iterm -> iterm) -> iterm.
```

This is $M = N R$:

```makam
app : iterm -> iterm -> iterm.
```

Let's add booleans as an example:
```makam
btrue : iterm.
bfalse : iterm.
ifthenelse : iterm -> iterm -> iterm -> iterm.
```

# Constructors for types

Now let's add type formers:

`arrow A B` is $A \to B$:

```makam
arrow : itype -> itype -> itype.
ibool : itype.
```

# Type system

This is just the base type system, representing the $\vdash_I$ typing judgement:

```makam
vdash_I : iterm -> itype -> prop.
```

Rule for $$
\frac{\Gamma, x : A \vdash_I N : B}
     {\Gamma \vdash_I (\lambda x:A.N) : A \to B}
$$

The rule itself has an explicit introduction of a fresh variable, closer to Harper's PFPL notation:
$$
\frac{\{\xi, x\} \Gamma, x : A \vdash_I N : B}
     {\{\xi\} \Gamma \vdash_I (\lambda x:A.N) : A \to B}
$$

With concrete syntax:
$$
\frac{\{\xi, x\} \Gamma, x : A \vdash_I N : B}
     {\{\xi\} \Gamma \vdash_I \texttt{lam} \; (x.N) : \texttt{arrow} \; A \; B}
$$

```makam
vdash_I (lam (fun x => N x)) (arrow A B) :-
  (x:iterm -> vdash_I x A -> vdash_I (N x) B).
```

The rule for application:

$$
\frac{\Gamma \vdash_I M : A \to B \;\;\;\;\; \Gamma \vdash_I N : A}
     {\Gamma \vdash_I M \; N : B}
$$

With concrete syntax:

$$
\frac{\Gamma \vdash_I M : \texttt{arrow} \; A \; B \;\;\;\;\; \Gamma \vdash_I N : A}
     {\Gamma \vdash_I \texttt{app} \; M \; N : B}
$$

```makam
vdash_I (app M N) B :-
  vdash_I M (arrow A B), vdash_I N A.
```

Rules for booleans:

$$
\frac{\;\;}{\Gamma \vdash_I \texttt{true} : \texttt{bool}}
$$

$$
\frac{\;\;}{\Gamma \vdash_I \texttt{false} : \texttt{bool}}
$$

$$
\frac{\Gamma \vdash_I b : \texttt{bool} \;\;\;\;\;
      \Gamma \vdash_I M : A \;\;\;\;\;
      \Gamma \vdash_I N : A}
     {\Gamma \vdash_I \texttt{if} \; b \; \texttt{then} \; M \; \texttt{else} \; N : A}
$$

```makam
vdash_I btrue ibool.

vdash_I bfalse ibool.

vdash_I (ifthenelse B M N) A :-
  vdash_I B ibool,
  vdash_I M A,
  vdash_I N A.

```

Example:

$\vdash (\lambda z.\texttt{if} \; (\lambda x.x) \; \texttt{true} \; \texttt{then} \; z \; \texttt{else} \; z) \; :? \; T$

```makam
vdash_I (lam (fun z => ifthenelse (app (lam (fun x => x)) btrue) z z)) T ?
```

We get $T := B \to B$ for any $B$.

# Now for justifications

The typing judgement $\vdash_J$:

```makam
vdash_J : just -> jtype -> prop.
```

It's all about the box type:

```makam
box : itype -> itype.
```

And the box type only needs one rule which is both an elimination and an introduction rule:
$$
\frac{\Gamma \vdash_I N_i : \square A_i \;\;\;\;\;
      \vec{x_i : A_i} \vdash_I M : A \;\;\;\;\;
      \vec{s_i : [\![ A_i ]\!]} \vdash_J j : [\![ A ]\!]}
     {\Gamma \vdash_I \texttt{let}_{\square} \; \vec{(x\&s)} = \vec{N} \; \texttt{in} \; (M, j)
      : \square A }
$$

First let's create the binding structure for $\texttt{let}_{\square}$: this is
a sequence of simultaneous bindings of a term variable $x$ and a justification variable $s$. The body of the binding is a pair $(M, j)$:

```makam
boxbind : type -> type.
body    : A -> boxbind A.
bind    : (iterm -> just -> boxbind A) -> boxbind A.
```

Using this, the constructor for $\texttt{let}_{\square}$ is:

```makam
letbox : list iterm -> boxbind (iterm * just) -> iterm.
```

Let's also write the predicate for opening up this binding structure, giving us
a list of fresh variables $\vec{x}$ and $\vec{s}$ as long as the body of the
structure:

```makam
open : boxbind (iterm * just) ->
       (list iterm -> list just -> iterm -> just -> prop) -> prop.

open (body (M, J)) P :- P [] [] M J.

open (bind (fun x s => B' x s)) P :-
  (x:iterm -> s:just ->
    open (B' x s) (pfun xs ss m j => P (x :: xs) (s :: ss) m j)).
```

Now for the typing rule. The main complication is that we need to drop all
assumptions for the $\vdash_I$ judgement when type-checking the term $M$,
replacing them with the $\Gamma' = \vec{x : A}$ context:

```makam
vdash_I_let_box_body : list itype -> itype ->
                       list iterm -> list just ->
                       iterm -> just -> prop.

vdash_I_let_box_body AS A XS SS M J :-
  assume_reset vdash_I (
    assume_many vdash_I XS AS (vdash_I M A)
  ),
  map bracket AS TS,
  bracket A T,
  assume_many vdash_J SS TS (vdash_J J T).

vdash_I (letbox NS F) (box A) :-
  map vdash_I NS BoxedAS,
  map (apply box) AS BoxedAS,
  open F (vdash_I_let_box_body AS A).
```

Adding booleans as a concrete type, to get an example:

```makam
jtrue : just.
jfalse : just.
jbool : jtype.
bracket ibool jbool.
vdash_J jtrue jbool.
vdash_J jfalse jbool.
```

And adding $\lambda x:A.M$, where we explicitly set the type $A$ of the variable $x$:

```makam
lam : itype -> (iterm -> iterm) -> iterm.
vdash_I (lam A F) (arrow A B) :-
  (x:iterm -> vdash_I x A -> vdash_I (F x) B).
```

Now we are ready for the example:

```makam
vdash_I (lam (box ibool) (fun x =>
         letbox [x]
                (bind (fun x' s =>
                  body (x', s))))) T ?

>> Yes:
>> T := arrow (box ibool) (box ibool)
```

But, if we try to reuse $x$, we do not get a well-typed term:

```makam
vdash_I (lam (box ibool) (fun x =>
         letbox [x]
                (bind (fun x' s =>
                  body (x, s))))) T ?

>> Impossible.
```

We now add an arrow type for justifications:

```makam
jarrow : jtype -> jtype -> jtype.
bracket (arrow A1 A2) (jarrow T1 T2) :-
  bracket A1 T1, bracket A2 T2.

japp : just -> just -> just.
vdash_J (japp J1 J2) T2 :-
  vdash_J J1 (jarrow T1 T2), vdash_J J2 T1.
```

Now let's try to type the proof of $\square(A \to B) \to \square A \to \square B$:

```makam
a : itype. ja : jtype. bracket a ja.
b : itype. jb : jtype. bracket b jb.

vdash_I (lam (box (arrow a b)) (fun f =>
        (lam (box a)           (fun x =>
        (letbox [f, x] (bind (fun f' j_f' =>
                       (bind (fun x' j_x' =>
                       (body (app f' x', japp j_f' j_x')))))))))))
        T ?
>> Yes:
>> T := arrow (box (arrow a b)) (arrow (box a) (box b))
```


Some extra stuff:

```
inot : iterm.
vdash_I inot (arrow ibool ibool).
```


```makam
eval : iterm -> iterm -> prop.

value : iterm -> prop.

value (lam F).
value (btrue).
value (bfalse).

eval V V when value V.

eval (app E1 E2) V :-
  eval E1 (lam F),
  eval E2 V2,
  eq (F V2) V.

eval (ifthenelse (btrue) ET EF) V :-
  eval ET V.

eval (ifthenelse (bfalse) ET EF) V :-
  eval EF V.
```
