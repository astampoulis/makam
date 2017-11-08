---
header-includes:
  <link rel="stylesheet" href="makam-highlight/css/highlight-default.css">
  <link rel="stylesheet" href="makam-highlight/css/highlight-makam.css">
  <script src="makam-highlight/js/highlight.pack.js"></script>
  <script>hljs.initHighlightingOnLoad();</script>
  <script src="livereload-js/dist/livereload.js?host=localhost"></script>
---

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
etype : sort.  (* [[ A ]] *)
```

We are now done with sorts.

Now, `bracket` is a (computational) function from $\textsf{Prop}_0$ to $\textsf{Prop}_J$:

```makam
bracket : itype => etype.
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
vdash_I : iterm => itype.
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
vdash_J : just => etype.
```

The term former $M \& j$:

```makam
ampersand : iterm -> just -> iterm.
```

Its type is:

```makam
box : itype -> itype.
```

The typing rule is:
$$
\frac{\Gamma \vdash_I M : A \;\;\;\;\; [\![ A ]\!] = T \;\;\;\;\; \Gamma \vdash_J j : T}
     {\Gamma \vdash_I M \& j : \square{A}}
$$

The rule is written as:

```makam
vdash_I (ampersand M J) (box A) :-
  vdash_I M A,
  bracket A T,
  vdash_J J T.
```

```makam
letbox : iterm -> (bindone just (bindone iterm iterm)) -> iterm.

vdash_I (letbox M F) B :-
  vdash_I M (box A),
  bracket A T,
  bindone.open F (fun s f' =>
    bindone.open f' (fun x m' => {prop|
      (vdash_J s T ->
       vdash_I x A ->
       vdash_I m' B) |})).

jtrue : just.
ebool : etype.
bracket ibool ebool.
vdash_J jtrue ebool.
vdash_I (ampersand btrue jtrue) T ?

jnot : just.
earrow : etype -> etype -> etype.
bracket (arrow A1 A2) (earrow T1 T2) :-
  bracket A1 T1,
  bracket A2 T2.
vdash_J jnot (earrow ebool ebool).

japp : just -> just -> just.
vdash_J (japp J1 J2) T2 :-
  vdash_J J1 (earrow T1 T2),
  vdash_J J2 T1.

inot : iterm.
vdash_I inot (arrow ibool ibool).

vdash_I (ampersand inot jnot) T?

vdash_I (letbox (ampersand btrue jtrue)
          (bindone _ (fun s =>
          (bindone _ (fun x =>
          ampersand (app inot x) (japp jnot s)))))) T ?

itermbig : type.
itypebig : type.
jambdas : bindmany just iterm -> itermbig.
jarrows : list etype -> itype -> itypebig.

typeofbig : itermbig -> itypebig -> prop.

typeofbig (jambdas F) (jarrows TS A) :-
  bindmany.open F (fun xs body => {prop|
    assume_many vdash_J xs TS
      (vdash_I body A) |}).

japp : itermbig -> list just -> iterm.
vdash_I (japp E JS) A :-
  typeofbig E (jarrows TS A),
  map vdash_J JS TS.


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

eval (ampersand M J) (ampersand V J) :-
  eval M V.

eval (letbox M F) V :-
  eval M (ampersand M' J),
  bindone.apply F J PreBody,
  bindone.apply PreBody M' Body,
  eval Body V.

eval (japp (jambdas F) JS) V :-
  bindmany.apply F JS Body,
  eval Body V.

lamt : itype -> bindone iterm iterm -> iterm.
vdash_I (lamt A F) (arrow A B) :-
  bindone.open F (fun x body => {prop|
    (vdash_I x A ->
     vdash_I body B) |}).

(bracket A TA ->
vdash_I (lamt (box A) (bindone _ (fun x =>
        letbox x (bindone _ (fun s =>
                 (bindone _ (fun x' =>
                 x'))))))) T) ?


(* alternative to ampersand + letbox *)
letallobox : list iterm -> bindmany just (bindmany iterm (iterm * just)) -> iterm.

vdash_I (letallobox ES F) (box A) :-
  map (apply box) AS TS,
  map vdash_I ES TS,
  map bracket AS JTS,
  bindmany.open F (fun js prebody =>
    bindmany.open prebody (fun xs body =>
      assume_many vdash_J js JTS (
        assume_many vdash_I xs AS {prop| [M J]
          eq body (M, J),
          vdash_I M A,
          bracket A T,
          vdash_J J T
  |}))).
```

```makam
vdash_I (lamt (box ibool) (bindone _ (fun x =>
        letallobox [x] (bindnext _ (fun s  => bindend (
                       (bindnext _ (fun x' => bindend (
                       (x', s)))))))))) T ?
```
