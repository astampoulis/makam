```makam
%use "04-ml-subset".
```

Let's add type synonyms now:

```makam
type_synonym : dbind typ T typ -> (typeconstructor T -> program) -> program.

type_synonym_info : typeconstructor T -> dbind typ T typ -> prop.

wfprogram (type_synonym Syn Program') :-
  (t:(typeconstructor T) ->
   type_synonym_info t Syn ->
   wfprogram (Program' t)).

teq : typ -> typ -> prop.
teq (arrow T1 T2) (arrow T1' T2') :- map teq [T1, T2] [T1', T2'].
teq (product TS) (product TS') :- map teq TS TS'.
teq (arrowmany TS T) (arrowmany TS' T') :- teq T T', map teq TS TS'.
teq nat nat.
teq (forall T) (forall T') :- (x:typ -> teq x x -> teq (T x) (T' x)).
teq (tconstr TC Args) (tconstr TC Args') :- map teq Args Args'.
teq (tconstr TC Args) T' :-
  type_synonym_info TC Syn,
  applymany Syn Args T,
  teq T T'.
teq T' (tconstr TC Args) :-
  type_synonym_info TC Syn,
  applymany Syn Args T,
  teq T' T.

(typeof E T) when not(refl.isunif T), once(typeof E T') :-
  teq T T'.
(typeof P S' S T) when not(refl.isunif T), once(typeof P S' S T') :-
  teq T T'.
  
ascribe : term -> typ -> term.
typeof (ascribe E T) T :- typeof E T.
  
wfprogram (
  (type_synonym (dbindnext (fun a => dbindbase (product [a, a])))
  (fun bintuple => 
  
  main (lam (tconstr bintuple [product [nat, nat]])
            (fun x => 
    case_or_else x
    (patt_tuple [patt_tuple [patt_wild, patt_wild], patt_tuple [patt_wild, patt_wild]])
    (dbindbase (tuple []))
    (tuple [])
  ))
))) ?
```
