Add LoadPath "..".
Declare ML Module "relation_extraction_plugin".

Inductive n : Set := | Zero : n | Succ : n -> n.

Inductive add : n -> n -> n -> Prop :=
| addZero : forall o, add o Zero o
| addSucc : forall o m p, add o m p -> add o (Succ m) (Succ p).

Extraction Relation (add [1 2]).
Extraction Relation  Relaxed (add [2 3]).
Extraction Relation  (add [1 2 3]).
Extraction Relation  Relaxed (add [3 2]).

Extraction Relation Fixpoint  (add [1 2] Struct 2).
Eval  compute in (add12 (Succ (Succ Zero)) (Succ Zero)).
Eval compute in (add12 (Succ Zero) (Succ (Succ Zero)))

Extraction Relation  Fixpoint  Relaxed (add [2 3]). (* no proof*)
Eval  compute in (add23 (Succ (Succ Zero)) (Succ Zero)).
Eval compute in (add23 (Succ Zero) (Succ (Succ Zero)))

(*Failure: 
Extraction Relation  Fixpoint  Relaxed add [1 2 3].
Extraction Relation    Relaxed add [1  3].
*)

