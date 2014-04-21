Add LoadPath "..".
Declare ML Module "relation_extraction_plugin".

Inductive n : Set := | Zero : n | Succ : n -> n.
Inductive add : n -> n -> n -> Prop :=
| addZero : forall o, add o Zero o
| addSucc : forall o m p, add o m p -> add o (Succ m) (Succ p).

Extraction Relation Fixpoint (add [2 3]).
Extraction Relation Fixpoint (add [1 2] Struct 2 as "addition").
Extraction Relation Fixpoint (add [1 2] Counter as "add_count").
Definition res0 := Eval compute in (add23 (Succ (Succ Zero)) (Succ (Succ (Succ Zero)))).
Definition res1 := Eval compute in (addition (Succ Zero) (Succ Zero)).
Definition res2 := Eval compute in (add_count (S (S (S (S O)))) (Succ Zero) (Succ Zero)).

Lemma test0: res0 = Some (Succ Zero).
Proof.
auto.
Qed.
Lemma test1: res1 = (Succ (Succ Zero)).
Proof.
auto.
Qed.
Lemma test2: res2 = Some (Succ (Succ Zero)).
Proof.
auto.
Qed.
