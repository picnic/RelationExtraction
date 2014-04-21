Add LoadPath "..".
Declare ML Module "relation_extraction_plugin".

Inductive n := N0 | N2 : nat -> nat -> n.


Inductive add : nat -> nat -> nat -> Prop :=
| addZ : forall o, add O o o
| addN : forall o m p, add m o p -> add (S m) o (S p).

Inductive nat_prod := P : nat -> nat -> nat_prod.
Inductive pc : nat -> nat -> nat_prod -> Prop :=
| pc0 : forall a b c d e f, add c d f -> pc a c (P d e) -> pc a b (P c O) -> pc (S a) b (P f e)
| pc1 : forall a b c d e f, pc a (plus d b) (P e f) -> pc a c (P O d) -> pc a b (P c O) -> pc (S a) b (P c e)
| pc2 : forall a b c, pc a (S b) c -> pc a b (P (S (S O)) O) -> pc (S a) b c
| pc3 : forall a b c d, pc a b (P c d) -> pc (S a) b (P d c)
| pc4 : forall a, pc O a (P O O).

Extraction Relation Fixpoint Relaxed (pc [1 2]) (add [1 2]).

Lemma pc12_check : forall (p1 p2 : nat) (po : nat_prod), pc12 p1 p2 = po -> pc p1 p2 po.
Proof.
apply pc12_correct.
Qed.
