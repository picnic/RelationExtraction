Add LoadPath "..".
Declare ML Module "relation_extraction_plugin".

Inductive n := N0 | N2 : nat -> nat -> n.


Inductive add : nat -> nat -> nat -> Prop :=
| addz : forall o, add O o o
| addn : forall o m p, add m o p -> add (S m) o (S p).

Inductive sub : nat -> nat -> nat -> Prop :=
| subz : forall o, sub O o o
| subn : forall o m p, sub m o p -> sub (S m) o (S p).

Inductive nat_prod := P : nat -> nat -> nat_prod.
Inductive pc : nat -> nat -> nat_prod -> Prop :=
| pc0 : forall a b c d e f, add c d f -> pc a c (P d e) -> pc a b (P c O) -> pc (S a) b (P f e)
| pc1 : forall a b c d e f g, sub c g e -> pc a (plus d b) (P e f) -> pc a c (P O d) -> pc a b (P c O) -> pc (S a) b (P c g)
| pc2 : forall a, pc O a (P O O).

Extraction Relation Fixpoint Relaxed pc [1 2] with add [1 2] sub [1 3].
Print pc12.

(*
Lemma pc12_correct : forall p1 p2 p3, pc12 p1 p2 = Some p3 -> pc p1 p2 p3.
Proof.
*)


