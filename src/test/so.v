Add LoadPath "..".
Declare ML Module "relation_extraction_plugin".

Inductive i : Set := | A | B | C | D.

Inductive test : i -> i -> i -> Prop :=
| c2 : forall v, test A v B
| c4 : forall v, test B v D
| c3 : test B C A
| c1 : test A B C
.
Extraction Relation Relaxed test [1 2].



