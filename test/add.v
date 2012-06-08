Add LoadPath "..".
Declare ML Module "relation_extraction_plugin".

Inductive n : Set := | Zero : n | Succ : n -> n.
Inductive add : n -> n -> n -> Prop :=
| addZero : forall o, add o Zero o
| addSucc : forall o m p, add o m p -> add o (Succ m) (Succ p).
Extraction Relation add [1 2].
Extraction Relation Single add [1 2 3].
