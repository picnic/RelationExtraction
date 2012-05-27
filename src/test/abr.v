Add LoadPath "..".
Declare ML Module "relation_extraction_plugin".

Inductive abr : Set := Empty : abr | Node : abr -> nat -> abr -> abr.
Inductive comp_nat : Set := Inf | Sup | Eq.

Inductive compare : nat -> nat -> comp_nat -> Prop :=
| compare_true : compare 0 0 Eq
| compare_inf : forall n, compare 0 (S n) Inf
| compare_sup : forall n, compare (S n) 0 Sup
| compare_rec : forall n m c, compare n m c -> compare (S n) (S m) c.

Inductive search : abr -> nat -> bool -> Prop :=
| searchempty : forall n, search Empty n false
| searchfound : forall n m t1 t2, compare n m Eq -> search (Node t1 m t2) n true
| searchinf : forall n m t1 t2 b, search t1 n b -> compare n m Inf -> search (Node t1 m t2) n b
| searchsup : forall n m t1 t2 b, search t2 n b -> compare n m Sup -> search (Node t1 m t2) n b.

Extraction Relation Fixpoint Relaxed search [1 2] with compare [1 2].
Print compare12.
Print search12.
Check compare12_correct.
Check search12_correct.

