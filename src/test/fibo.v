Add LoadPath "..".
Declare ML Module "relation_extraction_plugin".

Inductive fibo : nat -> nat -> Prop :=
| cgen : forall a n r1 r2, fibo n r1 -> fibo (S n) r2 ->
         a = S (S n) -> fibo a (plus r1 r2)
| cbase : forall a, (a = O) \/ (a = S O) -> fibo a (S O).
Extraction Relation fibo [1].
