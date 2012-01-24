Add LoadPath "..".
Declare ML Module "relation_extraction_plugin".


Inductive ident : Set :=
  | A : ident
  | B : ident
  | C : ident.

Inductive expr : Set :=
  | EZero : expr
  | ESucc : expr -> expr
  | EVar : ident -> expr
  | ETrue : expr
  | EFalse : expr.

Inductive instr : Set :=
  | Skip : instr
  | Sequ : instr -> instr -> instr
  | Affect : ident -> expr -> instr
  | If : expr -> instr -> instr -> instr.

Inductive val : Set :=
  | VTrue : val
  | VFalse : val
  | VZero : val
  | VSucc : val -> val.

Inductive envi : Set :=
  | EnvEmpty : envi
  | Env : ident -> val -> envi -> envi.

Definition empty_env : envi := EnvEmpty.

Definition eq_id i1 i2 := match (i1, i2) with
  | (A, A) => true
  | (B, B) => true
  | (C, C) => true
  | _ => false
end.


Fixpoint modif_env (i : ident) (v : val) (env:envi) : envi :=
  match env with
    | Env i2 v2 env => if eq_id i i2 then Env i v env else
      Env i2 v2 (modif_env i v env)
    | EnvEmpty => Env i v EnvEmpty
  end.

Fixpoint get_var (i : ident) (env:envi) :=
  match env with
    | Env i2 v2 env => if eq_id i i2 then v2 else
      get_var i env
    | EnvEmpty => VFalse
  end.

Inductive eval : expr -> envi -> val -> Prop :=
  | evalZero : forall env, eval EZero env VZero
  | evalTrue : forall env, eval ETrue env VTrue
  | evalFalse : forall env, eval EFalse env VFalse
  | evalVar : forall env v, eval (EVar v) env (get_var v env)
  | evalSucc : forall n v env, eval n env v -> eval (ESucc n) env (VSucc v).

Inductive exec : instr -> envi -> envi -> Prop :=
  | execSkip : forall env, exec Skip env env
  | execAffect : forall env i e v, eval e env v -> 
                 exec (Affect i e) env (modif_env i v env)
  | execSequ : forall env env1 env2 i1 i2, exec i1 env env1 -> 
               exec i2 env1 env2 -> exec (Sequ i1 i2) env env2
  | execIfTrue : forall env env1 e i1 i2, eval e env VTrue -> 
                 exec i1 env env1 -> exec (If e i1 i2) env env1
  | execIfFalse : forall env env2 e i1 i2, eval e env VFalse -> 
                  exec i2 env env2 -> exec (If e i1 i2) env env2.

Inductive even : nat -> Prop :=
| evenZ: even O
| evenN: forall n, even n -> even (S (S n)).

Inductive even_comp : nat -> bool -> Prop :=
| even_compZ: even_comp 0 true
| even_compO: even_comp 1 false
| even_compN: forall n v, even_comp n v -> even_comp (S (S n)) v.

Inductive n : Set := | Zero : n | Succ : n -> n.
Inductive add : n -> n -> n -> Prop :=
| add0 : forall o, add Zero o o
| addSucc : forall o m p, add m o p -> add (Succ m) o (Succ p).

Section List_predicates.

Variable A : Type.

Inductive list_len : list A -> nat -> Prop :=
| len_nil : list_len nil 0
| len_cons : forall e n tl, list_len tl n -> list_len (e::tl) (n+1).

End List_predicates.

Extraction Relation Fixpoint add [1 2].
Print add12.
Extraction Relation Fixpoint add [1 3].
Print add13.

Extraction Relation Fixpoint exec [1 2] with eval [1 2].
Print eval12.
Print exec12.

Extraction Relation Fixpoint even [1].
Print even_full.
Extraction Relation Fixpoint even_comp [1].
Print even_comp1.
(* TODO: Inductives with parameters
Extraction Relation Fixpoint list_len [1].
Print list_len1.
Extraction Relation Fixpoint list_len [1 2].
Print list_len_full.
*)


