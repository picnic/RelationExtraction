Add LoadPath "../src".
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
Extraction Relation Fixpoint add [1 3].
Extraction Relation Fixpoint exec [1 2] with eval [1 2].
Extraction Relation Fixpoint even [1].
Extraction Relation Fixpoint even_comp [1].

(* --- Basic proofs --- *)

(* add12 *)
Functional Scheme add12_ind := Induction for add12 Sort Prop.
(*
add 12: 2 branches
(let ...) match p1 with | Zero => let fix_5 := p2 in (match ...) fix_5 : add0
(let ...) match p1 with | Succ fix_6 => let fix_7 := p2 in (match ...) 
  let fix_8 := add12 fix_6 fix_7 in (match ...) Succ fix_8 : addSucc
*)
Lemma add12_correct : forall p1 p2 p3, add12 p1 p2 = p3 -> add p1 p2 p3.
Proof.
intros p1 p2 p3.
intro H.
rewrite <- H.
apply add12_ind.

(* add0 *)
simpl.
intros.
apply add0; assumption.

(* add1 *)
simpl.
intros.
apply addSucc; assumption.

Qed.

(* eval12 *)
Functional Scheme eval12_ind := Induction for eval12 Sort Prop.
(*
evalZero
evalSucc
evalVar
evalTrue
evalFalse
*)
Lemma eval12_correct : forall p1 p2 p3, eval12 p1 p2 = p3 -> eval p1 p2 p3.
Proof.
intros p1 p2 p3.
intro H.
rewrite <- H.
apply eval12_ind; simpl; intros.
apply evalZero; assumption.
apply evalSucc; assumption.
apply evalVar; assumption.
apply evalTrue; assumption.
apply evalFalse; assumption.
Qed.

(* even_comp1 *)
Functional Scheme even_comp1_ind := Induction for even_comp1 Sort Prop.
(*
even_compZ
even_compO
even_compN
*)
Lemma even_comp1_correct : forall p1 p2, even_comp1 p1 = p2 -> even_comp p1 p2.
Proof.
intros p1 p2.
intro H.
rewrite <- H.
apply even_comp1_ind; simpl; intros.
apply even_compZ; assumption.
apply even_compO; assumption.
apply even_compN; assumption.
Qed.

(* --- Full mode proofs --- *)

(* even_full *)
(*Lemma even_full_correct : forall n, even_full n = true -> even n.*)
(*Lemma even_full_complete : forall n, even n -> even_full n = true.*)

(* --- Completed functions proofs --- *)

(* add13 *)
Functional Scheme add13_ind := Induction for add13 Sort Prop.
(*Lemma add13_correct : forall p1 p2 p3, add13 p1 p2 = Some p3 -> add p1 p2 p3.
Proof.
intros p1 p2 p3.*)

(* exec12 *)
(*Lemma exec12_correct : forall p1 p2 p3, exec12 p1 p2 = Some p3 -> exec p1 p2 p3.*)


