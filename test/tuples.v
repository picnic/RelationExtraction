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
  | EFalse : expr
  | EInc : ident -> expr
  | If : expr -> expr -> expr -> expr
.

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

Inductive eval : expr -> envi -> val -> envi -> Prop :=
  | evalZero : forall env, eval EZero env VZero env
  | evalTrue : forall env, eval ETrue env VTrue env
  | evalFalse : forall env, eval EFalse env VFalse env
  | evalVar : forall env v, eval (EVar v) env (get_var v env) env
  | evalSucc : forall n v env env', eval n env v env' -> eval (ESucc n) env (VSucc v) env'
  | evalIfZ : forall n v n1 n2 env env' env2, eval n env VZero env' -> eval n2 env' v env2 -> 
               eval (If n n1 n2) env v env2 
  | evalIfNZ : forall m p v n1 n2 env env' env1, eval m env (VSucc p) env' -> eval n1 env' v env1 -> 
               eval (If m n1 n2) env v env1 
  | evalInc : forall v env, eval (EInc v) env (get_var v env) (modif_env v (VSucc (get_var v env)) env).

(*Extraction bool.
Extraction ident.
Extraction expr.
Extraction instr.
Extraction val.
Extraction envi.
Extraction eq_id.
Extraction empty_env.
Extraction modif_env.
Extraction get_var.*)

Extraction Relation eval [1 2].
