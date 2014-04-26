Add LoadPath "..".
Declare ML Module "relation_extraction_plugin".

Inductive bool : Set :=
  | True : bool
  | False : bool.

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
  | EIf : expr -> expr -> expr -> expr.

Inductive instr : Set :=
  | Boucle : expr -> instr -> instr
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
  | (A, A) => True
  | (B, B) => True
  | (C, C) => True
  | _ => False
end.


Fixpoint modif_env (i : ident) (v : val) (env:envi) : envi :=
  match env with
    | Env i2 v2 env => if eq_id i i2 then Env i v env else
      Env i2 v2 (modif_env i v env)
    | EnvEmpty => Env i v EnvEmpty
  end.

Fixpoint get_var (i : ident) (env:envi) :=
  match env with
    | Env i2 v2 env => if eq_id i i2 then Some v2 else
      get_var i env
    | EnvEmpty => None
  end.

Inductive eval : expr -> envi -> val -> Prop :=
  | evalZero : forall env, eval EZero env VZero
  | evalTrue : forall env, eval ETrue env VTrue
  | evalFalse : forall env, eval EFalse env VFalse
  | evalVar : forall env i v,  (get_var i env) = Some v -> eval (EVar i) env v
  | evalIfZ : forall n v n1 n2 env, eval n env VZero  -> eval n2 env v  -> 
               eval (EIf n n1 n2) env v  
  | evalIfNZ : forall m p v n1 n2 env , eval m env (VSucc p)  -> eval n1 env v -> 
               eval (EIf m n1 n2) env v  
  | evalSucc : forall n v env, eval n env v -> eval (ESucc n) env (VSucc v).

Inductive exec : instr -> envi -> envi -> Prop :=
  | execSkip : forall env, exec Skip env env
  | execAffect : forall env i e v, eval e env v -> exec (Affect i e) env (modif_env i v env)
  | execSequ : forall env env1 env2 i1 i2, exec i1 env env1 -> exec i2 env1 env2 -> exec (Sequ i1 i2) env env2
  | execIfTrue : forall env env1 e i1 i2, eval e env VTrue -> exec i1 env env1 -> exec (If e i1 i2) env env1
  | execIfFalse : forall env env2 e i1 i2, eval e env VFalse -> exec i2 env env2 -> exec (If e i1 i2) env env2
  | execWhileTrue : forall e i env env1 env2, eval e env VTrue -> exec i env env1 -> exec (Boucle e i) env1 env2 -> exec (Boucle e i) env env2
  | execWhileFalse : forall e i env, eval e env VFalse -> exec (Boucle e i) env env.

Extraction Relation (eval [1 2]) (exec [1 2]).
Extraction empty_env.

Inductive type : Set :=
 | TBool : type
 | TInt : type.

Inductive envt : Set :=
  | EnvtEmpty : envt
  | Envt : ident -> type -> envt -> envt.

Definition empty_envt : envt := EnvtEmpty.

Fixpoint get_type_var (i : ident) (env:envt) :=
  match env with
    | Envt i2 v2 env => match eq_id i i2 with
      | True => Some v2
      | False => get_type_var i env end
    | EnvtEmpty => None
  end.


Inductive typecheck : envt -> expr -> type -> Prop :=
  | tc_var : forall env x t, get_type_var x env = Some t ->
             typecheck env (EVar x) t
  | tc_Zero : forall env, typecheck env EZero TInt
  | tc_True : forall env, typecheck env ETrue  TBool
  | tc_False : forall env, typecheck env EFalse  TBool
  | tc_if : forall n v n1 n2 env, typecheck env n TInt  -> 
              typecheck env n2  v  -> typecheck env n1 v ->   typecheck env (EIf n n1 n2)  v  
  | tc_Succ : forall n  env, typecheck env n TInt -> typecheck env (ESucc n)  TInt.

Extraction type.
Extraction envt.
Extraction get_type_var.
Extraction Relation Single (typecheck [1 2]).

