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
  | Boucle : expr -> instr -> instr
  | Skip : instr
  | Sequ : instr -> instr -> instr
  | Affect : ident -> expr -> instr
  | If : expr -> instr -> instr -> instr
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

Inductive eval : expr -> envi -> val -> Prop :=
  | evalZero : forall env, eval EZero env VZero
  | evalTrue : forall env, eval ETrue env VTrue
  | evalFalse : forall env, eval EFalse env VFalse
  | evalVar : forall env v, eval (EVar v) env (get_var v env)
  | evalSucc : forall n v env, eval n env v -> eval (ESucc n) env (VSucc v).

Inductive exec : instr -> envi -> envi -> Prop :=
  | execSkip : forall env, exec Skip env env
  | execAffect : forall env i e v, eval e env v -> exec (Affect i e) env (modif_env i v env)
  | execSequ : forall env env1 env2 i1 i2, exec i1 env env1 -> exec i2 env1 env2 -> exec (Sequ i1 i2) env env2
  | execIfTrue : forall env env1 e i1 i2, eval e env VTrue -> exec i1 env env1 -> exec (If e i1 i2) env env1
  | execIfFalse : forall env env2 e i1 i2, eval e env VFalse -> exec i2 env env2 -> exec (If e i1 i2) env env2
  | execWhileTrue : forall e i env env1 env2, eval e env VTrue -> exec i env env1 -> exec (Boucle e i) env1 env2 -> exec (Boucle e i) env env2
  | execWhileFalse : forall e i env, eval e env VFalse -> exec (Boucle e i) env env.

Extraction Relation eval [1 2] with exec [1 2].
Extraction empty_env.

Inductive type : Set :=
 | TBool : type
 | TInt : type
 | TError : type.

Fixpoint get_type (g:envi) (e:expr) := match e with
  | EVar var => match get_var var g with
    | VZero => Some TInt
    | VSucc _ => Some TInt
    | VTrue => Some TBool
    | _ => None
   end
  | _ => None
end.

Inductive typecheck : envi -> expr -> type -> Prop :=
| c_varerror : forall g x, get_type g (EVar x) = None ->
          typecheck g (EVar x) TError
| c_var : forall g x t, get_type g (EVar x) = Some t ->
          typecheck g (EVar x) t.

Extraction option.
Extraction type.
Extraction get_type.
Extraction Relation Single typecheck [1 2].


