Add LoadPath "..".
Declare ML Module "relation_extraction_plugin".

(* This file must be used with:
   branch: opt_proofs
   commit: eb6f88e95029c3ce8a1f291a20989e14482cdb7d
*)

Inductive n := N0 | N2 : nat -> nat -> n.


Inductive add : nat -> nat -> nat -> Prop :=
| addz : forall o, add O o o
| addn : forall o m p, add m o p -> add (S m) o (S p).

Inductive sub : nat -> nat -> nat -> Prop :=
| subz : forall o, sub O o o
| subn : forall o m p, sub m p o -> sub (S m) (S p) o.

Inductive nat_prod := P : nat -> nat -> nat_prod.
Inductive pc : nat -> nat -> nat_prod -> Prop :=
| pc0 : forall a b c d e f, add c d f -> pc a c (P d e) -> pc a b (P c O) -> pc (S a) b (P f e)
| pc1 : forall a b c d e f g, sub c e g -> pc a (plus d b) (P e f) -> pc a c (P O d) -> pc a b (P c O) -> pc (S a) b (P c g)
| pc2 : forall a, pc O a (P O O).

Extraction Relation Fixpoint Relaxed pc [1 2] with add [1 2] sub [1 2].
Print pc12.

(*Lemma add12_correct : forall p1 p2 p3, add12 p1 p2 = p3 -> add p1 p2 p3.*)
Lemma sub12_correct : forall p1 p2 p3, sub12 p1 p2 = Some p3 -> sub p1 p2 p3.
Proof.
Admitted.

Lemma pc12_correct : forall p_1 p_2 p_3, pc12 p_1 p_2 = Some p_3 -> pc p_1 p_2 p_3.
Proof.
intros p_1 p_2.
(*intros until 0.*)
apply pc12_ind.

(**** pc2 ****)
intros.
(*CaseConstr (p1{O|S}, O, (), )*)
replace p1 with 0.
(*LetVar (fix_29, p2{O|S}, )*)
assert (fix_29 = p2).
auto.
replace fix_29 with p2.
(*OutputTerm (Some(P(O{O|S}, O{O|S}){P}){Some|None})*)
(* we have to use H : find the right term and subst with the left one *)
injection H.
intro H'.
replace p_3 with (P 0 0).
apply pc2.


(**** pc1 ****)
intros.
(*CaseConstr (p1{O|S}, S, (fix_30), )*)
replace p1 with (S fix_30).
(*LetVar (fix_31, p2{O|S}, )*)
assert (fix_31 = p2).
auto.
replace fix_31 with p2.
(*CaseConstr (pc12 (fix_30{O|S}) (fix_31{O|S}){Some|None}, Some, (fix_32), Pm_3)*)
(* result from a partial function *) (* NEW *)
replace (pc12 fix_30 fix_31) with (Some fix_32).
(*CaseConstr (fix_32{P}, P, (fix_34, fix_33), Pm_3)*)
replace (fix_32) with (P fix_34 fix_33).
(*CaseConstr (fix_33{O|S}, O, (), Pm_3)*)
replace (fix_33) with (0).
(*CaseConstr (pc12 (fix_30{O|S}) (fix_34{O|S}){Some|None}, Some, (fix_35), Pm_4)*)
(* result from a partial function *) (* NEW *)
replace (pc12 fix_30 fix_34) with (Some fix_35).
(*CaseConstr (fix_35{P}, P, (fix_37, fix_36), Pm_4)*)
replace (fix_35) with (P fix_37 fix_36).
(*CaseConstr (fix_37{O|S}, O, (), Pm_4)*)
replace (fix_37) with (0).
(*CaseConstr (pc12 (fix_30{O|S}) (plus (fix_36{%notype%}) (fix_31{%notype%}){O|S}){Some|None}, Some, (fix_38), Pm_5)*)
(* result from a partial function *) (* NEW *)
replace (pc12 fix_30 (fix_36 + fix_31)) with (Some fix_38).
(*CaseConstr (fix_38{P}, P, (fix_40, fix_39), Pm_5)*)
replace (fix_38) with (P fix_40 _x).
(*CaseConstr (sub13 (fix_34{O|S}) (fix_40{O|S}){Some|None}, Some, (fix_41), Pm_6)*)
(* result from a partial function *) (* NEW *)
replace (sub12 fix_34 fix_40) with (Some fix_41).
(* manual automatic renamings... Already done in the first prover *)
(* H *)
replace fix_31 with p2 in H.
replace (pc12 fix_30 p2) with (Some fix_32) in H.
replace fix_32 with (P fix_34 fix_33) in H.
replace fix_33 with 0 in H.
(* H0 *)
replace fix_35 with (P fix_37 fix_36) in e3.
replace fix_37 with 0 in e3.
replace (pc12 fix_30 fix_34) with (Some (P 0 fix_36)) in H0.
(* H1 *)
replace fix_31 with p2 in H1.
replace fix_31 with p2 in e6.
replace fix_38 with (P fix_40 _x) in e6.
replace (pc12 fix_30 (fix_36 + p2)) with (Some (P fix_40 _x)) in H1.
(* e8 (nothing) *)

(* new tactics to deal with Some *)
(* H: Some (P fix_34 0) = Some p_3 -> pc fix_30 p2 p_3 *)
specialize (H (P fix_34 0)).
assert (H' : pc fix_30 p2 (P fix_34 0)).
auto.

(* H0: Some (P 0 fix_36) = Some p_3 -> pc fix_30 fix_34 p_3 *)
specialize (H0 (P 0 fix_36)).
assert (H0' : pc fix_30 fix_34 (P 0 fix_36)).
auto.

(* H1: Some (P fix_40 _x) = Some p_3 -> pc fix_30 (fix_36 + p2) p_3 *)
specialize (H1 (P fix_40 _x)).
assert (H1' : pc fix_30 (fix_36 + p2) (P fix_40 _x)).
auto.

(* for conclusion: use the last hyp (here H2) *)
injection H2.
intro H2'.
replace p_3 with (P fix_34 fix_41).

(* e8: induction hyp of an other partial predicate *)
apply sub12_correct in e8.

(* induction Pm_3 H, Pm_4 H0, Pm_5 H1 *) (* NEW *)
revert e8 H1' H0' H'.
apply pc1.
(*OutputTerm (Some(P(fix_34{O|S}, fix_41{O|S}){P}){Some|None})*)

(**** %default% ****)
(*CaseDum (p1{O|S}, S, (fix_30))*)
(*LetDum (fix_31, p2{O|S})*)
(*CaseDum (pc12 (fix_30{O|S}) (fix_31{O|S}){Some|None}, Some, (fix_32))*)
(*CaseDum (fix_32{P}, P, (fix_34, fix_33))*)
(*CaseDum (fix_33{O|S}, O, ())*)
(*CaseDum (pc12 (fix_30{O|S}) (fix_34{O|S}){Some|None}, Some, (fix_35))*)
(*CaseDum (fix_35{P}, P, (fix_37, fix_36))*)
(*CaseDum (fix_37{O|S}, O, ())*)
(*CaseDum (pc12 (fix_30{O|S}) (plus (fix_36{%notype%}) (fix_31{%notype%}){O|S}){Some|None}, Some, (fix_38))*)
(*CaseDum (fix_38{P}, P, (fix_40, fix_39))*)
(*CaseDum (sub13 (fix_34{O|S}) (fix_40{O|S}){Some|None}, None, ())*)
(*OutputTerm (None)*)

(**** %default% ****)
(*CaseDum (p1{O|S}, S, (fix_30)) -> LetDum (fix_31, p2{O|S})*)
(*CaseDum (pc12 (fix_30{O|S}) (fix_31{O|S}){Some|None}, Some, (fix_32))*)
(*CaseDum (fix_32{P}, P, (fix_34, fix_33))*)
(*CaseDum (fix_33{O|S}, O, ())*)
(*CaseDum (pc12 (fix_30{O|S}) (fix_34{O|S}){Some|None}, Some, (fix_35))*)
(*CaseDum (fix_35{P}, P, (fix_37, fix_36))*)
(*CaseDum (fix_37{O|S}, O, ())*)
(*CaseDum (pc12 (fix_30{O|S}) (plus (fix_36{%notype%}) (fix_31{%notype%}){O|S}){Some|None}, None, ())*)
(*OutputTerm (None)*)

(**** pc0 ****)
(*CaseConstr (p1{O|S}, S, (fix_30), )*)
(*LetVar (fix_31, p2{O|S}, )*)
(*CaseConstr (pc12 (fix_30{O|S}) (fix_31{O|S}){Some|None}, Some, (fix_32), Pm_7)*)
(*CaseConstr (fix_32{P}, P, (fix_34, fix_33), Pm_7)*)
(*CaseConstr (fix_33{O|S}, O, (), Pm_7)*)
(*CaseConstr (pc12 (fix_30{O|S}) (fix_34{O|S}){Some|None}, Some, (fix_35), Pm_8)*)
(*CaseConstr (fix_35{P}, P, (fix_37, fix_36), Pm_8)*)
(*CaseDum (fix_37{O|S}, S, (fix_42))*)
(*LetVar (fix_43, add12 (fix_34{O|S}) (fix_37{O|S}){O|S}, Pm_9)*)
(*OutputTerm (Some(P(fix_43{O|S}, fix_36{O|S}){P}){Some|None})*)

(**** %default% ****)
(*CaseDum (p1{O|S}, S, (fix_30))*)
(*LetDum (fix_31, p2{O|S})*)
(*CaseDum (pc12 (fix_30{O|S}) (fix_31{O|S}){Some|None}, Some, (fix_32))*)
(*CaseDum (fix_32{P}, P, (fix_34, fix_33))*)
(*CaseDum (fix_33{O|S}, O, ())*)
(*CaseDum (pc12 (fix_30{O|S}) (fix_34{O|S}){Some|None}, None, ()) *)
(*OutputTerm (None)*)

(**** %default% ****)
(*CaseDum (p1{O|S}, S, (fix_30))*)
(*LetDum (fix_31, p2{O|S})*)
(*CaseDum (pc12 (fix_30{O|S}) (fix_31{O|S}){Some|None}, Some, (fix_32))*)
(*CaseDum (fix_32{P}, P, (fix_34, fix_33))*)
(*CaseDum (fix_33{O|S}, S, (fix_44))*)
(*OutputTerm (None)*)

(**** %default% ****)
(*CaseDum (p1{O|S}, S, (fix_30))*)
(*LetDum (fix_31, p2{O|S})*)
(*CaseDum (pc12 (fix_30{O|S}) (fix_31{O|S}){Some|None}, None, ())*)
(*OutputTerm (None)*)

