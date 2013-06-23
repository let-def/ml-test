Require Export Smallstep.
Require Import Relations.

Inductive tm : Type :=
  | tm_true : tm
  | tm_false : tm
  | tm_if : tm -> tm -> tm -> tm
  | tm_zero : tm
  | tm_succ : tm -> tm
  | tm_pred : tm -> tm
  | tm_iszero : tm -> tm.

Inductive bvalue : tm -> Prop :=
  | bv_true : bvalue tm_true
  | bv_false : bvalue tm_false.

Inductive nvalue : tm -> Prop :=
  | nv_zero : nvalue tm_zero
  | nv_succ : forall t, nvalue t ->
      nvalue (tm_succ t).

Definition value (t : tm) := bvalue t \/ nvalue t.

Hint Constructors bvalue nvalue.
Hint Unfold value.

Reserved Notation "t1 '-->' t2" (at level 40).
Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      (tm_if tm_true t1 t2) --> t1
  | ST_IfFalse : forall t1 t2,
      (tm_if tm_false t1 t2) --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      (tm_if t1 t2 t3) --> (tm_if t1' t2 t3)
  | ST_Succ : forall t1 t1',
      t1 --> t1' ->
      (tm_succ t1) --> (tm_succ t1')
  | ST_PredZero :
      (tm_pred tm_zero) --> tm_zero
  | ST_PredSucc : forall t1,
      nvalue t1 ->
      (tm_pred (tm_succ t1)) --> t1
  | ST_Pred : forall t1 t1',
      t1 --> t1' ->
      (tm_pred t1) --> (tm_pred t1')
  | ST_IszeroZero :
      (tm_iszero tm_zero) --> tm_true
  | ST_IszeroSucc : forall t1,
      nvalue t1 ->
      (tm_iszero (tm_succ t1)) --> tm_false
  | ST_Iszero : forall t1 t1',
      t1 --> t1' ->
      (tm_iszero t1) --> (tm_iszero t1')

where "t1 '-->' t2" := (step t1 t2).

Hint Constructors step.

Notation step_normal_form := (normal_form step).

Definition stuck (t : tm) : Prop :=
  step_normal_form t /\ ~value t.
Hint Unfold stuck.

Example some_tm_is_stuck :
  exists t, stuck t.
Proof.
  exists (tm_if tm_zero tm_zero tm_zero).
  split; intro contra; destruct contra.
  + solve by inversion 2.
  + solve by inversion.
  + solve by inversion.
Qed.


Lemma value_is_nf : forall t,
  value t -> step_normal_form t.
Proof.
  intros.
  intro.
  destruct H0.
  inversion H.
  - inversion H1; subst; inversion H0.
  - clear H.
    generalize dependent x.
    induction H1.
    + intros; solve by inversion 2.
    + intros.
      inversion H0.
      apply IHnvalue with (x:=t1').
      auto.
Qed.

Inductive ty : Type :=
  | ty_bool : ty
  | ty_nat : ty.

Inductive has_type : tm -> ty -> Prop :=
  | T_True :
      has_type tm_true ty_bool
  | T_False :
      has_type tm_false ty_bool
  | T_If : forall t1 t2 t3 T,
      has_type t1 ty_bool ->
      has_type t2 T ->
      has_type t3 T ->
      has_type (tm_if t1 t2 t3) T
  | T_Zero :
      has_type tm_zero ty_nat
  | T_Succ : forall t1,
      has_type t1 ty_nat ->
      has_type (tm_succ t1) ty_nat
  | T_Pred : forall t1,
      has_type t1 ty_nat ->
      has_type (tm_pred t1) ty_nat
  | T_Iszero : forall t1,
      has_type t1 ty_nat ->
      has_type (tm_iszero t1) ty_bool.

Hint Constructors has_type.

Example succ_hastype_nat__hastype_nat : forall t,
  has_type (tm_succ t) ty_nat ->
  has_type t ty_nat.
Proof.
  intros.
  inversion H; subst.
  assumption.
Qed.

Theorem progress : forall t T,
  has_type t T ->
  value t \/ exists t', t --> t'.
Proof with auto.
  intros t T HT.
  induction HT...
  - (* tm_if *)
    right.
    destruct IHHT1.
    + destruct H; destruct H; eauto;
        solve by inversion.
    + destruct H; eauto.
  - (* tm_succ *)
    destruct IHHT; destruct H; eauto.
    + right. solve by inversion 2.
  - right.
    destruct IHHT.
    + destruct H.
      solve by inversion 2.
      destruct H.
      exists tm_zero...
      exists t...
    + destruct H.
      exists (tm_pred x)...
  - right.
    destruct IHHT.
    + destruct H.
      solve by inversion 2.
      destruct H.
      * exists tm_true...
      * exists tm_false...
    + destruct H. exists (tm_iszero x)...
Qed.

Theorem preservation : forall t t' T,
  has_type t T ->
  t --> t' ->
  has_type t' T.
Proof with auto.
  intros.
  generalize dependent t'.
  induction H; try (intros; solve by inversion 1).
  - intros.
    inversion H2; subst...
  - intros.
    inversion H0; subst...
  - intros.
    inversion H0; subst...
    inversion H...
  - intros.
    inversion H0...
Qed.

Theorem preservation' : forall t t' T,
  has_type t T ->
  t --> t' ->
  has_type t' T.
Proof with auto.
  intros.
  generalize dependent T.
  induction H0; intros.
  - inversion H...
  - inversion H...
  - inversion H; subst.
    constructor...
  - inversion H...
  - inversion H...
  - inversion H0; subst.
    inversion H2...
  - inversion H...
  - inversion H...
  - inversion H0...
  - inversion H...
Qed.

