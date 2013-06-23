Require Export Imp.
Require Import Relations.

Inductive tm : Type :=
  | tm_const : nat -> tm
  | tm_plus : tm -> tm -> tm.

Module SimpleArith0.

Fixpoint eval (t : tm) : nat :=
  match t with
  | tm_const n => n
  | tm_plus a1 a2 => plus (eval a1) (eval a2)
  end.

Notation " t '==>' n " := (eval t = n) (at level 40).

End SimpleArith0.

Module SimpleArith1.

Reserved Notation " t '==>' n " (at level 40).
Inductive eval : tm -> nat -> Prop :=
  | E_Const : forall n,
      tm_const n ==> n
  | E_Plus : forall t1 t2 n1 n2,
      t1 ==> n1 ->
      t2 ==> n2 ->
      tm_plus t1 t2 ==> plus n1 n2
  where " t '==>' n " := (eval t n).

End SimpleArith1.

Reserved Notation " t '==>' t' " (at level 40).
Inductive eval : tm -> tm -> Prop :=
  | E_Const : forall n1, tm_const n1 ==> tm_const n1
  | E_Plus  : forall t1 n1 t2 n2,
      t1 ==> tm_const n1 ->
      t2 ==> tm_const n2 ->
      tm_plus t1 t2 ==> tm_const (n1 + n2)
  where " t '==>' t' " := (eval t t').

Module SimpleArith2.

Reserved Notation " t '-->' t' " (at level 40).
Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
      tm_plus (tm_const n1) (tm_const n2) -->
      tm_const (plus n1 n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      tm_plus t1 t2 --> tm_plus t1' t2
  | ST_Plus2 : forall n1 t2 t2',
      t2 --> t2' ->
      tm_plus (tm_const n1) t2 -->
      tm_plus (tm_const n1) t2'
  where " t '-->' t' " := (step t t').

Example test_step_1 :
      tm_plus
        (tm_plus (tm_const 0) (tm_const 3))
        (tm_plus (tm_const 2) (tm_const 4))
      -->
      tm_plus
        (tm_const (plus 0 3))
        (tm_plus (tm_const 2) (tm_const 4)).
Proof.
  repeat constructor.
Qed.


Example test_step_2 :
      tm_plus
        (tm_const 0)
        (tm_plus
          (tm_const 2)
          (tm_plus (tm_const 0) (tm_const 3)))
      -->
      tm_plus
        (tm_const 0)
        (tm_plus
          (tm_const 2)
          (tm_const (plus 0 3))).
Proof.
  repeat constructor.
Qed.

Theorem step_deterministic:
  partial_function step.
Proof.
  unfold partial_function.
  intros.
  generalize dependent y2.
  induction H.
  + intros.
    inversion H0; subst; auto; inversion H3.
  + intros.
    inversion H0; subst. 
    - inversion H.
    - rewrite (IHstep t1'0); auto.
    - inversion H.
  + intros.
    inversion H0; subst.
    - inversion H.
    - inversion H4.
    - rewrite (IHstep t2'0); auto.
Qed.

End SimpleArith2.

Inductive value : tm -> Prop :=
  v_const : forall n, value (tm_const n).

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
          tm_plus (tm_const n1) (tm_const n2)
      --> tm_const (plus n1 n2)
  | ST_Plus1 : forall t1 t1' t2,
        t1 --> t1' ->
        tm_plus t1 t2 --> tm_plus t1' t2
  | ST_Plus2 : forall v1 t2 t2',
        value v1 -> (* <----- n.b. *)
        t2 --> t2' ->
        tm_plus v1 t2 --> tm_plus v1 t2'

  where " t '-->' t' " := (step t t').

Tactic Notation "step_cases" tactic(first) tactic(c) :=
  first;
  [ c "ST_PlusConstConst" | c "ST_Plus1" | c "ST_Plus2" ].

Ltac impossible :=
  match goal with
  | [ H : _ |- _ ] => inversion H; fail
  end.

Theorem step_deterministic:
  partial_function step.
Proof.
  unfold partial_function.
  intros.
  generalize dependent y2.
  induction H.
  + intros.
    inversion H0; subst; auto;
    impossible.
  + intros.
    inversion H0; subst; try impossible.
    - rewrite (IHstep t1'0); auto.
    - inversion H3.
      rewrite <- H1 in H; impossible.
  + intros.
    inversion H0; subst.
    - inversion H1; subst.
      inversion H; rewrite <- H2 in H5; impossible.
      rewrite (IHstep t2'); auto. 
    - inversion H1; subst.
      inversion H; rewrite <- H3 in H6; impossible.
      rewrite (IHstep t2'); auto.
    - inversion H1; subst.
      inversion H; rewrite <- H4 in H7; impossible.
      rewrite (IHstep t2'); auto.
Qed.

Theorem progress : forall t,
  value t \/ (exists t', t --> t').
Proof.
  induction t.
  + repeat constructor.
  + right.
    destruct IHt1; destruct IHt2.
    - destruct H. destruct H0.
      exists (tm_const (n + n0)).
      constructor.
    - destruct H0.
      exists (tm_plus t1 x).
      repeat constructor; auto.
    - destruct H.
      exists (tm_plus x t2).
      repeat constructor; auto.
    - destruct H.
      exists (tm_plus x t2).
      repeat constructor; auto.
Qed.


Definition normal_form {X:Type} (R:relation X) (t:X) : Prop :=
  ~ exists t', R t t'.

Lemma value_is_nf : forall t,
  value t -> normal_form step t.
Proof.
  intros.
  unfold normal_form.
  intro contra.
  destruct contra.
  destruct H.
  inversion H0.
Qed.

Lemma nf_is_value : forall t,
  normal_form step t -> value t.
Proof.
  intros.
  unfold normal_form in H.
  induction t.
  - constructor.
  - exfalso. apply H.
    set (progress (tm_plus t1 t2)).
    destruct o.
    + inversion H0.
    + assumption.
Qed.  

Definition stepmany := refl_step_closure step.
Notation " t '-->*' t' " := (stepmany t t') (at level 40).

