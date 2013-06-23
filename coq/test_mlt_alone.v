Require Import Arith.
Require Import Relations.
Require Import List.

Tactic Notation "solve_by_inversion_step" tactic(t) :=  
  match goal with  
  | H : _ |- _ => solve [ inversion H; subst; t ] 
  end
  || fail "because the goal is not solvable by inversion.".

Tactic Notation "solve" "by" "inversion" "1" :=
  solve_by_inversion_step idtac.
Tactic Notation "solve" "by" "inversion" "2" :=
  solve_by_inversion_step (solve by inversion 1).
Tactic Notation "solve" "by" "inversion" "3" :=
  solve_by_inversion_step (solve by inversion 2).
Tactic Notation "solve" "by" "inversion" :=
  solve by inversion 1.

Module Id.

Inductive t (A : Type) := 
  | Id : nat -> t A.

Definition eq {A} (i1 i2 : t A) :=
  match i1, i2 with
  | Id n1, Id n2 => beq_nat n1 n2
  end.

Lemma eq_refl {A} (i : t A) : true = eq i i.
Proof.
  destruct i.
  induction n; simpl; auto.
Qed.

Lemma eq_true {A} : forall i1 i2 : t A, true = eq i1 i2 -> i1 = i2.
Proof.
  intros.
  destruct i1; destruct i2.
  inversion H.
  apply beq_nat_eq in H1.
  subst; reflexivity.
Qed.

Lemma eq_false {A} : forall i1 i2 : t A, false = eq i1 i2 -> i1 <> i2.
Proof.
  intros.
  destruct i1; destruct i2.
  inversion H.
  intro Heq.
  apply (beq_nat_false n n0); auto.
  inversion Heq.
  reflexivity.
Qed.

End Id.

Inductive ty : Type :=
  | TVar : Id.t ty -> ty
  | TArrow : ty -> ty -> ty
  | TForall : Id.t ty -> ty -> ty.

Inductive tm : Type :=
  | tvar : Id.t tm -> tm
  | tapp : tm -> tm -> tm
  | tabs : Id.t tm -> ty -> tm -> tm
  | tABS : Id.t ty -> tm -> tm
  | tAPP : tm -> ty -> tm.

Definition x := (Id.Id tm 0).
Definition y := (Id.Id tm 1).
Definition z := (Id.Id tm 2).

Definition X := (Id.Id ty 3).
Definition Y := (Id.Id ty 4).
Definition Z := (Id.Id ty 5).

Hint Unfold x y z X Y Z.

Inductive value : tm -> Prop :=
  | v_abs : forall x T t,
      value (tabs x T t)
  | v_ABS : forall x t,
      value t ->
      value (tABS x t).

Hint Constructors value.

Fixpoint subst_tm (x : Id.t tm) (s : tm) (t : tm) :=
  match t with
  | tvar x' => if Id.eq x x' then s else t
  | tabs x' T t1 => tabs x' T (if Id.eq x x' then t1 
                               else subst_tm x s t1)
  | tapp t1 t2 => tapp (subst_tm x s t1) (subst_tm x s t2)
  | tABS x' t1 => tABS x' (subst_tm x s t1)
  | tAPP t1 T => tAPP (subst_tm x s t1) T
  end.

Fixpoint subst_ty (x : Id.t ty) (s : ty) (t : ty) :=
  match t with
  | TVar x' => if Id.eq x x' then s else t
  | TArrow t1 t2 => TArrow (subst_ty x s t1) (subst_ty x s t2) 
  | TForall x' t' => 
      TForall x (if Id.eq x x' then t' else subst_ty x s t')
  end.

Fixpoint subst_ty_tm (x : Id.t ty) (s : ty) (t : tm) :=
  match t with
  | tvar x' => t
  | tabs x' T t1 => tabs x' (subst_ty x s T) (subst_ty_tm x s t1)
  | tapp t1 t2 => tapp (subst_ty_tm x s t1) (subst_ty_tm x s t2)
  | tABS x' t1 => tABS x' (if Id.eq x x' then t1
                           else subst_ty_tm x s t1)
  | tAPP t1 T => tAPP (subst_ty_tm x s t1) (subst_ty x s T)
  end.

Notation "t '[' x '<-' s ']'" := (subst_tm x s t) (at level 20).
Notation "t '[[' x '<=' s ']]'" := (subst_ty x s t) (at level 20).
Notation "t '[' x '<=' s ']'" := (subst_ty_tm x s t) (at level 20).

Reserved Notation "t1 '==>' t2" (at level 40).
Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T t12 v2,
      value v2 -> tapp (tabs x T t12) v2 ==> subst_tm x v2 t12
  | ST_App1 : forall t1 t1' t2,
      t1 ==> t1' ->
      tapp t1 t2 ==> tapp t1' t2
  | ST_App2 : forall v1 t2 t2',
      value v1 ->
      t2 ==> t2' ->
      tapp v1 t2 ==> tapp v1 t2'
  | ST_AppABS : forall X v1 T,
      value v1 ->
      tAPP (tABS X v1) T ==> subst_ty_tm X T v1
  | ST_AppABS1 : forall t1 t1' T,
      t1 ==> t1' ->
      tAPP t1 T ==> tAPP t1' T
  | ST_ABS : forall X t1 t1',
      t1 ==> t1' ->
      tABS X t1 ==> tABS X t1'
  where "t1 '==>' t2" := (step t1 t2).

Inductive multi {X:Type} (R: relation X) : relation X :=
  | multi_refl : forall (x : X),
                 multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

Notation multistep := (multi step).
Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).

Notation idB :=
  (tABS X (tabs x (TVar X) (tvar x))).

Notation idBB :=
  (tABS X (tabs x (TArrow (TVar X) (TVar X)) (tvar x))).

Lemma step_example1' :
  (tABS X (tapp (tAPP idBB (TVar X)) (tAPP idB (TVar X)))) ==>* idB.
Proof.
  eapply multi_step.
    apply ST_ABS.
    apply ST_App1.
    apply ST_AppABS.
    auto.
  eapply multi_step.
    simpl.
    apply ST_ABS.
    apply ST_App2.
    auto.
    apply ST_AppABS.
    auto.
  eapply multi_step.
    simpl.
    apply ST_ABS.
    apply ST_AppAbs. 
    auto.
  apply multi_refl.
Qed.

Module Context.

Inductive binding :=
  | TmVar  : Id.t tm -> ty -> binding
  | TyFree : Id.t ty -> binding.

Definition t := list binding.
Definition empty : t := nil.

Inductive unbound : forall A : Type, Id.t A -> t -> Prop :=
  | U_Empty : forall A id, unbound A id empty
  | U_TmVar : forall id1 id2 ty' ct,
      id1 <> id2 ->
      unbound tm id1 ct ->
      unbound tm id1 (TmVar id2 ty' :: ct)
  | U_TmStep : forall id1 id2 ct,
      unbound tm id1 ct ->
      unbound tm id1 (TyFree id2 :: ct)
  | U_TyFree : forall id1 id2 ct,
      id1 <> id2 ->
      unbound ty id1 ct ->
      unbound ty id1 (TyFree id2 :: ct)
  | U_TyStep : forall id1 id2 ty' ct,
      unbound ty id1 ct ->
      unbound ty id1 (TmVar id2 ty' :: ct).

Inductive bound_tm : Id.t tm -> ty -> t -> Prop :=
  | B_TmVar : forall id ty' ctx,
      unbound tm id ctx ->
      bound_tm id ty' (TmVar id ty' :: ctx)
  | B_TmStepTm : forall id1 ty1 id2 ty2 ctx,
      bound_tm id1 ty1 ctx ->
      id1 <> id2 ->
      bound_tm id1 ty1 (TmVar id2 ty2 :: ctx)
  | B_TmStepTy : forall id1 ty1 id2 ctx,
      bound_tm id1 ty1 ctx ->
      bound_tm id1 ty1 (TyFree id2 :: ctx).

Inductive bound_ty : Id.t ty -> t -> Prop :=
  | B_TyFree : forall id ctx,
      unbound ty id ctx ->
      bound_ty id (TyFree id :: ctx)
  | B_TyStepTy : forall id1 id2 ctx,
      bound_ty id1 ctx ->
      id1 <> id2 ->
      bound_ty id1 (TyFree id2 :: ctx)
  | B_TyStepTm : forall id1 id2 ty2 ctx,
      bound_ty id1 ctx ->
      bound_ty id1 (TmVar id2 ty2 :: ctx).

Definition extend (G : t) (b : binding) := b :: G.
Definition bind_tm (G : t) x T := (TmVar x T) :: G.
Definition bind_ty (G : t) x := (TyFree x) :: G.

(*Lemma extend_eq : forall (ctxt: context) x T,
  (extend ctxt x T) x = T.
Proof.
  intros.
  destruct x0.
  unfold extend; unfold beq_id; simpl.
  rewrite <- beq_nat_refl.
  auto.
Qed.

Lemma extend_neq : forall (ctxt : context) x1 T x2,
  beq_id x2 x1 = false ->
  (extend ctxt x2 T) x1 = ctxt x1.
Proof.
  intros.
  unfold extend. rewrite H. auto.
Qed.

Lemma extend_shadow : forall (ctxt: context) x T1 T2,
  (extend (extend ctxt x T1) x T2) = (extend ctxt x T2).
Proof.
  intros.
  extensionality x.
  unfold extend.
  destruct (beq_id x0 x); auto.
Qed.

Lemma extend_commute : forall (ctxt : context) x1 x2 T1 T2,
  x1 <> x2 ->
  (extend (extend ctxt x1 T1) x2 T2) = (extend (extend ctxt x2 T2) x1 T1).
Proof.
  intros.
  extensionality x.
  unfold extend.
  remember (beq_id x2 x) as x2x.
  remember (beq_id x1 x) as x1x.
  destruct x2x.
  destruct x1x; subst.
  + apply beq_id_eq in Heqx2x.
    apply beq_id_eq in Heqx1x.
    subst. exfalso.
    apply H. auto.
  + auto.
  + auto.
Qed.*)

End Context.

Inductive appears_free_in : Id.t tm -> tm -> Prop :=
  | afi_var : forall x,
      appears_free_in x (tvar x)
  | afi_app1 : forall x t1 t2,
      appears_free_in x t1 -> appears_free_in x (tapp t1 t2)
  | afi_app2 : forall x t1 t2,
      appears_free_in x t2 -> appears_free_in x (tapp t1 t2)
  | afi_abs1 : forall x y T11 t12,
      y <> x ->
      appears_free_in x t12 ->
      appears_free_in x (tabs y T11 t12)
  | afi_APP1 : forall x t T,
      appears_free_in x t ->
      appears_free_in x (tAPP t T)
  | afi_ABS : forall x X t,
      appears_free_in x t ->
      appears_free_in x (tABS X t).

Definition closed (t:tm) :=
  forall x, ~ appears_free_in x t.

Inductive wf_type : Context.t -> ty -> Prop :=
  | WF_Var : forall G X,
      Context.In (Context.TyFree X) G ->
      wf_type G (TVar X)
  | WF_Arrow : forall G T1 T2,
      wf_type G T1 ->
      wf_type G T2 ->
      wf_type G (TArrow T1 T2)
  | WF_Forall : forall G X T,
      wf_type (Context.bind_ty G X) T ->
      wf_type G (TForall X T).

Inductive has_type : Context.t -> tm -> ty -> Prop :=
  | T_Var : forall G x T,
      Context.In (Context.TmVar x T) G ->
      has_type G (tvar x) T
  | T_Abs : forall x G T11 T12 t12,
      has_type (Context.bind_tm G x T11) t12 T12 ->
      has_type G (tabs x T11 t12) (TArrow T11 T12)
  | T_App : forall T11 T12 G t1 t2,
      has_type G t1 (TArrow T11 T12) ->
      has_type G t2 T11 ->
      has_type G (tapp t1 t2) T12
  | T_ABS : forall X G T body,
      has_type (Context.bind_ty G X) body T ->
      has_type G (tABS X body) (TForall X T)
  | T_APP : forall X G body T T',
      has_type G body (TForall X T) ->
      wf_type G T' ->
      has_type G (tAPP body T') (subst_ty X T' T).

Example typing_example_2_full :
  has_type (Context.bind_ty Context.empty X)
    (tabs x (TVar X)
       (tabs y (TArrow (TVar X) (TVar X))
          (tapp (tvar y) (tapp (tvar y) (tvar x)))))
    (TArrow (TVar X) (TArrow (TArrow (TVar X) (TVar X)) (TVar X))).
Proof with (compute; auto).
  apply T_Abs.
  apply T_Abs.
  eapply T_App.
  - apply T_Var.
    simpl.
    left.
    split.
    auto.
    intro H.
    destruct H.
    apply H0.
    left.
    split.
  - eapply T_App.
    + apply T_Var...
    + apply T_Var...
Qed.

Theorem progress G t T :
  closed t -> has_type G t T ->
  value t \/ exists t', t ==> t'. 
Proof with (try constructor; eauto).
  intros Hcl Ht.
  induction Ht; intros.
  - unfold closed in Hcl.
    exfalso.
    apply (Hcl x0).
    constructor.
  - left. constructor.
  - right.
    assert (closed t1).
      unfold closed.
      intros x0 appear.
      apply (Hcl x0)...
    assert (closed t2).
      unfold closed.
      intros x0 appear.
      apply (Hcl x0).
      apply afi_app2...
    apply IHHt1 in H.
    apply IHHt2 in H0.
    destruct H; [ destruct H0 | .. ].
    + inversion Ht1; subst.
      * solve by inversion 2.
      * eexists...
      * solve by inversion 2.
      * solve by inversion 2.
    + destruct H0. 
      exists (tapp t1 x0)...
    + destruct H as [t'].
      exists (tapp t' t2)...
  - assert (closed body).
      intros x H.
      apply (Hcl x).
      apply afi_ABS...
    apply IHHt in H.
    destruct H.
    * left...
    * right. destruct H.
      eexists...
  - assert (closed body).
      intros x H'.
      apply (Hcl x).
      apply afi_APP1...
    apply IHHt in H0; clear IHHt; destruct H0.
    * destruct H0.
      inversion Ht.
      right.
      eexists...
    * right.
      destruct H0.
      exists (tAPP x0 T')...
Qed.

Lemma substitution_preserves_typing t : forall G x U t' T,
     has_type (Context.bind_tm G x U) t T ->
     has_type G t' U ->
     has_type G (t [x <- t']) T.
Proof.
  induction t.

  - intros; simpl.
    remember (Id.eq x0 t) as eq_x.
    destruct eq_x.
    + inversion H.
      apply Id.eq_true in Heqeq_x; subst.
      inversion H3.
      inversion H1; subst.
      auto.
    + 
    - 
    inversion H0; subst.

    + subst.
Qed.

(*Lemma has_type_in_context : forall G G0 t T,
  (forall x, G0 x = G x \/ G0 x = Empty) ->
  has_type G0 t T ->
  has_type G t T.
Proof.
  intros G G0 T t HG H.
  induction H.
  - destruct (HG x0).
    constructor. rewrite <- H0. auto.
    rewrite H in H0.
    inversion H0.
  - constructor.
    assert (has_type G t12 T12).
    apply IHhas_type. 
      intros.
      remember (beq_id x1 x0) as xeq.
      destruct xeq.
      apply beq_id_eq in Heqxeq; subst.
admit.*)

Lemma substitution_preserves_typing t : forall G x U t' T,
     has_type (extend G x (TmVar U)) t T ->
     has_type empty t' U ->
     has_type G ([x:=t']t) T.
Proof.
  induction t; intros; remember empty as G0.
  - (*unfold subst_tm.
    remember (beq_id x0 i) as eqx.
    destruct eqx.
    + apply beq_id_eq in Heqeqx.
      inversion H.
      subst x0 x1 T0 G1.
      rewrite PartialMap.extend_eq in H3.
      inversion H3; subst U; clear H3.
      inversion H0.
      * subst G0; inversion H1.
      * subst. 
      unfold G0 in H0.
  induction t.
  - unfold subst_tm.
    remember (beq_id x0 i) as Hx0.
    destruct Hx0.
    apply beq_id_eq in HeqHx0; subst.
    inversion H; subst.
    rewrite PartialMap.extend_eq in H3.
    inversion H3.
    rewrite <- H2.*)
    admit.
  - simpl.
    inversion H; subst.
    apply IHt1 with (t':=t') in H4; auto.
    apply IHt2 with (t':=t') in H6; auto.
    apply T_App with (T11:=T11); auto.
  - simpl. inversion H; subst.
    remember (beq_id x0 i) as eqx.
    destruct eqx.
    * apply T_Abs.
      apply beq_id_eq in Heqeqx; subst.
      rewrite PartialMap.extend_shadow in H6.
      auto.
    * apply T_Abs.
      inversion H; subst.
      apply IHt with (U:=U); auto.
      rewrite PartialMap.extend_commute in H6; auto.
  - simpl. 
    inversion H; subst.
    constructor.
    remember (beq_id x0 i) as eqx.
    destruct eqx.
    apply IHt.
    
Qed.
