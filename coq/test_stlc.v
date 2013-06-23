Require Export Types.

Module STLC.

Inductive ty : Type :=
  | TBool : ty
  | TArrow : ty -> ty -> ty.

Inductive tm : Type :=
  | tvar : id -> tm
  | tapp : tm -> tm -> tm
  | tabs : id -> ty -> tm -> tm
  | ttrue : tm
  | tfalse : tm
  | tif : tm -> tm -> tm -> tm.

Definition x := (Id 0).
Definition y := (Id 1).
Definition z := (Id 2).

Hint Unfold x.
Hint Unfold y.
Hint Unfold z.

Inductive value : tm -> Prop :=
  | v_abs : forall x T t,
      value (tabs x T t)
  | t_true :
      value ttrue
  | t_false :
      value tfalse.

Hint Constructors value.

Fixpoint subst (x : id) (s : tm) (t : tm) :=
  match t with
  | tvar x' => (if beq_id x x' then s else t)
  | tabs x' T t1 =>
      tabs x' T (if beq_id x x' then t1 else subst x s t1)
  | tapp t1 t2 =>
      tapp (subst x s t1) (subst x s t2)
  | ttrue => ttrue
  | tfalse => tfalse
  | tif t1 t2 t3 =>
      tif (subst x s t1) (subst x s t2) (subst x s t3)
  end.

Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).

Reserved Notation "t1 '==>' t2" (at level 40).
Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T t12 v2,
      value v2 -> tapp (tabs x T t12) v2 ==> subst x v2 t12
  | ST_App1 : forall t1 t1' t2,
      t1 ==> t1' ->
      tapp t1 t2 ==> tapp t1' t2
  | ST_App2 : forall v1 t2 t2',
      value v1 ->
      t2 ==> t2' ->
      tapp v1 t2 ==> tapp v1 t2'
  | ST_IfTrue : forall t1 t2,
      tif ttrue t1 t2 ==> t1
  | ST_IfFalse : forall t1 t2,
      tif tfalse t1 t2 ==> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      tif t1 t2 t3 ==> tif t1' t2 t3
  where "t1 '==>' t2" := (step t1 t2).


Notation multistep := (multi step).
Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).

Notation idB :=
  (tabs x TBool (tvar x)).

Notation idBB :=
  (tabs x (TArrow TBool TBool) (tvar x)).

Lemma step_example1' :
  (tapp idBB idB) ==>* idB.
Proof.
  eapply multi_step.
  apply ST_AppAbs.
  auto.
  simpl.
  apply multi_refl.
Qed.

Module PartialMap.

Definition partial_map (A:Type) := id -> option A.
Definition empty {A:Type} : partial_map A := (fun _ => None).
Definition extend {A:Type} (G : partial_map A) (x : id) (T : A) :=
  fun x' => if beq_id x x' then Some T else G x'.

Lemma extend_eq : forall A (ctxt: partial_map A) x T,
  (extend ctxt x T) x = Some T.
Proof.
  intros.
  destruct x0.
  unfold extend; unfold beq_id; simpl.
  rewrite <- beq_nat_refl.
  auto.
Qed.

Lemma extend_neq : forall A (ctxt : partial_map A) x1 T x2,
  beq_id x2 x1 = false ->
  (extend ctxt x2 T) x1 = ctxt x1.
Proof.
  intros.
  unfold extend. rewrite H. auto.
Qed.

End PartialMap.

Definition context := partial_map ty.

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall G x T,
      G x = Some T ->
      has_type G (tvar x) T
  | T_Abs : forall x G T11 T12 t12,
      has_type (extend G x T11) t12 T12 ->
      has_type G (tabs x T11 t12) (TArrow T11 T12)
  | T_App : forall T11 T12 G t1 t2,
      has_type G t1 (TArrow T11 T12) ->
      has_type G t2 T11 ->
      has_type G (tapp t1 t2) T12
  | T_True : forall G,
      has_type G ttrue TBool
  | T_False : forall G,
      has_type G tfalse TBool
  | T_If : forall t1 t2 t3 T G,
      has_type G t1 TBool ->
      has_type G t2 T ->
      has_type G t3 T ->
      has_type G (tif t1 t2 t3) T.

Example typing_example_2_full :
  has_type empty
    (tabs x TBool
       (tabs y (TArrow TBool TBool)
          (tapp (tvar y) (tapp (tvar y) (tvar x)))))
    (TArrow TBool (TArrow (TArrow TBool TBool) TBool)).
Proof with (compute; auto).
  apply T_Abs.
  apply T_Abs.
  eapply T_App.
  - apply T_Var...
  - eapply T_App.
    + apply T_Var...
    + apply T_Var...
Qed.

Theorem progress : forall t T,
  has_type empty t T ->
  value t \/ exists t', t ==> t'.
Proof with (try constructor; eauto).
  intros t T Ht.
  remember (@empty ty) as G. 
  induction Ht.
  - rewrite HeqG in H.
    inversion H.
  - left. constructor.
  - right. 
    destruct IHHt1...
    apply IHHt2 in HeqG.
    destruct HeqG.
    + clear IHHt2.
      inversion H; subst.
      exists (subst x0 t2 t)...
      solve by inversion.
      solve by inversion.
    + destruct H0 as [t'].
      exists (tapp t1 t')...
    + destruct H as [t'].
      exists (tapp t' t2)...
  - left...
  - left...
  - right.
    remember HeqG as IH1. clear HeqIH1.
    remember HeqG as IH2. clear HeqIH2.
    remember HeqG as IH3. clear HeqIH3.
    apply IHHt1 in IH1.
    apply IHHt2 in IH2.
    apply IHHt3 in IH3.
    clear IHHt1.
    clear IHHt2.
    clear IHHt3.
    destruct IH1.
    destruct H.
    + solve by inversion.
    + exists t2...
    + exists t3...
    + destruct H as [t'].
      exists (tif t' t2 t3)...
Qed.

Inductive appears_free_in : id -> tm -> Prop :=
  | afi_var : for
