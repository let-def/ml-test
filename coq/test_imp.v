Require Export SfLib.

Module AExp.

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

Fixpoint aeval (e : aexp) : nat :=
  match e with
  | ANum n => n
  | APlus a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2 => (aeval a1) - (aeval a2)
  | AMult a1 a2 => (aeval a1) * (aeval a2)
  end.

Example test_aeval1:
  aeval (APlus (ANum 2) (ANum 2)) = 4.
Proof.
  reflexivity.
Qed.

Fixpoint beval (e : bexp) : bool :=
  match e with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => beq_nat (aeval a1) (aeval a2)
  | BLe a1 a2 => ble_nat (aeval a1) (aeval a2)
  | BNot b1 => negb (beval b1)
  | BAnd b1 b2 => andb (beval b1) (beval b2)
  end.

Fixpoint optimize_0plus (e : aexp) : aexp :=
  match e with
  | ANum n => ANum n
  | APlus (ANum 0) n => n
  | APlus e1 e2 => APlus (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 => AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult e1 e2 => AMult (optimize_0plus e1) (optimize_0plus e2)
  end.

Theorem optimize_0plus_sound : forall e,
  aeval (optimize_0plus e) = aeval e.
Proof.
  intros e. induction e; try (simpl; auto; fail).

  destruct e1.
  + destruct n; simpl; auto.
  + destruct e1_1; simpl; auto.
  + destruct e1_1; simpl; auto.
  + destruct e1_1; simpl; auto.
Qed.

Fixpoint bexp_map_aexp (f : aexp -> aexp) (b : bexp) :=
  match b with
  | BTrue => BTrue
  | BFalse => BFalse
  | BEq a1 a2 => BEq (f a1) (f a2)
  | BLe a1 a2 => BLe (f a1) (f a2)
  | BNot b => BNot (bexp_map_aexp f b)
  | BAnd b1 b2 => BAnd (bexp_map_aexp f b1) (bexp_map_aexp f b2)
  end.

Theorem beval_map_aexp_sound 
  (f : aexp -> aexp) 
  (H : forall a:aexp, aeval (f a) = aeval a) :
  forall b: bexp, beval (bexp_map_aexp f b) = beval b.
Proof.
  intro b.
  induction b; simpl; auto.
  + rewrite IHb; trivial. 
  + rewrite IHb1, IHb2; trivial.
Qed.

Reserved Notation "e '==>' n" (at level 40).
Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum : forall (n:nat), (ANum n) ==> n
  | E_APlus : forall (e1 e2 : aexp) (n1 n2 : nat),
      (e1 ==> n1) -> (e2 ==> n2) -> (APlus e1 e2) ==> (n1 + n2)
  | E_AMinus : forall (e1 e2 : aexp) (n1 n2 : nat),
      (e1 ==> n1) -> (e2 ==> n2) -> (AMinus e1 e2) ==> (n1 - n2)
  | E_AMult : forall (e1 e2 : aexp) (n1 n2 : nat),
      (e1 ==> n1) -> (e2 ==> n2) -> (AMult e1 e2) ==> (n1 * n2)
  where "e '==>' n" := (aevalR e n).

Theorem aeval_iff_aevalR : forall a n,
  aeval a = n <-> (a ==> n).
Proof.
  split.
  + generalize dependent n.
    induction a; intros; subst; constructor;
      try apply IHa1; try apply IHa2; reflexivity.
  + intros. induction H; simpl; auto.
Qed.

End AExp.

(* States *)
Definition state := id -> nat.
Definition empty_state : state := fun _ => 0.
Definition update (st : state) (V : id) (n : nat) : state :=
  fun V' => if beq_id V V' then n else st V'.

Theorem update_eq : forall n V st,
  (update st V n) V = n.
Proof.
  intros.
  unfold update.
  assert (beq_id V V = true).
    destruct V. induction n0; auto.
  rewrite H; auto.
Qed.

Theorem update_neq : forall V2 V1 n st,
  beq_id V2 V1 = false ->
  (update st V2 n) V1 = (st V1).
Proof.
  intros.
  unfold update. rewrite H.
  reflexivity.
Qed.

Theorem update_example : forall (n:nat),
  (update empty_state (Id 2) n) (Id 3) = 0.
Proof.
  intro.
  compute.
  reflexivity.
Qed.

Theorem update_shadow : forall x1 x2 k1 k2 (f : state),
   (update (update f k2 x1) k2 x2) k1 = (update f k2 x2) k1.
Proof.
  intros.
  unfold update.
  destruct (beq_id k2 k1); auto.
Qed.

Theorem beq_id_eq k1 k2 : beq_id k1 k2 = true <-> k1 = k2.
Proof.
  split.

  - destruct k1. 
    destruct k2. 
    revert n0.

    induction n; induction n0.

    + auto.
    + intros; inversion H.
    + intros; inversion H.
    + intros. repeat f_equal.
      assert (beq_id (Id n) (Id n0) = true).
      rewrite <- H.
      compute. auto.
      assert (Id n = Id n0) by apply (IHn n0 H0).
      injection H1; intro; auto.
  - intro.
    rewrite H.
    destruct k2.
    unfold beq_id; simpl.
    clear H; clear k1.
    induction n; auto.
Qed.

Theorem update_same : forall x1 k1 k2 (f : state),
  f k1 = x1 ->
  (update f k1 x1) k2 = f k2.
Proof.
  intros.
  unfold update.
  remember (beq_id k1 k2) as H'.
  destruct H'; auto.
  symmetry in HeqH'.
  rewrite <- H.
  assert (k1 = k2) by
    (apply (beq_id_eq _ _); auto).
  subst. auto.
Qed.
 
Theorem update_permute : forall x1 x2 k1 k2 k3 f,
  beq_id k2 k1 = false ->
  (update (update f k2 x1) k1 x2) k3 = (update (update f k1 x2) k2 x1) k3.
Proof.
  intros.
  unfold update.
  remember (beq_id k1 k3) as b.
  destruct b.
  remember (beq_id k2 k3) as b'.
  destruct b'.
  + symmetry in Heqb; symmetry in Heqb'.
    assert (k1 = k3) by (apply (beq_id_eq _ _); auto).
    assert (k2 = k3) by (apply (beq_id_eq _ _); auto).
    rewrite H0 in H.
    rewrite H1 in H.
    assert (beq_id k3 k3 = true)
      by (apply (beq_id_eq k3 k3); auto).
      rewrite H2 in H; inversion H.
  + auto.
  + auto.
Qed.


Inductive aexp : Type :=
  | ANum : nat -> aexp
  | AId : id -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

Definition X : id := Id 0.
Definition Y : id := Id 1.
Definition Z : id := Id 2.

Fixpoint aeval (st : state) (e : aexp) : nat :=
  match e with
  | AId id => st id
  | ANum n => n
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2 => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (e : bexp) : bool :=
  match e with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => beq_nat (aeval st a1) (aeval st a2)
  | BLe a1 a2 => ble_nat (aeval st a1) (aeval st a2)
  | BNot b1 => negb (beval st b1)
  | BAnd b1 b2 => andb (beval st b1) (beval st b2)
  end.

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com.

Notation "'SKIP'" :=
  CSkip.
Notation "l '::=' a" :=
  (CAss l a) (at level 60).
Notation "c1 ; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity).

Fixpoint ceval_step1 (st : state) (c : com) : state :=
  match c with
  | SKIP => st
  | l ::= a1 =>
      update st l (aeval st a1)
  | c1 ; c2 =>
      let st' := ceval_step1 st c1 in
      ceval_step1 st' c2
  | IFB b THEN c1 ELSE c2 FI =>
      if (beval st b)
      then ceval_step1 st c1
      else ceval_step1 st c2
  | WHILE b1 DO c1 END => st
  end.


Fixpoint ceval_step2 (st : state) (c : com) (i : nat) : state :=
  match i with
  | O => empty_state
  | S i' =>
    match c with
      | SKIP =>
          st
      | l ::= a1 =>
          update st l (aeval st a1)
      | c1 ; c2 =>
          let st' := ceval_step2 st c1 i' in
          ceval_step2 st' c2 i'
      | IFB b THEN c1 ELSE c2 FI =>
          if (beval st b) then ceval_step2 st c1 i' else ceval_step2 st c2 i'
      | WHILE b1 DO c1 END =>
          if (beval st b1)
          then let st' := ceval_step2 st c1 i' in
               ceval_step2 st' c i'
          else st
    end
  end.


Fixpoint ceval_step3 (st : state) (c : com) (i : nat)
                    : option state :=
  match i with
  | O => None
  | S i' =>
    match c with
      | SKIP =>
          Some st
      | l ::= a1 =>
          Some (update st l (aeval st a1))
      | c1 ; c2 =>
          match (ceval_step3 st c1 i') with
          | Some st' => ceval_step3 st' c2 i'
          | None => None
          end
      | IFB b THEN c1 ELSE c2 FI =>
          if (beval st b) then ceval_step3 st c1 i' else ceval_step3 st c2 i'
      | WHILE b1 DO c1 END =>
          if (beval st b1)
          then match (ceval_step3 st c1 i') with
               | Some st' => ceval_step3 st' c i'
               | None => None
               end
          else Some st
    end
  end.


Definition bind_option {X Y : Type} (xo : option X) (f : X -> option Y)
                      : option Y :=
  match xo with
    | None => None
    | Some x => f x
  end.

Fixpoint ceval_step (st : state) (c : com) (i : nat)
                    : option state :=
  match i with
  | O => None
  | S i' =>
    match c with
      | SKIP =>
          Some st
      | l ::= a1 =>
          Some (update st l (aeval st a1))
      | c1 ; c2 =>
          bind_option
            (ceval_step st c1 i')
            (fun st' => ceval_step st' c2 i')
      | IFB b THEN c1 ELSE c2 FI =>
          if (beval st b) then ceval_step st c1 i' else ceval_step st c2 i'
      | WHILE b1 DO c1 END =>
          if (beval st b1)
          then bind_option
                 (ceval_step st c1 i')
                 (fun st' => ceval_step st' c i')
          else Some st
    end
  end.

Definition test_ceval (st:state) (c:com) :=
  match ceval_step st c 500 with
  | None => None
  | Some st => Some (st X, st Y, st Z)
  end.

Definition pup_to_n : com :=
  Z ::= ANum 1;
  Y ::= ANum 0;
  WHILE BLe (AId Z) (AId X) DO
    Y ::= APlus (AId Y) (AId Z);
    Z ::= APlus (AId Z) (ANum 1)
  END;
  X ::= ANum 0;
  Z ::= ANum 0.



Example pup_to_n_1 : 
  test_ceval (update empty_state X 5) pup_to_n
  = Some (0, 15, 0).
Proof. reflexivity. Qed.

Definition even_X : com :=
  Z ::= ANum 1;
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    X ::= AMinus (AId X) (ANum 1);
    Z ::= AMinus (ANum 1) (AId Z)
  END.

Reserved Notation "c1 '/' st '==>' st'" (at level 40, st at level 39).
Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      SKIP / st ==> st
  | E_Ass : forall st a1 n l,
      aeval st a1 = n ->
      (l ::= a1) / st ==> (update st l n)
  | E_Seq : forall c1 c2 st st' st'',
      c1 / st ==> st' ->
      c2 / st' ==> st'' ->
      (c1 ; c2) / st ==> st''
  | E_IfTrue : forall st st' b1 c1 c2,
      beval st b1 = true ->
      c1 / st ==> st' ->
      (IFB b1 THEN c1 ELSE c2 FI) / st ==> st'
  | E_IfFalse : forall st st' b1 c1 c2,
      beval st b1 = false ->
      c2 / st ==> st' ->
      (IFB b1 THEN c1 ELSE c2 FI) / st ==> st'
  | E_WhileEnd : forall b1 st c1,
      beval st b1 = false ->
      (WHILE b1 DO c1 END) / st ==> st
  | E_WhileLoop : forall st st' st'' b1 c1,
      beval st b1 = true ->
      c1 / st ==> st' ->
      (WHILE b1 DO c1 END) / st' ==> st'' ->
      (WHILE b1 DO c1 END) / st ==> st''

  where "c1 '/' st '==>' st'" := (ceval c1 st st').

Theorem ceval_step__ceval: forall c st st',
      (exists i, ceval_step st c i = Some st') ->
      c / st ==> st'.
Proof.
  intros.
  destruct H; rename H into E.
  generalize dependent st.
  generalize dependent st'.
  generalize dependent c.
  induction x.
  + (* x = 0 *)
    intros; inversion E.
  + induction c; intros; inversion E; try (constructor; auto; fail).
    - unfold bind_option in H0.
      remember (ceval_step st c1 x).
      induction o.
      * apply E_Seq with (st' := a);
        apply IHx; auto.
      * inversion H0.
    - remember (beval st b) as bval.
      induction bval.
      * apply E_IfTrue; auto.
      * apply E_IfFalse; auto.
    - remember (beval st b) as bval.
      induction bval.
      * unfold bind_option in H0.
        remember (ceval_step st c x).
        destruct o.
        apply E_WhileLoop with (st':=s); auto.
        try inversion H0.
      * inversion H0.
        apply E_WhileEnd.
        subst; auto.
Qed.

Theorem ceval_step_more: forall i1 i2 st st' c,
  i1 <= i2 -> ceval_step st c i1 = Some st' ->
  ceval_step st c i2 = Some st'.
Proof.
  induction i1.
  * intros; inversion H0.
  * intros.
    induction i2; [inversion H | .. ].
    apply le_S_n in H.
    destruct c.
    - (* SKIP *) simpl; inversion H0; auto.
    - (* ::= *) simpl; inversion H0; auto.
    - (* ; *)
      inversion H0.  
      remember (ceval_step st c1 i1) as st'c1.
      destruct st'c1; symmetry in Heqst'c1.
      + simpl.
        pose Heqst'c1.
        apply IHi1 with (i2:=i2) in e; auto.
        rewrite e; simpl.
        simpl in H2.
        rewrite (IHi1 i2 _ _ _ H H2).
        auto.
      + inversion H2.
   - (* IF *)
     inversion H0; simpl.
     destruct (beval st b).
     + rewrite (IHi1 i2 _ _ _ H H2).
       auto.
     + rewrite (IHi1 i2 _ _ _ H H2).
       auto.
   - (* WHILE *)
     inversion H0; simpl.
     destruct (beval st b); try reflexivity.
     remember (ceval_step st c i1) as st'c1.
     destruct st'c1. 
     + simpl. simpl in H2.
       symmetry in Heqst'c1.
       assert (ceval_step st c i2 = Some s) as Heqst'c1'
         by (apply IHi1; auto).
       rewrite Heqst'c1'.
       simpl.
       rewrite H2.
       apply IHi1 with (i2:=i2) in H2; auto.
     + inversion H2.
Qed.

Theorem ceval_deterministic: forall c st st1 st2,
     c / st ==> st1 ->
     c / st ==> st2 ->
     st1 = st2.
Proof.
  intros.
  generalize dependent st2.
  (*induction c. 
  - inversion H; intros; inversion H0; auto.
  - inversion H; intros. inversion H5.
    rewrite <- H10, <- H4; reflexivity.
  - inversion H; subst.
    intros.
    inversion H0; subst.

  inversion H6; subst.*)

  induction H.
  - intros. inversion H0. auto.
  - intros. inversion H0; subst. auto.
  - intros. inversion H1; subst.
    apply IHceval2.
    rewrite (IHceval1 st'0 H4).
    auto.
  - intros.
    inversion H1; subst.
    + apply IHceval; auto. 
    + rewrite H7 in H.
      inversion H.
  - intros.
    inversion H1; subst.
    + congruence.
    + apply IHceval; auto.
  - intros.
    inversion H0; subst; auto.
    congruence.
  - intros.
    inversion H2; subst.
    + congruence.
    + apply IHceval2.
      rewrite IHceval1 with (st2:=st'0); auto.
Qed.

Inductive sinstr : Type :=
  | SPush : nat -> sinstr
  | SLoad : id -> sinstr
  | SPlus : sinstr
  | SMinus : sinstr
  | SMult : sinstr.
     
Fixpoint s_execute (st : state) (stack : list nat)
  (prog : list sinstr) : list nat :=
  match prog with
  | instr :: prog' =>
      match instr with
      | SPush n => s_execute st (n :: stack) prog'
      | SLoad V => s_execute st (st V :: stack) prog'
      | SPlus =>
          match stack with
          | a :: b :: stack' =>
              s_execute st ((b + a) :: stack') prog'
          | _ => s_execute st stack prog'
          end
      | SMult =>
          match stack with
          | a :: b :: stack' => 
              s_execute  st ((b * a) :: stack') prog'
          | _ => s_execute st stack prog'
          end
      | SMinus =>
          match stack with
          | a :: b :: stack' =>
              s_execute  st ((b - a) :: stack') prog'
          | _ => s_execute st stack prog'
          end
      end
  | nil => stack
  end.

Fixpoint s_compile (e : aexp) : list sinstr :=
  match e with
  | ANum n => [SPush n]
  | AId V => [SLoad V]
  | APlus e1 e2 => s_compile e1 ++ s_compile e2 ++ [SPlus]
  | AMult e1 e2 => s_compile e1 ++ s_compile e2 ++ [SMult]
  | AMinus e1 e2 => s_compile e1 ++ s_compile e2 ++ [SMinus]
  end.
 
Theorem s_execute_compose : forall st stk x xs,
 s_execute st stk (x :: xs) = s_execute st (s_execute st stk [x]) xs.
Proof.
  induction stk. 
  - intros.
    destruct x; auto.
  - intros.
    simpl.
    destruct x; destruct stk; auto.
Qed.

Theorem s_execute_compose' st stk l1 l2:
 s_execute st stk (l1 ++ l2) = s_execute st (s_execute st stk l1) l2.
Proof.
  generalize dependent stk.
  induction l1.
  - auto.
  - rewrite <- app_comm_cons.
    intro.
    rewrite s_execute_compose.
    rewrite IHl1.
    rewrite <- s_execute_compose.
    auto.
Qed.

Theorem s_compile_correct : forall (st : state) (e : aexp) stk,
  s_execute st stk (s_compile e) = (aeval st e) :: stk.
Proof.
  induction e; simpl; auto;
   (intros;
    rewrite s_execute_compose';
    rewrite s_execute_compose';
    rewrite IHe1;
    rewrite IHe2;
    reflexivity).
Qed.

