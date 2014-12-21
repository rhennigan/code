Require Export sf_basic.

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

Theorem andb_true_elim1 : forall a b : bool, andb a b = true -> a = true.
Proof.
  intros a b.
  intro H.
  destruct a.
  Case "a = true". 
  {
    simpl.
    reflexivity. 
  }
  Case "a = false".
  {
    rewrite <- H.
    simpl.
    reflexivity.
  }
Qed.

Theorem andb_true_elim2 : forall a b : bool, andb a b = true -> b = true.
Proof.
  intros a b.
  intro H.
  destruct b.
  Case "b = true".
  {
    simpl.
    reflexivity.
  }
  Case "b = false".
  {
    rewrite <- H.
    destruct a.
    SCase "a = true".
    {
      simpl.
      reflexivity.
    }
    SCase "a = false".
    {
      simpl.
      reflexivity.
    }
  }
Qed.

Theorem plus_0_r : forall n : nat, n + 0 = n.
Proof.
  intro n.
  induction n as [| k].
  Case "n = 0".
  {
    simpl.
    reflexivity.
  }
  Case "n = S k".
  {
    simpl.
    rewrite -> IHk.
    reflexivity.
  }
Qed.

Theorem minus_diag : forall n : nat, minus n n = 0.
Proof.
  intro n.
  induction n as [| m].
  Case "n = 0".
  {
    reflexivity.
  }
  Case "n = S m".
  {
    rewrite <- IHm.
    reflexivity.
  }
Qed.

Theorem mult_0_r : forall n : nat, n * 0 = 0.
Proof.
  intro n.
  induction n as [| m].
  Case "n = 0". reflexivity.
  Case "n = S m".
  {
    simpl.
    rewrite -> IHm.
    reflexivity.
  }
Qed.

Theorem plus_n_Sm : forall n m : nat, S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [| k].
  Case "n = 0". simpl. reflexivity.
  Case "n = S k".
  {
    simpl.
    rewrite <- IHk.
    reflexivity.
  }
Qed.

Theorem plus_comm : forall n m : nat, n + m = m + n.
Proof.
  intros n m.
  induction n as [| k].
  Case "n = 0". simpl. rewrite -> plus_0_r. reflexivity.
  Case "n = S k".
  {
    simpl. 
    rewrite <- plus_n_Sm.
    rewrite <- IHk.
    reflexivity.
  }
Qed.

Theorem plus_assoc : forall n m p : nat, n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [| k].
  Case "n = 0". simpl. reflexivity.
  Case "n = S k".
  {
    simpl.
    rewrite -> IHk.
    reflexivity.
  }
Qed.

Fixpoint double (n : nat) : nat :=
  match n with
    | O => O
    | S m => S (S (double m))
  end.

Lemma double_plus : forall n : nat, double n = n + n.
Proof.
  intro n.
  induction n as [| m].
  Case "n = 0". simpl. reflexivity.
  Case "n = S m".
  {
    Check plus_n_Sm.
    rewrite <- plus_n_Sm.
    simpl.
    rewrite -> IHm.
    reflexivity.
  }
Qed.

Theorem mult_0_plus' : forall n m : nat, (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n).
  Case "Proof of assertion". reflexivity.
  rewrite -> H. reflexivity.
Qed.

Theorem plus_rearrange : 
  forall n m p q : nat, 
    (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (n + m = m + n) as H.
  Case "Proof of assertion". rewrite <- plus_comm. reflexivity.
  rewrite -> H. reflexivity.
Qed.

Theorem plus_swap : 
  forall n m p : nat,
    n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> plus_assoc.
  rewrite -> plus_assoc.
  assert (n + m = m + n) as H. rewrite <- plus_comm. reflexivity.
  rewrite <- H. reflexivity.
Qed.

Theorem mult_comm :
  forall m n : nat,
    m * n = n * m.
Proof.
  Admitted.

Lemma evenb_n_plus_2 : forall n : nat, evenb n = evenb (S (S n)).
Proof.
  intro n.
  induction n as [| n'].
  Case "n = 0". simpl. reflexivity.
  Case "n = n'".
  {
    induction n' as [| n''].
    SCase "n' = 0". simpl. reflexivity.
    SCase "n' = n''". simpl. reflexivity.
  }
Qed.

Lemma double_neg : forall b : bool, negb (negb b) = b.
Proof.
  intro b.
  destruct b.
  simpl. reflexivity.
  simpl. reflexivity.
Qed.

Theorem evenb_n_oddb_Sn : forall n : nat, evenb n = negb (evenb (S n)).
Proof.
  intro n.
  induction n as [| n'].
  Case "n = 0". simpl. reflexivity.
  Case "n = n'". 
  {
    rewrite <- evenb_n_plus_2.
    rewrite -> IHn'.
    rewrite -> double_neg.
    reflexivity.
  }
Qed.

Theorem ble_nat_refl : forall n : nat,
  true = ble_nat n n.
Proof.
  intro n.
  induction n as [| m].
  Case "n = 0". simpl. reflexivity.
  Case "n = S m".
  {
    simpl.
    rewrite <- IHm.
    reflexivity.
  }
Qed.

Theorem zero_nbeq_S : forall n : nat,
  beq_nat 0 (S n) = false.
Proof.
  intro n. simpl. reflexivity.
Qed.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  intro b.
  destruct b.
  simpl. reflexivity.
  simpl. reflexivity.
Qed.

Theorem plus_ble_compat_l : forall n m p : nat, 
  ble_nat n m = true -> ble_nat (p + n) (p + m) = true.
Proof.
  intros n m p.
  intro H1.
  induction p as [| p'].
  Case "p = 0". simpl. exact H1.
  Case "p = S p'".
  {
    simpl.
    rewrite -> IHp'.
    reflexivity.
  }
Qed.

Theorem S_nbeq_0 : forall n : nat,
  beq_nat (S n) 0 = false.
Proof.
  intro n. simpl. reflexivity.
Qed.

Theorem mult_1_l : forall n : nat, 1 * n = n.
Proof.
  intro n.
  simpl.

Theorem all3_spec : forall b c : bool,
    orb
      (andb b c)
      (orb (negb b)
               (negb c))
  = true.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  (* FILL IN HERE *) Admitted.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  (* FILL IN HERE *) Admitted.