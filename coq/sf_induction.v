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

Lemma mult_1_r :
  forall m : nat, m * 1 = m.
Proof.
  intro m.
  induction m as [|m'].
  Case "m = 0". simpl. reflexivity.
  Case "m = S m'".
  {
    simpl.
    rewrite -> IHm'.
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

Theorem plus_n_Sm_left : forall n m : nat, S (n + m) = (S n) + m.
Proof.
  intros n m.
  replace (n + m) with (m + n).
  rewrite -> plus_n_Sm.
  rewrite -> plus_comm.
  reflexivity.
  {
    rewrite -> plus_comm.
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

Lemma mult_m_Sn : forall m n : nat, m * (S n) = m + m * n.
Proof.
  intros m n.
  induction m as [|m'].
  simpl. reflexivity.
  simpl.
  rewrite -> IHm'.
  replace (m' + (n + m' × n)) with (n + (m' + m' × n)).
  reflexivity.
  rewrite -> plus_comm.
  rewrite <- plus_assoc.
  replace (m' × n + n) with (n + m' × n).
  reflexivity.
  rewrite -> plus_comm.
  reflexivity.
Qed.

Lemma mult_Sm_n : forall m n : nat, (S m) * n = n + m * n.
Proof.
  intros m n.
  induction m as [|m'].
  simpl. reflexivity.
  simpl. reflexivity.
Qed.

Theorem mult_comm :
  forall m n : nat,
    m * n = n * m.
Proof.
  intros m n.
  induction m as [|m'].
  Case "m = 0". simpl. rewrite -> mult_0_r. reflexivity.
  Case "m = S m'".
  {
    rewrite -> mult_m_Sn.
    rewrite -> mult_Sm_n.
    rewrite -> IHm'.
    reflexivity.
  }
Qed.

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
  rewrite -> plus_0_r.
  reflexivity.
Qed.

Theorem all3_spec : forall b c : bool,
                      orb (andb b c) (orb (negb b) (negb c)) = true.
Proof.
  intros b c.
  destruct b.
  Case "b = false".
  {
    destruct c.
    SCase "c = false". simpl. reflexivity.
    SCase "c = true". simpl. reflexivity.
  }
  Case "b = true".
  {
    destruct c.
    SCase "c = false". simpl. reflexivity.
    SCase "c = true". simpl. reflexivity.
  }
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
                              (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p.
  induction p as [| p'].
  Case "p = 0". 
  {
    simpl.
    rewrite -> mult_0_r.
    rewrite -> mult_0_r.
    rewrite -> mult_0_r.
    simpl. reflexivity.
  }
  Case "p = S p'".
  {
    rewrite -> mult_comm. 
    simpl. 
    rewrite -> mult_comm.
    rewrite -> IHp'.
    assert (H1 : n × S p' = S p' × n).
    SSCase "Proof of H1". rewrite -> mult_comm. reflexivity.
    assert (H2 : m × S p' = S p' × m).
    SSCase "Proof of H2". rewrite -> mult_comm. reflexivity.
    rewrite -> H1. simpl.
    rewrite -> H2. simpl.
    Check plus_assoc.
    rewrite -> plus_assoc.
    rewrite -> plus_assoc.
    assert (H3 : p' × n = n × p').
    SSCase "Proof of H3". rewrite -> mult_comm. reflexivity.
    rewrite -> H3.
    assert (H4 : p' × m = m × p').
    SSCase "Proof of H4". rewrite -> mult_comm. reflexivity.
    rewrite -> H4.
    assert (H5 : n + n × p' + m = n + m + n × p').
    SSCase "Proof of H5". 
    {
      rewrite -> plus_comm. 
      rewrite -> plus_assoc.
      assert (H6 : m + n = n + m). rewrite -> plus_comm. reflexivity.
      rewrite -> H6. reflexivity.
    }
    rewrite -> H5.
    reflexivity.
  }
Qed.

Theorem mult_assoc : forall n m p : nat,
                       n * (m * p) = (n * m) * p.
Proof.
  intros n m p.
  induction n as [| n'].
  Case "n = 0". simpl. reflexivity.
  Case "n = S n'".
  {
    simpl.
    rewrite -> mult_plus_distr_r.
    rewrite -> IHn'.
    reflexivity.
  }
Qed.

Theorem beq_nat_refl : forall n : nat, 
                         true = beq_nat n n.
Proof.
  intro n.
  induction n as [| n'].
  Case "n = 0". simpl. reflexivity.
  Case "n = S n'".
  {
    simpl.
    rewrite -> IHn'.
    reflexivity.
  }
Qed.

Theorem plus_swap' : forall n m p : nat, 
                       n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> plus_assoc.
  rewrite -> plus_assoc.
  replace (n + m) with (m + n). 
  reflexivity.
  rewrite <- plus_comm. 
  reflexivity.
Qed.

Lemma double_inc : 
  forall n : nat, (S n) + (S n) = S (S (n + n)).
Proof.
  intro n.
  induction n as [| n'].
  Case "n = 0". simpl. reflexivity.
  Case "n = S n'".
  {
    rewrite -> IHn'.
    simpl.
    Check plus_n_Sm.
    rewrite <- plus_n_Sm.
    Check plus_n_Sm.
    rewrite <- plus_n_Sm.
    reflexivity.
  }
Qed.

Theorem bin_inc_comm : 
  forall b : bin, bin_to_nat (bin_inc b) = S (bin_to_nat b).
Proof.
  intro b.
  induction b as [|b1|b2].
  Case "b = S0". simpl. reflexivity.
  Case "b = S1 b1". simpl. reflexivity.
  Case "b = S2 b2".
  {
    simpl.
    rewrite -> plus_0_r.
    rewrite -> plus_0_r.
    rewrite -> IHb2.
    rewrite -> double_inc.
    reflexivity.
  }
Qed.

Theorem bin_nat_comm : 
  forall n : nat, bin_to_nat (nat_to_bin n) = n.
Proof.
  intro n.
  induction n as [|n'].
  Case "n = 0". simpl. reflexivity.
  Case "n = S n'".
  {
    simpl.
    rewrite -> bin_inc_comm.
    rewrite -> IHn'.
    reflexivity.
  }
Qed.

Definition normalize (b : bin) : bin :=
  nat_to_bin (bin_to_nat b).

Theorem nat_bin_equivalence : 
  forall n : nat, forall b : bin, 
    (nat_to_bin n = (normalize b)) <-> (bin_to_nat (normalize b) = n).
Proof.
  intros n b.
  split.
  Case "nat_to_bin n = normalize b -> bin_to_nat (normalize b) = n".
  {
    induction n as [|n'].
    SCase "n = 0".
    {
      simpl.
      intro H1.
      rewrite <- H1.
      reflexivity.
    }
    SCase "n = S n'".
    {
      intro H2.
      rewrite <- H2.
      rewrite -> bin_nat_comm.
      reflexivity.
    }
  }
  Case "bin_to_nat (normalize b) = n -> nat_to_bin n = normalize b".
  {
    intro H3.
    rewrite <- H3.
    induction b as [|b1|b2].
    SCase "b = S0". simpl. compute. reflexivity.
    SCase "b = S1 b1".
    {
      replace (normalize (S1 b1)) with (nat_to_bin (bin_to_nat (S1 b1))).
      {
        simpl.
        rewrite -> plus_0_r.
        simpl.
        rewrite -> bin_nat_comm.
        reflexivity.
      }
      {
        compute.
        reflexivity.
      }
    }
    SCase "b = S2 b2".
    {
      replace (normalize (S2 b2)) with (nat_to_bin (bin_to_nat (S2 b2))).
      {
        rewrite -> bin_nat_comm.
        reflexivity.
      }
      {
        compute.
        reflexivity.
      }
    }
  }
Qed.

Check nat_bin_equivalence.