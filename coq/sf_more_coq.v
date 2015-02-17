Require Export sf_poly.

Theorem beq_nat_eq : forall n m, true = beq_nat n m -> n = m.
Proof.
  intros n.
  induction n as [| n'].
  Case "n = O".
  {
    intros m H.
    destruct m as [| m']. reflexivity.
    simpl in H. inversion H.
  }
  Case "n = S n'".
  {
    intros m H.
    destruct m as [| m'].
    SCase "m = O".
    {
      simpl in H. 
      inversion H.
    }
    SCase "m = S m'".
    {
      assert (S_eq : forall n m : nat, S n = S m -> n = m).
      SSCase "Proof of S_eq".
      {
        intro a.
        induction a as [| a'].
        SSSCase "a = O".
        {
          intros b H'.
          destruct b as [| b'].
          SSSSCase "b = O". reflexivity.
          SSSSCase "b = S b'". inversion H'.
        }
        SSSCase "a = S a'".
        {
          intros b H'.
          destruct b as [| b'].
          SSSSCase "b = O". inversion H'.
          SSSSCase "b = S b'". inversion H'. reflexivity.
        }
      }
      simpl in H.
      apply IHn' in H.
      rewrite -> H.
      reflexivity.
    }
  }
Qed.

Print beq_nat_eq.

Definition impossible (n : nat) : bool := 
  if beq_nat n 3
  then if beq_nat n 5
       then true
       else false
  else false.

Theorem impossible_false :
  forall n : nat, true = impossible n -> 3 = 5.
Proof.
  intro n.
  unfold impossible.
  remember (beq_nat n 3) as e3. destruct e3.
  Case "e3 = true".
  {
    remember (beq_nat n 5) as e5. destruct e5.
    SCase "e5 = true".
    {
      intro.
      assert (H3: n = 3). apply beq_nat_eq. assumption.
      assert (H5: n = 5). apply beq_nat_eq. assumption.
      remember n as n1.
      remember n as n2.
      rewrite -> Heqn1 in H3.
      rewrite -> H3 in Heqn1.
      rewrite -> H5 in Heqn1.
      symmetry.
      assumption.
    }
    SCase "e5 = false".
    {
      intro H.
      inversion H.
    }
  }
  Case "e3 = false".
  {
    intro H.
    inversion H.
  }
Qed.

Theorem rev_exercise1 : 
  forall (lst1 lst2 : list nat),
    lst1 = rev lst2 -> lst2 = rev lst1.
Proof.
  intros lst1 lst2 H.
  rewrite -> H.
  rewrite -> rev_involutive.
  reflexivity.
Qed.

SearchAbout rev.
Check f_equal.

Theorem trans_eq : forall (X : Type) (n m o : X), n = m -> m = o -> n = o.
Proof.
  intros X n m o H1 H2.
  rewrite -> H1.
  rewrite <- H2.
  reflexivity.
Qed.

Example trans_eq_example1 : 
  forall (a b c d e f : nat),
    [a;b] = [c;d] -> [c;d] = [e;f] -> [a;b] = [e;f].
Proof.
  intros.
  apply trans_eq with (m := [c;d]).
  apply H. apply H0.
Qed.

Example trans_eq_example2 :
  forall (n m o p : nat),
    m = (minustwo o) -> (n + p) = m -> (n + p) = (minustwo o).
Proof.
  intros.
  apply trans_eq with m.
  apply H0. apply H.
Qed.

Theorem eq_add_S :
  forall (n m : nat), S n = S m -> n = m.
Proof.
  intros n m H.
  inversion H.
  reflexivity.
Qed.

Theorem f_equal : forall (A B : Type) (f : A -> B) (x y : A), x = y -> f x = f y.
Proof.
  intros.
  inversion H.
  reflexivity.
Qed.

Theorem beq_nat_0_l : forall (n : nat), beq_nat 0 n = true -> n = 0.
Proof.
  intros.
  inversion H.
  destruct n.
  reflexivity.
  inversion H1.
Qed.

Theorem beq_nat_0_r : forall (n : nat), beq_nat n 0 = true -> n = 0.
Proof.
  intros.
  destruct n.
  reflexivity.
  inversion H.
Qed.

Theorem S_inj : forall (n m : nat) (b : bool), beq_nat (S n) (S m) = b -> beq_nat n m = b.
Proof.
  intros.
  simpl in H.
  assumption.
Qed.

Theorem plus_n_n_injective : forall (n m : nat), n + n = m + m -> n = m.
Proof.
  intro n.
  induction n as [|n'].
  Case "n = O".
  {
    intros m H.
    simpl in H.
    destruct m. reflexivity.
    inversion H.
  }
  Case "n = S n'".
  {
    intros m H.
    destruct m. inversion H.
    simpl in H. 
    inversion H.
    do 2 rewrite <- plus_n_Sm in H1.
    inversion H1.
    apply IHn' in H2.
    inversion H2.
    reflexivity.
  }
Qed.

Theorem double_injective : forall (n m : nat), double n = double m -> n = m.
Proof.
  intro n.
  induction n as [|n'].
  Case "n = O".
  {
    intros m H.
    destruct m.
    reflexivity.
    inversion H.
  }
  Case "n = S n'".
  {
    intros m H.
    destruct m as [|m']. inversion H.
    apply f_equal.
    apply IHn'.
    inversion H.
    reflexivity.
  }
Qed.

Theorem beq_nat_true : forall (n m : nat), beq_nat n m = true -> n = m.
Proof.
  intros n m H.
  symmetry in H.
  apply beq_nat_eq.
  assumption.
Qed.

Theorem double_injective2 : forall (n m : nat), double n = double m -> n = m.
Proof.
  intros n m.
  generalize dependent n.
  induction m as [|m'].
  Case "m = O".
  {
    intros n H.
    destruct n as [|n'].
    SCase "n = O". reflexivity.
    SCase "n = S n'". inversion H.
  }
  Case "m = S m'".
  {
    intros n H.
    destruct n as [|n'].
    SCase "n = 0". inversion H.
    SCase "n = S n'".
    {
      apply f_equal.
      apply IHm'.
      inversion H.
      reflexivity.
    }
  }
Qed.

Theorem index_after_last :      (* list length is equal to the list boundary *)
  forall (n : nat) (X : Type) (xxs : list X),
    length xxs = n -> index n xxs = None.
Proof.
  intros n X xxs H.
  generalize dependent n.
  induction xxs as [|x xs].
  Case "xxs = nil".
  {
    intros n H.
    destruct n as [|n'].
    SCase "n = O". reflexivity.
    SCase "n = S n'". inversion H.
  }
  Case "xxs = cons x xs".
  {
    intros n H.
    destruct n as [|n'].
    SCase "n = 0". inversion H.
    SCase "n = S n'".
    {
      apply IHxs.
      rewrite <- pred_Sn.
      inversion H.
      reflexivity.
    }
  }
Qed.

Lemma eq_sub_S :
  forall n m : nat, S n = S m -> n = m.
Proof.
  intros n m H.
  apply eq_add_S in H.
  assumption.
Qed.

Theorem length_snoc3 :
  forall (n : nat) (X : Type) (v : X) (lst : list X),
    length lst = n -> length (snoc lst v) = S n.
Proof.
  intros n X v lst H.
  generalize dependent n.
  induction lst as [|x xs].
  Case "lst = []".
  {
    simpl.
    intros n H.
    rewrite <- H.
    reflexivity.
  }
  Case "lst = x::xs".
  {
    simpl.
    intros n H.
    Check eq_add_S.
    do 2 apply eq_add_S.
    Check pred_Sn.
    rewrite -> pred_Sn.
    simpl.
  }
  rewrite <- H.
  induction 
  unfold length.
  simpl.
  