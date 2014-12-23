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
  induction n as [| n'].
  Case "n = O".
  {
    intro H.
    unfold impossible in H.
    simpl in H.
    inversion H.
  }
  Case "n = S n'".
  {
    intro H.
    unfold impossible in *. simpl in *.
    remember (beq_nat n' 3) as e3. destruct e3.
    {
      remember (beq_nat n' 5) as e5. destruct e5.
      {
        assert (H_refl : true = true). reflexivity.
        apply IHn' in H_refl.
        assumption.
      }
      {
        remember (beq_nat n' 2) as e2. destruct e2.
        {
          remember (beq_nat n' 4) as e4. destruct e4.
          {
            assert (H_2_4 : beq_nat n' 2 = beq_nat n' 4). rewrite <- Heqe2. rewrite <- Heqe4. reflexivity.
            inversion H_2_4.
          }
        }
      }
    }
    
  }