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
          SSSSCase "b = S b'". apply (IHa' H') with (m := b').
        }
      }
    }
    
  }