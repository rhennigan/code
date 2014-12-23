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
        intro n.
      }
    }
    
  }