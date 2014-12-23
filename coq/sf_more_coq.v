Require Export sf_poly.

Theorem beq_nat_eq : forall n m, true = beq_nat n m -> n = m.
Proof.
  intros n m H.
  induction n as [| n'].
  Case "n = O".
  {
    destruct m as [| m'].
  }