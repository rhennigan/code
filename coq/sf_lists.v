Require Export sf_induction.

Module NatList.

Inductive natprod : Type :=
  | pair : nat -> nat -> natprod.

Check (pair 3 5).

