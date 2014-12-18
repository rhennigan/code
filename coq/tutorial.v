Section Minimal_Logic.

  Variables A B C : Prop.

  Lemma distr_imp : (A -> B -> C) -> (A -> B) -> A -> C.
  Proof.
    auto.
  Qed.

  Lemma conj_commutative : B /\ A -> A /\ B.
  Proof.
    intro    suppose_B_and_A.
    destruct suppose_B_and_A as [B_True A_True].
    split.
    apply    A_True.
    apply    B_True.
  Qed.

  Lemma disj_commutative : A \/ B -> B \/ A.
  Proof.
    intro supposeAorB.              (* Assume A \/ B, need to show B \/ A *)
    elim supposeAorB.               (* Break into two subproofs: A -> B \/ A and B -> B \/ A *)
    intro supposeA.                 (* Assume A to prove first part, need to show B \/ A *)
    clear supposeAorB.              (* Don't need this assumption anymore *)
    right.                          (* Disjunction derivation rule for A in B \/ A *)
    apply supposeA.                 (* A -> A, so done with first part *)
    intro supposeB.                 (* Assume B to show B \/ A *)
    left.                           (* This time we need the left side *)
    apply supposeB.                 (* Done with second part, proof complete *)
  Qed.

  Check disj_commutative.
  Print disj_commutative.
