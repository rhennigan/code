Section Minimal_Logic.

  Variables A B C : Prop.

  Lemma distr_imp : (A -> B -> C) -> (A -> B) -> A -> C.
  Proof.
    auto.
  Qed.

  Print distr_imp.

  Lemma conj_commutative : A /\ B -> B /\ A.
  Proof.
    intros.
    elim H.
    split.
    apply H1.
    apply H0.
  Qed.

Print conj_commutative.

Check conj.

Print conj.

Lemma disj_commutative : A \/ B -> B \/ A.
Proof.
intro supposeAorB.              (* Assume A \/ B, 
                                   Need to show B \/ A *)
elim supposeAorB.               (* Break into two subproofs: A -> B \/ A and B -> B \/ A *)
intro supposeA.                 (* Assume A to prove first part *)
clear supposeAorB.              (* Don't need this assumption anymore *)
right.                          (* A gave us B \/ A, so  *)
apply supposeA.
intro supposeB.
left.
apply supposeB.
Qed.

Check disj_commutative.
Print disj_commutative.