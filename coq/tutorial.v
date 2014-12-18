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

Variables D E F : Prop.

Lemma easy_mode : D \/ E -> E \/ D.
Proof.
auto.