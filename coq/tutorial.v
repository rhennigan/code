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