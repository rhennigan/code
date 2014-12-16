Section Minimal_Logic.

Variables A B C : Prop.

Check (A -> B).

Lemma stupid : (A -> (B -> C)) -> (A -> B) -> (A -> C).
  intro H.
  intros H2 H3.
  apply H.
  exact H3.
  apply H2.
  exact H3.
Qed.

Check stupid.

Print stupid.

Lemma again : (A -> (B -> C)) -> (A -> B) -> (A -> C).
Proof.
  intros HABC HAB HA.
  apply HABC.
  exact HA.
  apply HAB.
  exact HA.
Qed.

Print again.

Inspect 4.

Lemma conj_commutative : A /\ B -> B /\ A.
Proof.
  intro AB.
  elim AB.
  split.
  exact H0.
  exact H.
Qed.

Print conj_commutative.