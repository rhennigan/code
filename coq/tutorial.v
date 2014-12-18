Section Minimal_Logic.

  (* Variables A B C : Prop. *)

  Lemma distr_imp : 
    forall A B C : Prop, (A -> B -> C) -> (A -> B) -> A -> C.
  Proof.
    auto.
  Qed.

  Print distr_imp.

  Lemma conj_commutative : 
    forall A B : Prop, B /\ A -> A /\ B.
  Proof.
    intros   suppose_A_Prop suppose_B_Prop.
    intro    suppose_B_and_A.
    destruct suppose_B_and_A as [B_True A_True].
    split.
    apply    A_True.
    apply    B_True.
  Qed.

  Print conj_commutative.

  Lemma disj_commutative : 
    forall A B : Prop, A \/ B -> B \/ A.
  Proof.
    intros suppose_A_Prop suppose_B_Prop. (* Let A, B be propositions *)
    intro  suppose_A_or_B.                (* Assume A \/ B, need to show B \/ A *)
    elim   suppose_A_or_B.                (* Break into two subproofs: A -> B \/ A and B -> B \/ A *)
    intro  suppose_A_True.                (* Assume A to prove first part, need to show B \/ A *)
    clear  suppose_A_or_B.                (* Don't need this assumption anymore *)
    right.                                (* Disjunction derivation rule for A in B \/ A *)
    apply  suppose_A_True.                (* A -> A, so done with first part *)
    intro  suppose_B_True.                (* Assume B to show B \/ A *)
    left.                                 (* This time we need the left side *)
    apply  suppose_B_True.                (* Done with second part, proof complete *)
  Qed.

  Print disj_commutative.

  Lemma conj_distributive : 
    forall A B C : Prop, A -> (B /\ C) -> (A -> B) /\ (A -> C).
  Proof.
    intros A_Prop B_Prop C_Prop.
    intro A_True.
    intro B_and_C_True.
    destruct B_and_C_True as [B_True C_True].
    clear A_True.
    split.
    intro A_True.
    apply B_True.
    intro A_True.
    apply C_True.
  Qed.

  Print conj_distributive.

  Lemma Peirce_neg : 
    forall A B : Prop, ~ (((A -> B) -> A) -> A) -> False.
  Proof.
    tauto.
  Qed.

  Print Peirce_neg.

  Theorem contrapositive : 
    forall P Q : Prop, (P -> Q) -> (~ Q -> ~ P).
  Proof.
    intros suppose_P_Prop suppose_Q_Prop.
    intros suppose_P_im_Q.
    intros suppose_Q_False.
    intros suppose_P_True.
    apply suppose_P_im_Q in suppose_P_True.
    unfold not in suppose_Q_False.
    apply suppose_Q_False in suppose_P_True.
    exact suppose_P_True.
  Qed.
  
Print contrapositive.

Lemma neg_implication : 
  forall A B : Prop, ~ (A -> B) -> A /\ ~ B.
Proof.
  intro A_im_B_Not_True.
  unfold not in suppose_not_A_im_B.
  apply contrapositive in suppose_not_A_im_B.
  
  apply contrapositive in suppose_not_A_im_B.

Lemma Peirce_neg_alt : ~ (((A -> B) -> A) -> A) -> False.
Proof.
  tauto.

Peirce_neg = 
fun H : ~ (((A -> B) -> A) -> A) =>
(fun H0 : False => (fun H1 : False => False_ind False H1) H0)
  ((fun H0 : ((A -> B) -> A) -> A => H H0)
     ((fun (H0 : A -> False) (H1 : (A -> B) -> A) =>
       (fun H2 : A =>
        (fun H3 : A => (fun H4 : False => False_ind A H4) (H0 H3)) H2)
         ((fun H2 : A -> B => H1 H2)
            ((fun (_ : B -> A) (H3 : A) =>
              (fun H4 : False => False_ind B H4) (H0 H3))
               (fun y : B => H1 (fun _ : A => y)))))
        (fun y : A => H (fun _ : (A -> B) -> A => y))))