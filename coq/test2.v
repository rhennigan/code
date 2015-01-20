Module NatTest.

Inductive Number : Set :=
  | Zero : Number
  | Next : Number -> Number.

Notation "0" := Zero.

Fixpoint Addition (a : Number) (b : Number) : Number :=
  match a with
  | 0 => b
  | Next n => Next (Addition n b)
  end.

Notation "a + b" := (Addition a b).

Definition three := Next (Next (Next Zero)).
Definition two := Next (Next Zero).
Eval compute in (three + two).

Theorem Add_Zero_Left : forall (n : Number), 0 + n = n.
Proof.
  intro n.
  simpl.
  reflexivity.
Qed.

Theorem Add_Zero_Right : forall (n : Number), n + 0 = n.
Proof.
  intro n.
  induction n as [|k].
  {
    simpl.
    reflexivity.
  }
  {
    simpl.
    rewrite -> IHk.
    reflexivity.
  }
Qed.

Theorem Equal_Next_Up : 
  forall (a b : Number), (a = b) -> (Next a = Next b).
Proof.
  intros a b H.
  rewrite -> H.
  reflexivity.
Qed.

Theorem Equal_Next_Down :
  forall (a b : Number), (Next a = Next b) -> (a = b).
Proof.
  intros a.
  induction a as [|m].
  {
    intro b.
    induction b as [|n].
    {
      intro H.
      reflexivity.
    }
    {
      intro H.
      inversion H.
    }
  }
  {
    intro b.
    induction b as [|n].
    {
      intro H.
      inversion H.
    }
    {
      intro H.
      inversion H.
      reflexivity.
    }
  }
Qed.

Theorem Addition_Associative :
  forall (a b c : Number), (a + b) + c = a + (b + c).
Proof.
  intros a b c.
  induction a as [|n].
  {
    simpl.
    reflexivity.
  }
  {
    simpl.
    rewrite -> IHn.
    reflexivity.
  }
Qed.

Theorem Addition_Next_Distribution :
  forall (a b : Number), Next (a + b) = a + Next b.
Proof.
  intros a b.
  induction a as [|n].
  {
    simpl.
    reflexivity.
  }
  {
    simpl.
    rewrite -> IHn.
    reflexivity.
  }
Qed.

Theorem Addition_Commutative :
  forall (a b : Number), a + b = b + a.
Proof.
  intros a b.
  induction a as [|n].
  {
    simpl.
    rewrite -> Add_Zero_Right.
    reflexivity.
  }
  {
    simpl.
    rewrite -> IHn.
    rewrite -> Addition_Next_Distribution.
    reflexivity.
  }
Qed.