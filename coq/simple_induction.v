Module NatTesting.

Inductive nat : Set := 
  | Z : nat
  | S : nat -> nat.

Fixpoint add (a : nat) (b : nat) :=
  match a with
    | Z => b
    | S n => add n (S b)
  end.

Eval compute in (add (S (S (S Z))) (S (S Z))).

Theorem add_associative :
  forall (a b c : nat), add (add a b) c = add a (add b c).
Proof.
  intro a.
  induction a as [|n].
  {
    simpl.
    reflexivity.
  }
  {
    intros b.
    induction b as [|m].
    {
      intro c.
      simpl.
      apply IHn.
    }
    {
      intro c.
      simpl.
      inversion c as [|k].
      {
        inversion.
      }
      {

      }
    }
  }