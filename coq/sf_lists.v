Require Export sf_induction.

Module NatList.

Inductive natprod : Type :=
  | pair : nat -> nat -> natprod.

Notation "( x , y )" := (pair x y).

Definition fst (p : natprod) : nat :=
  match p with
    | (a, b) => a
  end.
Definition snd (p : natprod) : nat :=
  match p with
    | (a, b) => b
  end.

Definition swap_pair (p : natprod) : natprod :=
  match p with
    | (a, b) => (b, a)
  end.

Theorem surjective_pairing' : 
  forall n m : nat, (n, m) = (fst (n, m), snd (n, m)).
Proof.
  reflexivity.
Qed.

Theorem surjective_pairing :
  forall p : natprod, p = (fst p, snd p).
Proof.
  intro p.
  destruct p as [n m].
  reflexivity.
Qed.

Theorem snd_fst_is_swap :
  forall p : natprod, (snd p, fst p) = swap_pair p.
Proof.
  intro p.
  destruct p as [n m].
  reflexivity.
Qed.

Theorem fst_swap_is_snd :
  forall p : natprod, fst (swap_pair p) = snd p.
Proof.
  intro p. destruct p as [n m]. reflexivity.
Qed.