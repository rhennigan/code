Module SimpleTesting.

Inductive nat : Type :=
 | O : nat
 | S : nat -> nat.

(* Addition *)
Fixpoint plus (n m : nat) : nat :=
 match n with
 | O => m
 | S n' => S (plus n' m)
 end.

(* Equality *)
Fixpoint NatEq (n m : nat) : bool :=
  match n, m with
    | O, O => true
    | O, _ => false
    | _, O => false
    | (S n'), (S m') => NatEq n' m'
  end.

Lemma plus_zero (n : nat): plus n O = n.
Proof.
induction n.
-simpl. reflexivity.
-simpl. rewrite IHn. reflexivity.
Qed.

Lemma plus_succ (n m : nat): S(plus n m) = plus n (S m).
Proof.
induction n.
-simpl. reflexivity.
-simpl. rewrite IHn. reflexivity.
Qed.

(* Addition is commutative *)
Theorem commutative_addition (n m : nat): plus n m = plus m n.
Proof.
induction n.
-simpl. rewrite plus_zero. reflexivity.
-simpl. rewrite IHn. rewrite plus_succ. reflexivity.
Qed.

Print commutative_addition.

Inductive List (A:Type) : Type :=
 | Nil : List A
 | Cons : A -> List A -> List A.

Print list.

Eval compute in (cons 2 (cons 1 nil)).

Inductive mult (n m : nat) : nat :=
  match n, m with 
      | O, _ ⇒ O

End SimpleTesting.