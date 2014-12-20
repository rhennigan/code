Section Basics.
  Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

  Definition next_weekday (d : day) : day :=
    match d with
      | monday => tuesday
      | tuesday => wednesday
      | wednesday => thursday
      | thursday => friday
      | _ => monday
    end.

  Eval compute in (next_weekday friday).
  Eval compute in (next_weekday (next_weekday saturday)).

  Inductive bool : Type :=
  | true : bool
  | false : bool.

  Definition negb (b : bool) : bool :=
    match b with
      | false => true
      | true => false
    end.

  Definition andb (a b : bool) : bool :=
    match a, b with
      | true, true => true
      | _, _ => false
    end.

  Definition orb (a b : bool) : bool :=
    match a, b with
      | true, _ => true
      | _, true => true
      | _, _ => false
    end.

  Definition nandb (a b : bool) : bool :=
    match a, b with
      | false, _ => true
      | _, false => true
      | _, _ => false
    end.

  Example test_nandb1: (nandb true false) = true.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example test_nandb2: (nandb false false) = true.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example test_nandb3: (nandb false true) = true.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example test_nandb4: (nandb true true) = false.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Definition andb3 (a b c : bool) : bool := andb a (andb b c).

  Example test_andb31: (andb3 true true true) = true.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example test_andb32: (andb3 false true true) = false.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example test_andb33: (andb3 true false true) = false.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example test_andb34: (andb3 true true false) = false.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Check negb.
End Basics.

Module NatTest.

  Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.
  
  Definition pred (n : nat) : nat :=
    match n with
      | O => O
      | S m => m
    end.

End NatTest.

Definition minustwo (n : nat) : nat :=
  match n with
    | S (S m) => m
    | _ => O
  end.

Check (S (S (S (S O)))).
Eval compute in (minustwo 4).

Fixpoint evenb (n : nat) : bool :=
  match n with
    | O => true
    | S O => false
    | S (S m) => evenb m
  end.

Definition oddb (n : nat) : bool := negb (evenb n).

Example test_oddb1: (oddb (S O)) = true.
Proof.
  reflexivity.
Qed.

Example test_oddb2: (oddb (S (S (S (S O))))) = false.
Proof. 
  reflexivity. 
Qed.

Module NatTest2.

  Fixpoint plus (a b : nat) : nat :=
    match a, b with
      | O, y => y
      | S x, y => S (plus x y)
    end.

  Eval compute in (plus (S (S (S O))) (S (S O))).

  Fixpoint mult (a b : nat) : nat :=
    match a, b with
      | O, y => O
      | S x, y => plus y (mult x y)
    end.

  Eval compute in (mult (S (S (S O))) (S (S O))).

  Fixpoint minus (a b : nat) : nat :=
    match a, b with
      | O, _ => O
      | x, O => x
      | S x, S y => minus x y
    end.

  Eval compute in (minus 12 8).

End NatTest2.

Fixpoint exp (b p : nat) : nat :=
  match b, p with
    | _, O => S O
    | x, S O => x
    | x, S y => mult x (exp x y)
  end.

Eval compute in (exp 2 3).
Eval compute in (exp 10 4).

Fixpoint factorial (n : nat) : nat :=
  match n with
    | O => S O
    | S m => mult (S m) (factorial m)
  end.

Eval compute in (factorial 1).
Eval compute in (factorial 2).
Eval compute in (factorial 3).
Eval compute in (factorial 4).

Example test_factorial1: (factorial 3) = 6.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_factorial2: (factorial 5) = (mult 10 12).
Proof.
  simpl.
  reflexivity.
Qed.

Notation "x + y" := (plus x y) (at level 50, left associativity) : nat_scope.
Notation "x - y" := (minus x y) (at level 50, left associativity) : nat_scope.
Notation "x * y" := (mult x y) (at level 40, left associativity) : nat_scope.

Check ((0 + 1) + 1).
Eval compute in ((0 + 1) + 1).

Fixpoint beq_nat (a b : nat) : bool :=
  match a, b with
    | O, O => true
    | S x, S y => beq_nat x y
    | _, _ => false
  end.

Eval compute in (beq_nat 5 3).

Fixpoint blt_nat (a b : nat) : bool :=
  match a, b with
    | O, S _ => true
    | S x, S y => blt_nat x y
    | _, _ => false
  end.

Fixpoint bgt_nat (a b : nat) : bool :=
  match a, b with
    | S _, O => true
    | S x, S y => bgt_nat x y
    | _, _ => false
  end.