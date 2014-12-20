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

Definition evenb (n : nat) : bool :=
  match n with
    | O => true
    | S _ => false
    | S (S m) => evenb m
  end.