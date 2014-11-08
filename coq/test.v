Inductive day : Type :=
 | monday : day
 | tuesday : day
 | wednesday : day
 | thursday : day
 | friday : day
 | saturday : day
 | sunday : day.

Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.

Proof. 
simpl.
reflexivity.
Qed.

Inductive bool : Type :=
 | true : bool
 | false : bool.

Definition negb (b:bool) : bool :=
 match b with
 | true => false
 | false => true
 end.

Definition andb (b1 b2 : bool) : bool :=
 match b1 with
 | false => false
 | true => b2
 end.

Definition orb (b1 b2 : bool) : bool :=
 match b1 with
 | false => b2
 | true => true
 end.

(* Exercise *)

Definition nandb (b1 b2 : bool) : bool :=
 negb (andb b1 b2).

Example test_nandb1: (nandb true false) = true.
Proof. reflexivity. Qed.

Example test_nandb2: (nandb false false) = true.
Proof. reflexivity. Qed.

Example test_nandb3: (nandb false true) = true.
Proof. reflexivity. Qed.

Example test_nandb4: (nandb true true) = false.
Proof. reflexivity. Qed.

Check nandb.

Module Testing1.

Inductive nat : Type :=
 | O : nat
 | S : nat -> nat.

Definition predecessor (n:nat) : nat :=
 match n with
 | O => O
 | S n' => n'
 end.

End Testing1.

Check S.

Fixpoint evenb (n:nat) : bool :=
 match n with
 | O => true
 | S O => false
 | S (S n') => evenb n'
 end.

Definition oddb (n:nat) : bool :=
 negb (evenb n).

Module Testing2.

Fixpoint plus (n m : nat) : nat :=
 match n with
 | O => m
 | S n' => S (plus n' m)
 end.

Eval compute in (plus (S (S (S O))) (S (S O))).

Fixpoint mult (n m : nat) : nat :=
 match n with
 | O => O
 | S n' => plus m (mult n' m)
 end.

Eval compute in (mult (S (S (S O))) (S (S O))).

End Testing2.

(* test *)

Let f ≔ fun x ⇒ x.