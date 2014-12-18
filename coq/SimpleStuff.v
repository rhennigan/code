Module SimpleTesting.

Require Setoid.

Inductive empty_set : Set :=.

Inductive unit : Set :=
  tt : unit.

Inductive nat : Type :=
 | Z : nat
 | S : nat -> nat.

(* Addition *)
Fixpoint plus (n m : nat) : nat :=
 match n with
 | Z => m
 | S n' => S (plus n' m)
 end.

Inductive NatEq : nat -> nat -> Prop :=
  | NatRefl : forall x : nat, (NatEq x x)
  | NatSymm : forall (x y : nat), (NatEq x y) -> (NatEq y x)
  | NatTrns : forall (x y z : nat), (NatEq x y) -> (NatEq y z) -> (NatEq x z).

Lemma zero_eq_zero : NatEq Z Z.
Proof.
  apply NatRefl.
Qed.

Check nat.

Section Declaration.


(* Hypothesis Pos_n : (gt n 0). *)

(* Lemma sn_eq_sn (n m : nat) : (NatEq n m) -> (NatEq (S n) (S m)). *)
(* Proof. *)
(*   intros. *)


Lemma zero_plus (n : nat) : NatEq (plus Z n) n.
Proof.
  simpl.
  apply NatRefl.
Qed.

Lemma plus_zero (n : nat): NatEq (plus n Z) n.
Proof.
  induction n.
  simpl.
  apply NatRefl.
  simpl.
  auto.
  apply NatRefl.


(* Addition is commutative? *)
Theorem addition_commutative (m n : nat): (NatEq (plus n m) (plus m n)).
Proof.
induction n.
-simpl.

(* Equality *)
(* Fixpoint NatEq (n m : nat) : bool := *)
(*   match n, m with *)
(*     | O, O => true *)
(*     | O, _ => false *)
(*     | _, O => false *)
(*     | (S n'), (S m') => NatEq n' m' *)
(* (*   end. *) *)

(* Lemma plus_zero (n : nat): plus n O = n. *)
(* Proof. *)
(* induction n. *)
(* -simpl. reflexivity. *)
(* -simpl. rewrite IHn. reflexivity. *)
(* Qed. *)

(* Lemma plus_succ (n m : nat): S(plus n m) = plus n (S m). *)
(* Proof. *)
(* induction n. *)
(* -simpl. reflexivity. *)
(* -simpl. rewrite IHn. reflexivity. *)
(* Qed. *)

(* (* Addition is commutative *) *)
(* Theorem commutative_addition (n m : nat): plus n m = plus m n. *)
(* Proof. *)
(* induction n. *)
(* -simpl. rewrite plus_zero. reflexivity. *)
(* -simpl. rewrite IHn. rewrite plus_succ. reflexivity. *)
(* Qed. *)

(* Print commutative_addition. *)

(* Inductive List (A:Type) : Type := *)
(*  | Nil : List A *)
(*  | Cons : A -> List A -> List A. *)

(* Print list. *)

(* Eval compute in (cons 2 (cons 1 nil)). *)


End SimpleTesting.