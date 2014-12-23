(* Inductive day : Type := *)
(* | monday : day *)
(* | tuesday : day *)
(* | wednesday : day *)
(* | thursday : day *)
(* | friday : day *)
(* | saturday : day *)
(* | sunday : day. *)

(* Definition next_weekday (d : day) : day := *)
(*   match d with *)
(*     | monday => tuesday *)
(*     | tuesday => wednesday *)
(*     | wednesday => thursday *)
(*     | thursday => friday *)
(*     | _ => monday *)
(*   end. *)

(* Eval compute in (next_weekday friday). *)
(* Eval compute in (next_weekday (next_weekday saturday)). *)

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
Notation "x × y" := (mult x y) (at level 40, left associativity) : nat_scope.

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

Eval compute in (blt_nat 5 3).
Eval compute in (blt_nat 3 3).
Eval compute in (blt_nat 2 3).

Fixpoint ble_nat (a b : nat) : bool :=
  match a, b with
    | S x, S y => ble_nat x y
    | O, _ => true
    | _, _ => false
  end.

Fixpoint bge_nat (a b : nat) : bool :=
  match a, b with
    | S x, S y => bge_nat x y
    | _, O => true
    | _, _ => false
  end.

Eval compute in (ble_nat 5 3).
Eval compute in (ble_nat 3 3).
Eval compute in (ble_nat 2 3).

Example test_blt_nat1: (blt_nat 2 2) = false.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_blt_nat2: (blt_nat 2 4) = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_blt_nat3: (blt_nat 4 2) = false.
Proof.
  simpl.
  reflexivity.
Qed.

Theorem plus_0_n : forall n : nat, 0 + n = n.
Proof.
  intro.
  compute.
  reflexivity.
Qed.

Print plus_0_n.

Theorem plus_1_L : forall n : nat, 1 + n = S n.
Proof.
  intro.
  compute.
  reflexivity.
Qed.

Theorem mult_0_L : forall n : nat, 0 × n = 0.
Proof.
  intro.
  compute.
  reflexivity.
Qed.

Theorem plus_id_example : forall m n : nat, m = n -> m + m = n + n.
Proof.
  intro m.
  intro n.
  intro m_eq_n.
  rewrite -> m_eq_n.
  reflexivity.
Qed.

Theorem plus_id_exercise : 
  forall m n o : nat, (n = m) -> (m = o) -> (n + m = m + o).
Proof.
  intros m n o.
  intro H_neqm.
  intro H_meqo.
  rewrite -> H_neqm.
  rewrite <- H_meqo.
  reflexivity.
Qed.

Theorem mult_0_plus : forall n m : nat, (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_0_n.
  reflexivity.
Qed.

Theorem mult_S_1 : forall n m : nat, m = S n -> m * (1 + n) = m * m.
Proof.
  intros n m.
  intro H_m_eq_Sn.
  rewrite -> plus_1_L.
  rewrite <- H_m_eq_Sn.
  reflexivity.
Qed.

Theorem plus_1_neq_0 : 
  forall n : nat, 
    beq_nat (n + 1) 0 = false.
Proof.
  intro n.
  destruct n as [ | m].
  compute.
  reflexivity.
  compute.
  reflexivity.
Qed.

Print plus_1_neq_0.

Theorem negb_involutive :
  forall b : bool,
    negb (negb b) = b.
Proof.
  intro b.
  destruct b.
  {
    compute.
    reflexivity.
  }
  {
    compute.
    reflexivity.
  }
Qed.

Theorem zero_nbeq_plus_1 : 
  forall n : nat,
    beq_nat 0 (n + 1) = false.
Proof.
  intro n.
  destruct n as [|m].
  { (* n = 0 *)
    compute.
    reflexivity.
  }
  { (* n = S m *)
    compute.
    reflexivity.
  }
Qed.

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool), (forall (x : bool), f x = x) -> forall (b : bool), f (f b) = b.
Proof.
  intro f.
  intro H_fx_eq_x.
  intro b.
  rewrite -> H_fx_eq_x.
  rewrite -> H_fx_eq_x.
  reflexivity.
Qed.

Theorem negation_fn_applied_twice :
  forall (f : bool -> bool), (forall (x : bool), f x = negb x) -> forall (b : bool), f (f b) = b.
Proof.
  intro f.
  intro H_fx_neq_x.
  intro b.
  rewrite -> H_fx_neq_x.
  rewrite -> H_fx_neq_x.
  destruct b.
  { 
    compute.
    reflexivity. 
  }
  { 
    compute.
    reflexivity.
  }
Qed.

Theorem andb_eq_orb :
  forall (b c : bool),
    (andb b c = orb b c) -> 
    b = c.
Proof.
  intros b c.
  destruct b.
  {
    destruct c.
    {
      compute.
      reflexivity.
    }
    {
      compute.
      intro H.
      rewrite -> H.
      reflexivity.
    }
  }
  {
    destruct c.
    {
      compute.
      intro H.
      rewrite -> H.
      reflexivity.
    }
    {
      compute.
      reflexivity.
    }
  }
Qed.

Inductive bin : Type :=
| S0 : bin
| S1 : bin -> bin 
| S2 : bin -> bin.

Fixpoint bin_inc (b : bin) : bin :=
  match b with
    | S0 => S2 S0
    | S1 n => S2 n
    | S2 n => S1 (bin_inc n)
  end.

Eval compute in (bin_inc S0).
Eval compute in (bin_inc (bin_inc S0)).
Eval compute in (bin_inc (bin_inc (bin_inc S0))).
Eval compute in (bin_inc (bin_inc (bin_inc (bin_inc S0)))).
Eval compute in (bin_inc (bin_inc (bin_inc (bin_inc (bin_inc S0))))).

Fixpoint bin_to_nat (b : bin) : nat :=
  match b with
    | S0 => 0
    | S1 n => 2 * (bin_to_nat n)
    | S2 n => 1 + (2 * (bin_to_nat n))
  end.

Eval compute in (bin_to_nat (bin_inc S0)).
Eval compute in (bin_to_nat (bin_inc (bin_inc S0))).
Eval compute in (bin_to_nat (bin_inc (bin_inc (bin_inc S0)))).
Eval compute in (bin_to_nat (bin_inc (bin_inc (bin_inc (bin_inc S0))))).
Eval compute in (bin_to_nat (bin_inc (bin_inc (bin_inc (bin_inc (bin_inc S0)))))).

Fixpoint nat_to_bin (n : nat) : bin :=
  match n with
    | O => S0
    | S n' => bin_inc (nat_to_bin n')
  end.

Theorem bin_correct : forall n : nat, forall b : bin, (nat_to_bin n = b) -> (bin_to_nat b = n).
Proof.
  simple induction n.
  {
    simple induction b.
    {
      auto.
    }
    {
      intro b2.
      intro H2.
      intro H3.
      rewrite <- H3.
      auto.
    }
    {
      intro b3.
      intro H4.
      intro H5.
      rewrite <- H5.
      auto.
    }
  }
Abort.                          (* Proof appears in sf_induction.v *)


(* Can't be defined *)
(* Fixpoint countdown (n c : nat) : nat :=  *)
(*   match n with *)
(*     | 0 => c *)
(*     | _ => match (evenb n) with *)
(*             | true => countdown (n + 1) (c + 1) *)
(*             | false => countdown (n - 3) (c + 1) *)
(*       end *)
(*   end. *)

