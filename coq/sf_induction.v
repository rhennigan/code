Require Export sf_basic.

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

Theorem andb_true_elim1 : forall a b : bool, andb a b = true -> a = true.
Proof.
  intros a b.
  intro H.
  destruct a.
  Case "a = true". 
  {
    simpl.
    reflexivity. 
  }
  Case "a = false".
  {
    rewrite <- H.
    simpl.
    reflexivity.
  }
Qed.

Theorem andb_true_elim2 : forall a b : bool, andb a b = true -> b = true.
Proof.
  intros a b.
  intro H.
  destruct b.
  Case "b = true".
  {
    simpl.
    reflexivity.
  }
  Case "b = false".
  {
    rewrite <- H.
    destruct a.
    SCase "a = true".
    {
      simpl.
      reflexivity.
    }
    SCase "a = false".
    {
      simpl.
      reflexivity.
    }
  }
Qed.

Theorem plus_0_r : forall n : nat, n + 0 = n.
Proof.
  intro n.
  induction n as [| k].
  Case "n = 0".
  {
    simpl.
    reflexivity.
  }
  Case "n = S k".
  {
    simpl.
    rewrite -> IHk.
    reflexivity.
  }
Qed.

Theorem minus_diag : forall n : nat, minus n n = 0.
Proof.
  intro n.
  induction n as [| m].
  Case "n = 0".
  {
    reflexivity.
  }
  Case "n = S m".
  {
    rewrite <- IHm.
    reflexivity.
  }
Qed.

Theorem mult_0_r : forall n : nat, n * 0 = 0.
Proof.
  intro n.
  induction n as [| m].
  Case "n = 0". reflexivity.
  Case "n = S m".
  {
    simpl.
    rewrite -> IHm.
    reflexivity.
  }
Qed.

Theorem plus_n_Sm : forall n m : nat, S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [| k].
  Case "n = 0". simpl. reflexivity.
  Case "n = S k".
  {
    simpl.
    rewrite <- IHk.
    reflexivity.
  }
Qed.

Theorem plus_comm : forall n m : nat, n + m = m + n.
Proof.
  intros n m.
  induction n as [| k].
  Case "n = 0". simpl. rewrite -> plus_0_r. reflexivity.
  Check plus_0_r.