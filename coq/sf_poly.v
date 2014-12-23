Require Export sf_lists.

Inductive boollist : Type :=
| bool_nil : boollist
| bool_cons : bool -> boollist -> boollist.

Inductive list' (X : Type) : Type :=
| nil' : list' X
| cons' : X -> list' X -> list' X.

Check nil.
Check cons.
Check (list nat).

Fixpoint length {X : Type} (L:list X) : nat :=
  match L with
    | nil => 0
    | cons x xs => 1 + (length xs)
  end.

Example test_length1 :
  length (cons 1 (cons 2 nil)) = 2.
Proof. reflexivity. Qed.

Example test_length2 :
  length (cons true (cons false (cons true nil))) = 3.
Proof. reflexivity. Qed.

Fixpoint app {T:Type} (a b : list T) : (list T) :=
  match a with
    | nil => b
    | cons x xs => cons x (app xs b)
  end.

Check @nil.
Check @length.
Check @app.
Check @test_length2.

Fixpoint snoc {X:Type} (l:list X) (v:X) : (list X) :=
  match l with
    | nil => cons v nil
    | cons x xs => cons x (snoc xs v)
  end.

Eval compute in (snoc (cons 1 (cons 2 nil)) 5).

Notation "x :: y" := 
  (cons x y) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := 
  (app x y) (at level 60, right associativity).

Eval compute in ([1;2;3;4;5] ++ [6;7;8;9;10]).

Definition list123''' := [1; 2; 3].

Check ([3 + 4] ++ nil).

Fixpoint repeat {X : Type} (n : X) (count : nat) : list X :=
  match count with
    | 0 => []
    | S c => n :: (repeat n c)
  end.

Example test_repeat1:
  repeat true 2 = cons true (cons true nil).
Proof. reflexivity. Qed.

Theorem nil_app : forall X:Type, forall l:list X,
  app [] l = l.
Proof.
  intros X l.
  reflexivity.
Qed.

Theorem rev_snoc : ∀X : Type,
                     ∀v : X,
                     ∀s : list X,
  rev (snoc s v) = v :: (rev s).
Proof.
  (* FILL IN HERE *) Admitted.

Theorem rev_involutive : ∀X : Type, ∀l : list X,
  rev (rev l) = l.
Proof.
(* FILL IN HERE *) Admitted.

Theorem snoc_with_append : ∀X : Type,
                         ∀l1 l2 : list X,
                         ∀v : X,
  snoc (l1 ++ l2) v = l1 ++ (snoc l2 v).
Proof.
  (* FILL IN HERE *) Admitted.