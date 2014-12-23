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

Fixpoint length (X:Type) (L:list X) : nat :=
  match L with
    | nil => 0
    | cons x xs => 1 + (length X xs)
  end.

Example test_length1 :
  length nat (cons 1 (cons 2 nil)) = 2.
Proof. reflexivity. Qed.

Example test_length2 :
  length bool (cons true (cons false (cons true nil))) = 3.
Proof. reflexivity. Qed.

Fixpoint app T l__1 l__2 : (list T) :=
  match l__1 with
    | nil => l__2
    | cons x xs => cons x (app T xs l__2)
  end.

Check app.

Fixpoint snoc (X:Type) (l:list X) (v:X) : (list X) :=
  match l with
    | nil => cons v nil
    | cons x xs => cons x (snoc X xs v)
  end.

Eval compute in (snoc nat (cons 1 (cons 2 nil)) 5).