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

Fixpoint rev {X : Type} (l : list X) : list X :=
  match l with
    | [] => []
    | x :: xs => snoc (rev xs) x
  end.

Example test_repeat1:
  repeat true 2 = cons true (cons true nil).
Proof. reflexivity. Qed.

Theorem nil_app : 
  forall X : Type, forall l : list X, app [] l = l.
Proof.
  intros X l.
  reflexivity.
Qed.

Theorem rev_snoc : 
  forall X : Type, forall v : X, forall s : list X,
    rev (snoc s v) = v :: (rev s).
Proof.
  intros X v s.
  induction s as [|x xs]. reflexivity.
  simpl. rewrite -> IHxs. reflexivity.
Qed.

Theorem rev_involutive : 
  forall X : Type, forall l : list X,
    rev (rev l) = l.
Proof.
  intros X l.
  induction l as [|x xs]. reflexivity.
  simpl. 
  rewrite -> rev_snoc. 
  rewrite -> IHxs.
  reflexivity.
Qed.

Theorem snoc_with_append : 
  forall X : Type, forall lst1 lst2 : list X, forall v : X,
    snoc (lst1 ++ lst2) v = lst1 ++ (snoc lst2 v).
Proof.
  intros X lst1 lst2 v.
  induction lst1 as [|x xs]. reflexivity.
  simpl. rewrite -> IHxs. reflexivity.
Qed.

Inductive prod (X Y : Type) : Type :=
  pair : X -> Y -> prod X Y.

Arguments pair {X} {Y} _ _.

Check @prod.

Notation "( x , y )" := (pair x y).

Notation "X × Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X × Y) : X :=
  match p with (x,y) => x end.

Definition snd {X Y : Type} (p : X × Y) : Y :=
  match p with (x,y) => y end.

Check (5, 3).