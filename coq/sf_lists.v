Require Export sf_induction.

Module NatList.

Inductive natprod : Type :=
  | pair : nat -> nat -> natprod.

Notation "( x , y )" := (pair x y).

Definition fst (p : natprod) : nat :=
  match p with
    | (a, b) => a
  end.
Definition snd (p : natprod) : nat :=
  match p with
    | (a, b) => b
  end.

Definition swap_pair (p : natprod) : natprod :=
  match p with
    | (a, b) => (b, a)
  end.

Theorem surjective_pairing' : 
  forall n m : nat, (n, m) = (fst (n, m), snd (n, m)).
Proof.
  reflexivity.
Qed.

Theorem surjective_pairing :
  forall p : natprod, p = (fst p, snd p).
Proof.
  intro p.
  destruct p as [n m].
  reflexivity.
Qed.

Theorem snd_fst_is_swap :
  forall p : natprod, (snd p, fst p) = swap_pair p.
Proof.
  intro p.
  destruct p as [n m].
  reflexivity.
Qed.

Theorem fst_swap_is_snd :
  forall p : natprod, fst (swap_pair p) = snd p.
Proof.
  intro p. destruct p as [n m]. reflexivity.
Qed.

Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint repeat (n count : nat) : natlist :=
  match count with
    | 0 => []
    | S c => n :: (repeat n c)
  end.

Eval compute in (repeat 5 3).

Fixpoint length (lst : natlist) : nat :=
  match lst with
    | [] => 0
    | x :: xs => 1 + (length xs)
  end.

Eval compute in (length (repeat 1 12)).

Fixpoint app (lst1 lst2 : natlist) : natlist :=
  match lst1 with
    | [] => lst2
    | x :: xs => x :: (app xs lst2)
  end.
Notation "x ++ y" := (app x y) (right associativity, at level 60).

Eval compute in ([1;2;3] ++ [4;5;6]).

Definition hd (default : nat) (lst : natlist) : nat :=
  match lst with
    | [] => default
    | x :: xs => x
  end.

Definition tl (lst : natlist) : natlist :=
  match lst with
    | [] => []
    | x :: xs => xs
  end.

Fixpoint nonzeros (lst : natlist) : natlist :=
  match lst with
    | [] => []
    | 0 :: xs => nonzeros xs
    | x :: xs => x :: (nonzeros xs)
  end.

Example test_nonzeros: nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof.
  simpl. reflexivity.
Qed.

Fixpoint oddmembers (l:natlist) : natlist :=
  match l with
    | [] => []
    | x :: xs => 
      match (oddb x) with
          | true => x :: (oddmembers xs)
          | false => oddmembers xs
      end
  end.

Example test_oddmembers: oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof.
  simpl. reflexivity.
Qed.

Fixpoint countoddmembers (l:natlist) : nat := length (oddmembers l).

Example test_countoddmembers1: countoddmembers [1;0;3;1;4;5] = 4.
Proof. simpl. reflexivity. Qed.

Example test_countoddmembers2: countoddmembers [0;2;4] = 0.
Proof. simpl. reflexivity. Qed.

Example test_countoddmembers3: countoddmembers nil = 0.
Proof. simpl. reflexivity. Qed.

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1, l2 with
    | [], [] => []
    | xs, [] => xs
    | [], ys => ys
    | x :: xs, y :: ys => x :: y :: (alternate xs ys)
  end.

Example test_alternate1: alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. simpl. reflexivity. Qed.

Example test_alternate2: alternate [1] [4;5;6] = [1;4;5;6].
Proof. simpl. reflexivity. Qed.

Example test_alternate3: alternate [1;2;3] [4] = [1;4;2;3].
Proof. simpl. reflexivity. Qed.

Example test_alternate4: alternate [] [20;30] = [20;30].
Proof. simpl. reflexivity. Qed.

Definition bag := natlist.

Fixpoint count (v:nat) (s:bag) : nat := 
  match s, v with
    | [], _ => 0
    | x :: xs, _ =>
      match (beq_nat x v) with
        | true => 1 + (count v xs)
        | false => count v xs
      end
  end.

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof. simpl. reflexivity. Qed.

Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof. simpl. reflexivity. Qed.

Definition sum : bag -> bag -> bag := app.

Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. simpl. reflexivity. Qed.

Definition add (v:nat) (s:bag) : bag := v :: s.

Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof. reflexivity. Qed.

Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof. reflexivity. Qed.

Definition member (v:nat) (s:bag) : bool := negb (beq_nat 0 (count v s)).

Example test_member1: member 1 [1;4;1] = true.
Proof. reflexivity. Qed.

Example test_member2: member 2 [1;4;1] = false.
Proof. reflexivity. Qed.

Theorem nil_app : 
  forall l : natlist, [] ++ l = l.
Proof.
  intro l.
  simpl.
  reflexivity.
Qed.

Theorem tl_length_pred : 
  forall L : natlist, pred (length L) = length (tl L).
Proof.
  intro L.
  induction L as [|x L'].
  Case "L = nil". simpl. reflexivity.
  Case "L = cons x L'".
  {
    simpl.
    reflexivity.
  }
Qed.
