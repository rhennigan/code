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

(* zip *)
Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y) : list (X × Y) :=
  match (lx, ly) with
    | ([], _) => []
    | (_, []) => []
    | (x::xs, y::ys) => (x,y) :: (combine xs ys)
  end.

Eval compute in (combine [1;2] [false;false;true;true]).

Fixpoint split {X Y : Type} (lxy : list (X × Y)) : (list X) × (list Y) :=
  match lxy with
    | [] => ([], [])
    | (x, y) :: xys => 
      let (xs, ys) := split xys in
      (x :: xs, y :: ys)
  end.

Eval compute in (split [(1,false);(2,false)]).

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof. reflexivity. Qed.

Inductive option (X:Type) : Type :=
  | Some : X -> option X
  | None : option X.

Arguments Some {X} _.
Arguments None {X}.

Fixpoint index {X : Type} (n : nat) (l : list X) : option X :=
  match l with
    | [] => None
    | a :: l' => if beq_nat n O then Some a else index (pred n) l'
  end.

Example test_index1 : index 0 [4;5;6;7] = Some 4.
Proof. reflexivity. Qed.

Example test_index2 : index 1 [[1];[2]] = Some [2].
Proof. reflexivity. Qed.

Example test_index3 : index 2 [true] = None.
Proof. reflexivity. Qed.

Definition hd_opt {X : Type} (l : list X) : option X :=
  match l with
    | [] => None
    | x::xs => Some x
  end.

Check @hd_opt.

Example test_hd_opt1 : hd_opt [1;2] = Some 1.
Proof. reflexivity. Qed.

Example test_hd_opt2 : hd_opt [[1];[2]] = Some [1].
Proof. reflexivity. Qed.

Definition doit3times {X:Type} (f:X -> X) (x:X) : X :=
  (f (f (f x))).

Check @doit3times.

Example test_doit3times: doit3times minustwo 9 = 3.
Proof. reflexivity. Qed.

Example test_doit3times': doit3times negb true = false.
Proof. reflexivity. Qed.

Definition prod_curry {X Y Z : Type}
           (f : X × Y -> Z) (x : X) (y : Y) : Z := f (x, y).

Definition prod_uncurry {X Y Z : Type}
           (f : X -> Y -> Z) (p : X × Y) : Z := f (fst p) (snd p).

Check @prod_curry.
Check @prod_uncurry.

Theorem uncurry_curry : 
  forall (X Y Z : Type) (f : X -> Y -> Z) (x : X) (y : Y),
    prod_curry (prod_uncurry f) x y = f x y.
Proof.
  intros X Y Z f x y.
  compute. 
  reflexivity.
Qed.

Theorem curry_uncurry :
  forall (X Y Z : Type) (f : (X × Y) -> Z) (p : (X × Y)),
    prod_uncurry (prod_curry f) p = f p.
Proof.
  intros X Y Z f p.
  compute.
  destruct p.
  reflexivity.
Qed.

Fixpoint filter {X:Type} (test: X -> bool) (l:list X) : (list X) :=
  match l with
      | [] => []
      | x :: xs => 
        if test x
        then x :: filter test xs
        else filter test xs
  end.

Print filter.

Example test_filter1: filter evenb [1;2;3;4] = [2;4].
Proof. reflexivity. Qed.

Definition length_is_1 {X : Type} (l : list X) : bool :=
  beq_nat (length l) 1.

Example test_filter2:
  filter length_is_1 [[1;2];[3];[4];[5;6;7];[];[8]] = [[3];[4];[8]].
Proof. reflexivity. Qed.

Definition countoddmembers' (l:list nat) : nat :=
  length (filter oddb l).

Example test_countoddmembers'1: countoddmembers' [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers'2: countoddmembers' [0;2;4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers'3: countoddmembers' nil = 0.
Proof. reflexivity. Qed.

Example test_anon_fun':
  doit3times (fun n => n × n) 2 = 256.
Proof. reflexivity. Qed.

Example test_filter2':
  filter (fun l => beq_nat (length l) 1) 
         [[1;2];[3];[4];[5;6;7];[];[8]] = [[3];[4];[8]].
Proof. reflexivity. Qed.



Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun n => (andb (evenb n) (bgt_nat n 7))) l.

Eval compute in (filter_even_gt7 [1;2;6;9;10;3;12;8]).

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. reflexivity. Qed.

Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof. reflexivity. Qed.

Fixpoint partition {X:Type} (p:X -> bool) (lst:list X) : 
  ((list X) × (list X)) :=
  match lst with
    | [] => ([],[])
    | v :: lst' => 
      let (xs, ys) := partition p lst' in
      if p v
      then (v :: xs, ys)
      else (xs, v :: ys)
  end.

Eval compute in (partition oddb [1;2;3;4;5]).

Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed.

Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.

Fixpoint map {X Y:Type} (f:X -> Y) (lst:list X) : (list Y) := 
  match lst with
    | [] => []
    | x :: xs => (f x) :: (map f xs)
  end.

Example test_map1: map (plus 3) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.

Example test_map2: map oddb [2;1;2;5] = [false;true;false;true].
Proof. reflexivity. Qed.

Example test_map3:
  map (fun n => [evenb n; oddb n]) [2;1;2;5]
  = [[true;false];[false;true];[true;false];[false;true]].
Proof. reflexivity. Qed.

Lemma map_snoc :
  forall (X Y : Type) (f : X -> Y) (lst : list X) (v : X),
    map f (snoc lst v) = snoc (map f lst) (f v).
Proof.
  intros X Y f lst v.
  induction lst as [|x xs].
  Case "lst = nil".
  {
    simpl.
    reflexivity.
  }
  Case "lst = x :: xs".
  {
    simpl.
    rewrite -> IHxs.
    reflexivity.
  }
Qed.

Theorem map_rev :
  forall (X Y : Type) (f : X -> Y) (lst : list X),
    map f (rev lst) = rev (map f lst).
Proof.
  intros X Y f lst.
  induction lst as [|x xs].
  Case "lst = nil".
  {
    simpl.
    reflexivity.
  }
  Case "lst = x :: xs".
  {
    simpl.
    rewrite -> map_snoc.
    rewrite -> IHxs.
    reflexivity.
  }
Qed.

Fixpoint flat_map {X Y : Type} (f : X -> list Y) (lst : list X) : (list Y) :=
  match lst with
    | [] => []
    | x :: xs => (f x) ++ (flat_map f xs)
  end.

Eval compute in (flat_map (fun n => [n;n+1;n+2;n+3;n+4]) [0;5;10]).

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4] = [1;1;1;5;5;5;4;4;4].
Proof. reflexivity. Qed.

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X) : option Y :=
  match xo with
    | None => None
    | Some x => Some (f x)
  end.

(* Definition flip_args {X Y Z : Type} (f : X -> Y -> Z) : (Y -> X -> Z) := *)
(*   fun x y => f y x. *)

(* Check @flip_args. *)

(* Fixpoint foldl_aux {X Y : Type} (f : X -> Y -> Y) (l : list X) (b : Y) : Y := *)
(*   match l with *)
(*     | [] => b *)
(*     | x :: xs => foldl_aux f xs (f x b) *)
(*   end. *)

(* Definition foldl {X Y : Type} (f : X -> Y -> Y) (l : list X) (b : Y) : Y := *)
(*   foldl_aux (flip_args f) l b. *)

Fixpoint foldr {X Y : Type} (f : X -> Y -> Y) (l : list X) (b : Y) : Y :=
  match l with
    | [] => b
    | x :: xs => f x (foldr f xs b)
  end.

Definition fold {X Y : Type} (f : X -> Y -> Y) (l : list X) (b : Y) : Y := foldr f l b.

(* Eval compute in (foldl plus [1;2;3;4] 0). *)
Eval compute in (foldr plus [1;2;3;4] 0).

(* Eval compute in (foldl (flip_args (fun x y => x ++ y)) [[1];[2];[3];[4]] []). *)
Eval compute in (foldr (fun x y => x ++ y) [[1];[2];[3];[4]] []).

Check (fold andb).

Example fold_example1 : fold mult [1;2;3;4] 1 = 24.
Proof. reflexivity. Qed.

Example fold_example2 : fold andb [true;true;false;true] true = false.
Proof. reflexivity. Qed.

Example fold_example3 : fold app [[1];[];[2;3];[4]] [] = [1;2;3;4].
Proof. reflexivity. Qed.

Definition constfun {X : Type} (x : X) : nat -> X :=
  fun (k : nat) => x.

Definition ftrue := constfun true.

Example constfun_example1 : ftrue 0 = true.
Proof. reflexivity. Qed.

Example constfun_example2 : (constfun 5) 99 = 5.
Proof. reflexivity. Qed.

Definition override {X : Type} (f : nat -> X) (k : nat) (x : X) : nat -> X :=
  fun (k' : nat) => if beq_nat k k' then x else f k'.

Check @override.

Definition fmostlytrue := override (override ftrue 1 false) 3 false.

Example override_example1 : fmostlytrue 0 = true.
Proof. reflexivity. Qed.

Example override_example2 : fmostlytrue 1 = false.
Proof. reflexivity. Qed.

Example override_example3 : fmostlytrue 2 = true.
Proof. reflexivity. Qed.

Example override_example4 : fmostlytrue 3 = false.
Proof. reflexivity. Qed.

Eval compute in (map fmostlytrue [1;2;3;4;5;6;7;8;9;10]).

Theorem override_example :
  forall (b : bool), (override (constfun b) 3 true) 2 = b.
Proof.
  intro b.
  destruct b.
  unfold override.
  simpl.
  unfold constfun.
  reflexivity.
  unfold override.
  simpl.
  unfold constfun.
  reflexivity.
Qed.

Definition plus3 := (fun x => 3 + x).

Theorem unfold_example : 
  forall (m n : nat), 3 + n = m -> plus3 n + 1 = m + 1.
Proof.
  intros m n H.
  unfold plus3.
  rewrite -> H.
  reflexivity.
Qed.

Theorem override_eq : 
  forall {X : Type} (x : X) (k : nat) (f : nat -> X),
    (override f k x) k = x.
Proof.
  intros X x k f.
  unfold override.
  rewrite <- beq_nat_refl.
  reflexivity.
Qed.

Theorem override_neq : 
  forall (X : Type) (x1 x2 : X) (k1 k2 : nat) (f : nat -> X),
    f k1 = x1 -> beq_nat k2 k1 = false -> (override f k2 x2) k1 = x1.
Proof.
  intros X x1 x2 k1 k2 f.
  intro H1.
  intro H2.
  unfold override.
  rewrite -> H2.
  rewrite -> H1.
  reflexivity.
Qed.

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

Example test_fold_length1 : fold_length [4;7;0] = 3.
Proof. reflexivity. Qed.

Theorem fold_length_correct :
  forall (X : Type) (lst : list X), fold_length lst = length lst.
Proof.
  intros X lst.
  unfold fold_length.
  induction lst as [|x xs].
  Case "lst = nil".
  {
    simpl.
    reflexivity.
  }
  Case "lst = x :: xs".
  {
    simpl.
    rewrite -> IHxs.
    reflexivity.
  }
Qed.

Check @fold.

Definition fold_map {X Y : Type} (f : X -> Y) (lst : list X) : list Y :=
  fold (fun x => cons (f x)) lst [].

Eval compute in (map plus3 [1;2;3;4;5;6]).
Eval compute in (fold_map plus3 [1;2;3;4;5;6]).

Theorem fold_map_correct :
  forall (X Y : Type) (f : X -> Y) (lst : list X),
    (map f lst) = (fold_map f lst).
Proof.
  intros X Y f lst.
  induction lst as [|x xs].
  Case "lst = nil".
  {
    unfold fold_map.
    simpl.
    reflexivity.
  }
  Case "lst = cons x xs".
  {
    unfold fold_map.
    simpl.
    rewrite -> IHxs.
    unfold fold_map.
    reflexivity.
  }
Qed.
