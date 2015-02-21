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

  Fixpoint remove_one (v : nat) (s : bag) : bag :=
    match s with
      | [] => []
      | x :: xs => 
        match (beq_nat x v) with
          | true => xs
          | false => x :: (remove_one v xs)
        end
    end.

  Example test_remove_one1: count 5 (remove_one 5 [2;1;5;4;1]) = 0.
  Proof. reflexivity. Qed.
  Example test_remove_one2: count 5 (remove_one 5 [2;1;4;1]) = 0.
  Proof. reflexivity. Qed.
  Example test_remove_one3: count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
  Proof. reflexivity. Qed.
  Example test_remove_one4: count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
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
    Case "L = nil". 
    {
      simpl. 
      reflexivity.
    }
    Case "L = cons x L'".
    {
      simpl.
      reflexivity.
    }
  Qed.

  Theorem app_assoc :
    forall L__1 L__2 L__3 : natlist, (L__1 ++ L__2) ++ L__3 = L__1 ++ (L__2 ++ L__3).
  Proof.
    intros L__1 L__2 L__3.
    induction L__1 as [| x xs].
    Case "L__1 = nil".
    {
      simpl.
      reflexivity.
    }
    Case "L__1 = x :: xs".
    {
      simpl.
      rewrite -> IHxs.
      reflexivity.
    }
  Qed.

  Theorem app_length :
    forall L__1 L__2 : natlist, length (L__1 ++ L__2) = (length L__1) + (length L__2).
  Proof.
    intros L__1 L__2.
    induction L__1 as [| x xs].
    Case "L__1 = nil".
    {
      simpl.
      reflexivity.
    }
    Case "L__1 = x :: xs".
    {
      simpl.
      rewrite -> IHxs.
      reflexivity.
    }
  Qed.

  Fixpoint snoc (L : natlist) (v : nat) : natlist :=
    match L with
      | [] => [v]
      | x :: xs => x :: (snoc xs v)
    end.

  Fixpoint rev (L : natlist) : natlist :=
    match L with
      | [] => []
      | x :: xs => snoc (rev xs) x
    end.

  Example test_rev1: rev [1;2;3] = [3;2;1].
  Proof. reflexivity. Qed.
  Example test_rev2: rev nil = nil.
  Proof. reflexivity. Qed.

  Theorem length_snoc : 
    forall n : nat, forall L : natlist,
      length (snoc L n) = S (length L).
  Proof.
    intros n L.
    induction L as [| x xs].
    Case "L = nil".
    {
      simpl.
      reflexivity.
    }
    Case "L = x :: xs".
    {
      simpl.
      rewrite -> IHxs.
      reflexivity.
    }
  Qed.

  Theorem length_app1 : 
    forall n : nat, forall L : natlist,
      length (L ++ [n]) = S (length L).
  Proof.
    intros n L.
    induction L as [| x xs].
    Case "L = nil".
    {
      simpl.
      reflexivity.
    }
    Case "L = x :: xs".
    {
      simpl.
      rewrite -> IHxs.
      reflexivity.
    }
  Qed.

  Theorem rev_length:
    forall L : natlist, length (rev L) = length L.
  Proof.
    intro L.
    induction L as [| x xs].
    Case "L = nil".
    {
      simpl.
      reflexivity.
    }
    Case "L = x :: xs".
    {
      simpl.
      rewrite -> length_snoc.
      rewrite -> IHxs.
      reflexivity.
    }
  Qed.

  Theorem app_nil_end : 
    forall L : natlist, L ++ [] = L.
  Proof.
    intro L.
    induction L as [|x xs].
    Case "L = nil". simpl. reflexivity.
    Case "L = x :: xs".
    {
      simpl.
      rewrite -> IHxs.
      reflexivity.
    }
  Qed.

  Lemma rev_snoc :
    forall v : nat, forall L : natlist, rev (snoc L v) = v :: (rev L).
  Proof.
    intros v L.
    induction L as [|x xs].
    Case "L = nil". reflexivity.
    Case "L = x :: xs".
    {
      simpl.
      rewrite -> IHxs.
      simpl.
      reflexivity.
    }
  Qed.

  Lemma snoc_app :
    forall v : nat, forall L : natlist, snoc L v = L ++ [v].
  Proof.
    intros v L.
    induction L as [|x xs].
    Case "L = nil". simpl. reflexivity.
    Case "L = x :: xs".
    {
      simpl.
      rewrite <- IHxs.
      reflexivity.
    }
  Qed.

  Lemma rev_pairs :
    forall L__1 L__2 : natlist,
      (L__1 = L__2) -> (rev L__1 = rev L__2).
  Proof.
    intros L__1 L__2.
    intro H.
    induction L__1 as [|x xs].
    SCase "L__1 = nil". rewrite <- H. reflexivity.
    SCase "L__1 = x :: xs". rewrite <- H. reflexivity.
  Qed.

  Theorem rev_involutive :
    forall L : natlist, rev (rev L) = L.
  Proof.
    intro L.
    induction L as [| x xs].
    Case "L = nil". simpl. reflexivity.
    Case "L = x :: xs".
    {
      simpl.
      Check rev_snoc.
      rewrite -> rev_snoc.
      rewrite -> IHxs.
      reflexivity.
    }
  Qed.

  Theorem app_assoc4 :
    forall L__1 L__2 L__3 L__4 : natlist,
      L__1 ++ (L__2 ++ (L__3 ++ L__4)) = ((L__1 ++ L__2) ++ L__3) ++ L__4.
  Proof.
    intros L__1 L__2 L__3 L__4.
    rewrite <- app_assoc.
    rewrite <- app_assoc.
    reflexivity.
  Qed.

  Theorem snoc_append : 
    forall (L : natlist) (n : nat),
      snoc L n = L ++ [n].
  Proof.
    intros L n.
    apply (snoc_app n L).
  Qed.

  Lemma snoc_both (L__1 : natlist) (L__2 : natlist) (v : nat) :
    (L__1 = L__2) -> (snoc L__1 v = snoc L__2 v).
  Proof.
    intros H__eq.
    destruct L__1 as [| x xs].
    Case "L__1 = nil".  rewrite <- H__eq. reflexivity.
    Case "L__1 = x :: xs".
    {
      simpl.
      rewrite <- H__eq.
      reflexivity.
    }
  Qed.

  Check snoc_both.

  Theorem distr_rev : 
    forall L__1 L__2 : natlist,
      rev (L__1 ++ L__2) = (rev L__2) ++ (rev L__1).
  Proof.
    intros L__1 L__2.
    induction L__1 as [| x xs].
    Case "L__1 = nil". 
    {
      simpl. 
      rewrite -> app_nil_end.
      reflexivity.
    }
    Case "L__1 = x :: xs".
    {
      simpl.
      assert (H : snoc (rev (xs ++ L__2)) x = snoc (rev L__2 ++ rev xs) x).
      rewrite -> IHxs. reflexivity.
      rewrite -> H.
      rewrite -> snoc_append.
      rewrite -> snoc_append.
      Check app_assoc.
      rewrite -> app_assoc.
      reflexivity.
    }
  Qed.

  Lemma nonzeros_app : 
    forall L__1 L__2 : natlist,
      nonzeros (L__1 ++ L__2) = (nonzeros L__1) ++ (nonzeros L__2).
  Proof.
    intros L__1 L__2.
    induction L__1 as [| x xs].
    Case "L__1 = nil". simpl. reflexivity.
    Case "L__1 = x :: xs".
    {
      destruct x as [| x'].
      SCase "x = 0". simpl. rewrite -> IHxs. reflexivity.
      SCase "x = S x'". simpl. rewrite -> IHxs. reflexivity.    
    }
  Qed.

  Fixpoint beq_natlist (L__1 L__2 : natlist) : bool :=
    match L__1, L__2 with
      | [], [] => true
      |  _, [] => false
      | [],  _ => false
      | x :: xs, y :: ys =>
        match (beq_nat x y) with
          | false => false
          | true => beq_natlist xs ys
        end
    end.

  Example test_beq_natlist1 : (beq_natlist nil nil = true).
  Proof. reflexivity. Qed.

  Example test_beq_natlist2 : beq_natlist [1;2;3] [1;2;3] = true.
  Proof. reflexivity. Qed.

  Example test_beq_natlist3 : beq_natlist [1;2;3] [1;2;4] = false.
  Proof. reflexivity. Qed.

  Theorem beq_natlist_refl : forall L : natlist, true = beq_natlist L L.
  Proof.
    intro L. 
    induction L as [| x xs]. 
    Case "L = nil". reflexivity.
    Case "L = x xs". 
    {
      destruct x as [| x']. 
      SCase "x = 0". rewrite -> IHxs. reflexivity.
      SCase "x = S x'".
      {
        simpl. 
        rewrite <- beq_nat_refl. 
        rewrite <- IHxs. 
        reflexivity.
      }
    }
  Qed.

  Fixpoint bpalindrome_aux (L S : natlist) : bool :=
    match L, S with
      | [], [] => true
      | [], _  => false
      | x :: xs, [] => bpalindrome_aux xs [x]
      | x :: xs, y :: ys =>
        match (beq_nat x y) with
          | true => bpalindrome_aux xs ys
          | false => bpalindrome_aux xs (x :: y :: ys)
        end
    end.

  Definition bpalindrome (L : natlist) : bool := bpalindrome_aux L [].

  Check bpalindrome.

  Lemma bool_flip :
    forall (b1 b2 : bool),
      (b1 = negb b2) -> (negb b1 = b2).
  Proof.
    intros b1 b2 H.
    rewrite -> H.
    SearchAbout negb.
    rewrite -> double_neg.
    reflexivity.
  Qed.

  Lemma bool_flip' :
    forall (b1 b2 : bool),
      (negb b1 = b2) -> (b1 = negb b2).
  Proof.
    intros b1 b2 H.
    rewrite <- H.
    rewrite -> double_neg.
    reflexivity.
  Qed.

  Lemma bool_im_flip :
    forall (b1 b2 : bool),
      (b1 = b2) -> (b2 = b1).
  Proof.
    auto.
  Qed.

  (* Lemma palindrome_cons : *)
  (*   forall (p : natlist) (v : nat), *)
  (*     (bpalindrome p) = negb (bpalindrome (v :: p)). *)
  (* Proof. *)
  (*   intros p. *)
  (*   induction p as [|x xs]. *)
  (*   Case "p = nil". *)
  (*   { *)
  (*     intro v. *)
  (*     unfold bpalindrome. *)
  (*     reflexivity. *)
  (*   } *)
  (*   Case "p = cons x xs". *)
  (*   { *)
  (*     intro v. *)
  (*     apply bool_flip'. *)
  (*     assert (bpalindrome xs = negb (bpalindrome (x :: xs))). apply (IHxs x). *)
  (*     rewrite <- H. *)
  (*     unfold bpalindrome in *. *)
  (*     simpl. *)
      
  (*   } *)

  (* Theorem palindrome_ext : *)
  (*   forall (lst : natlist) (v : nat),  *)
  (*     (bpalindrome lst) = (bpalindrome (snoc (v :: lst) v)). *)
  (* Proof. *)
  (*   intros lst v. *)
  (*   destruct (bpalindrome lst). *)
  (*   Case "lst is a palindrome". *)
  (*   { *)
  (*     induction lst as [|x xs]. *)
  (*     SCase "lst = nil". *)
  (*     { *)
  (*       unfold bpalindrome. *)
  (*       simpl. *)
  (*       rewrite <- beq_nat_refl. *)
  (*       reflexivity. *)
  (*     } *)
  (*     SCase "lst = cons x xs". *)
  (*     { *)
  (*       unfold bpalindrome in *. *)
  (*       simpl in *. *)
  (*     } *)
  (*   } *)
  (*   Case "lst is not a palindrome". *)
  (*   { *)

  (*   } *)

  Eval compute in (bpalindrome [1;2;2;1;1;2;2;1]).

  Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.

  Fixpoint natlist_first (L : natlist) : natoption :=
    match L with
      | [] => None
      | x :: xs => Some x
    end.

  Fixpoint natlist_last (L : natlist) : natoption :=
    match L with
      | [] => None
      | [x] => Some x
      | x :: xs => natlist_last xs
    end.

  Theorem double_rev_cons_eq_snoc :
    forall L : natlist, forall v : nat,
      (rev (v :: (rev L))) = (snoc L v).
  Proof.
    intros L v.
    simpl.
    rewrite -> rev_involutive.
    reflexivity.
  Qed.

<<<<<<< HEAD
Theorem rev_involutive' :
  forall L : natlist, rev (rev L) = L.
Proof.
intro L.
induction L.
trivial.
simpl.
rewrite -> rev_snoc.
rewrite IHL.
trivial.
Qed.



Print rev_involutive.
Print natlist_ind.

Locate snoc.
SearchAbout snoc.
SearchAbout rev.
SearchAbout nat.

=======
  Theorem count_member_nonzero :
    forall (s : bag), ble_nat 1 (count 1 (1 :: s)) = true.
  Proof.
    reflexivity.
  Qed.

  Theorem ble_n_Sn :
    forall n : nat, ble_nat n (S n) = true.
  Proof.
    intro n.
    induction n as [| n'].
    Case "n = 0". reflexivity.
    Case "n = S n'".
    {
      simpl. 
      rewrite -> IHn'. 
      reflexivity.
    }
  Qed.

  Theorem remove_decreases_count :
    forall (s : bag), ble_nat (count 0 (remove_one 0 s)) (count 0 s) = true.
  Proof.
    intro s.
    induction s as [| x xs]. 
    Case "s = nil". reflexivity.
    Case "s = x :: xs".
    {
      destruct x as [| x'].
      SCase "x = 0".
      {
        simpl.
        rewrite -> ble_n_Sn.
        reflexivity.
      }
      SCase "x = S x'".
      {
        simpl.
        rewrite <- IHxs.
        reflexivity.
      }
    }
  Qed.

  Theorem sum_adds_counts :
    forall (b__1 b__2 : bag), forall (v : nat),
      (count v (sum b__1 b__2)) = (count v b__1) + (count v b__2).
  Proof.
    intros b__1 b__2 v.
    induction b__1 as [| x xs].
    Case "b__1 = nil". reflexivity.
    Case "b__1 = x :: xs".
    {
      simpl.
      destruct (beq_nat x v).
      SCase "x = v". simpl. rewrite -> IHxs. reflexivity.
      SCase "x ~= v". rewrite -> IHxs. reflexivity.
    }
  Qed.

  Lemma empty_rev_is_empty :
    forall (L : natlist), (rev L = []) -> (L = []).
  Proof.
    intros L H. 
    assert (H1 : rev (rev L) = rev []). 
    apply (rev_pairs (rev L) [] H).
    assert (H2 : L = rev []).
    rewrite -> rev_involutive in H1.
    rewrite -> H1. reflexivity.
    rewrite -> H2. reflexivity.
  Qed.

  Lemma empty_rev_is_empty_conv :
    forall (L : natlist), (L = []) -> (rev L = []).
  Proof.
    intros L H. rewrite -> H. reflexivity.
  Qed.

  Theorem rev_injective :
    forall (L__1 L__2 : natlist), rev L__1 = rev L__2 -> L__1 = L__2.
  Proof.
    intros L__1 L__2 H1.
    assert (H2 : rev (rev L__1) = rev (rev L__2)).
    apply (rev_pairs (rev L__1) (rev L__2) H1).
    rewrite -> rev_involutive in H2.
    rewrite -> rev_involutive in H2.
    assumption.
  Qed.

  Fixpoint index (n : nat) (L : natlist) : natoption :=
    match L with
      | [] => None
      | x :: xs => 
        match (beq_nat n 0) with
          | true => Some x
          | false => index (pred n) xs
        end
    end.

  Example test_index1 : index 0 [4;5;6;7] = Some 4.
  Proof. reflexivity. Qed.

  Example test_index2 : index 3 [4;5;6;7] = Some 7.
  Proof. reflexivity. Qed.

  Example test_index3 : index 10 [4;5;6;7] = None.
  Proof. reflexivity. Qed.

  Fixpoint index' (n : nat) (L : natlist) : natoption :=
    match L with
      | [] => None
      | x :: xs => if (beq_nat n 0) then 
                    Some x else 
                    index' (pred n) xs
    end.

  Example test_index1' : index' 0 [4;5;6;7] = Some 4.
  Proof. reflexivity. Qed.

  Example test_index2' : index' 3 [4;5;6;7] = Some 7.
  Proof. reflexivity. Qed.

  Example test_index3' : index' 10 [4;5;6;7] = None.
  Proof. reflexivity. Qed.

  Definition option_elim (default : nat) (o : natoption) :=
    match o with
      | Some x => x
      | None => default
    end.

  Definition hd_opt := natlist_first.

  Example test_hd_opt1 : hd_opt [] = None.
  Proof. reflexivity. Qed.

  Example test_hd_opt2 : hd_opt [1] = Some 1.
  Proof. reflexivity. Qed.

  Example test_hd_opt3 : hd_opt [5;6] = Some 5.
  Proof. reflexivity. Qed.

  Theorem option_elim_hd : 
    forall (L : natlist) (default : nat),
      hd default L = option_elim default (hd_opt L).
  Proof.
    intros L d.
    induction L as [|x xs].
    {
      reflexivity.
    }
    {
      reflexivity.
    }
  Qed.

  Module Dictionary.
    
    Inductive dictionary : Type :=
    | empty : dictionary
    | record : nat -> nat -> dictionary -> dictionary.

    Definition insert (key value : nat) (d : dictionary) : dictionary :=
      (record key value d).

    Fixpoint find (key : nat) (d : dictionary) : natoption :=
      match d with
        | empty => None
        | record k v d' =>
          if (beq_nat key k)
          then (Some v)
          else (find key d')
      end.

    Theorem dictionary_invariant1' : 
      forall (d : dictionary) (k v : nat),
        (find k (insert k v d)) = Some v.
    Proof.
      intros d k v.
      simpl.
      rewrite <- beq_nat_refl.
      reflexivity.
    Qed.

    Theorem dictionary_invariant2' :
      forall (d : dictionary) (m n o : nat),
        beq_nat m n = false -> find m d = find m (insert n o d).
    Proof.
      intros d m n o H.
      simpl.
      rewrite -> H.
      reflexivity.
    Qed.

  End Dictionary.

End NatList.
>>>>>>> a4b61f7557d64f6d6f405ca5c8607063cd4d4b32
