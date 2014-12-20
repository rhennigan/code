Section Basics.
  Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

  Definition next_weekday (d : day) : day :=
    match d with
      | monday => tuesday
      | tuesday => wednesday
      | wednesday => thursday
      | thursday => friday
      | _ => monday
    end.

  Eval compute in (next_weekday friday).
  Eval compute in (next_weekday (next_weekday saturday)).

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

Example test_nandb2: (nandb false false) = true.
(* FILL IN HERE *) Admitted.
Example test_nandb3: (nandb false true) = true.
(* FILL IN HERE *) Admitted.
Example test_nandb4: (nandb true true) = false.
(* FILL IN HERE *) Admitted.