(** * Basics: Functional Programming in Coq *)

(* ################################################################# *)
(** * Data and Functions *)

(* ================================================================= *)
(** ** Enumerated Types *)

(** In Coq, we can build practically everything from first
    principles... *)

(* ================================================================= *)
(** ** Days of the Week *)

(** A datatype definition: *)

Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

(** A function on days: *)

Definition next_working_day (d:day) : day :=
  match d with
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => monday
  | saturday  => monday
  | sunday    => monday
  end.

(** Simplification: *)

Compute (next_working_day friday).
(* ==> monday : day *)

Compute (next_working_day (next_working_day saturday)).
(* ==> tuesday : day *)

(** Second, we can record what we _expect_ the result to be in the
    form of a Coq example: *)

Example test_next_working_day:
  (next_working_day (next_working_day saturday)) = tuesday.

(** We can then present a _proof script_ giving evidence for
    the claim: *)

Proof. simpl. reflexivity.  Qed.

(** Third, we can ask Coq to _extract_, from our [Definition], a
    program in a more conventional programming language (OCaml,
    Scheme, or Haskell) with a high-performance compiler.  This
    facility is very useful, since it gives us a path from
    proved-correct algorithms written in Gallina to efficient machine
    code.

    (Of course, we are trusting the correctness of the
    OCaml/Haskell/Scheme compiler, and of Coq's extraction facility
    itself, but this is still a big step forward from the way most
    software is developed today!)

    Indeed, this is one of the main uses for which Coq was developed.
    We'll come back to this topic in later chapters. *)

(* ================================================================= *)
(** ** Booleans *)

(** Another familiar enumerated type: *)

Inductive bool : Type :=
  | true
  | false.

(** Booleans are also available in Coq's standard library, but
    in this course we'll define everything from scratch, just to see
    how it's done. *)
Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

(** Note the syntax for defining multi-argument
    functions ([andb] and [orb]).  *)
Example test_orb1:  (orb true  false) = true.
Proof. simpl. reflexivity.  Qed.
Example test_orb2:  (orb false false) = false.
Proof. simpl. reflexivity.  Qed.
Example test_orb3:  (orb false true)  = true.
Proof. simpl. reflexivity.  Qed.
Example test_orb4:  (orb true  true)  = true.
Proof. simpl. reflexivity.  Qed.

(** We can define new symbolic notations for existing definitions. *)

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5:  false || false || true = true.
Proof. simpl. reflexivity. Qed.

(** We can also write these function using "if" expressions.  *)

Definition negb' (b:bool) : bool :=
  if b then false
  else true.

Definition andb' (b1:bool) (b2:bool) : bool :=
  if b1 then b2
  else false.

Definition orb' (b1:bool) (b2:bool) : bool :=
  if b1 then true
  else b2.

(** This works for all datatypes with two constructors: *)

Inductive bw : Type :=
  | b
  | w.

Definition invert (x: bw) : bw :=
  if x then w
  else b.

Compute (invert b).
(* ==> w: bw *)

Compute (invert w).
(* ==> b: bw *)