(** * Logic1: Logic in Coq: part 1 *)

Set Warnings "-notation-overridden,-parsing".
Set Warnings "-deprecated-hint-without-locality".
Require Nat.
From LF Require Export Tactics.


(** We have now seen many examples of factual claims (_propositions_)
    and ways of presenting evidence of their truth (_proofs_).  In
    particular, we have worked extensively with equality
    propositions ([e1 = e2]), implications ([P -> Q]), and quantified
    propositions ([forall x, P]).  In this chapter, we will see how
    Coq can be used to carry out other familiar forms of logical
    reasoning.

    Before diving into details, we should talk a bit about the status of
    mathematical statements in Coq.  Recall that Coq is a _typed_
    language, which means that every sensible expression has an
    associated type.  Logical claims are no exception: any statement
    we might try to prove in Coq has a type, namely [Prop], the type
    of _propositions_.  We can see this with the [Check] command: *)

Check (forall n m : nat, n + m = m + n) : Prop.

(** Note that _all_ syntactically well-formed propositions have type
    [Prop] in Coq, regardless of whether they are true or not.

    Simply _being_ a proposition is one thing; being _provable_ is
    a different thing! *)

Check 2 = 2 : Prop.

Check 3 = 2 : Prop.

Check forall n : nat, n = 2 : Prop.

(** Indeed, propositions don't just have types -- they are
    _first-class_ entities that can be manipulated in all the same ways as
    any of the other things in Coq's world. *)

(** So far, we've seen one primary place that propositions can appear:
    in [Theorem] (and [Lemma] and [Example]) declarations. *)

Theorem plus_2_2_is_4 :
  2 + 2 = 4.
Proof. reflexivity.  Qed.

(** But propositions can be used in other ways.  For example, we
    can give a name to a proposition using a [Definition], just as we
    give names to other kinds of expressions. *)

Definition plus_claim : Prop := 2 + 2 = 4.
Check plus_claim : Prop.

(** We can later use this name in any situation where a proposition is
    expected -- for example, as the claim in a [Theorem] declaration. *)

Theorem plus_claim_is_true :
  plus_claim.
Proof. reflexivity.  Qed.

(** We can also write _parameterized_ propositions -- that is,
    functions that take arguments of some type and return a
    proposition. *)

(** For instance, the following function takes a number
    and returns a proposition asserting that this number is equal to
    three: *)

Definition is_three (n : nat) : Prop :=
  n = 3.
Check is_three : nat -> Prop.

(** In Coq, functions that return propositions are said to define
    _properties_ of their arguments.

    For instance, here's a (polymorphic) property defining the
    familiar notion of an _injective function_. *)

Definition injective {A B} (f : A -> B) : Prop :=
  forall x y : A, f x = f y -> x = y.

Lemma succ_inj : injective S.
Proof.
  intros x y H. injection H as H1. apply H1.
Qed.

(** The familiar equality operator [=] is a (binary) function that returns
    a [Prop].

    The expression [n = m] is syntactic sugar for [eq n m] (defined in
    Coq's standard library using the [Notation] mechanism).

    Because [eq] can be used with elements of any type, it is also
    polymorphic: *)

Check @eq : forall A : Type, A -> A -> Prop.

(** (Notice that we wrote [@eq] instead of [eq]: The type
    argument [A] to [eq] is declared as implicit, and we need to turn
    off the inference of this implicit argument to see the full type
    of [eq].) *)

(* ################################################################# *)
(** * Logical Connectives *)

(* ================================================================= *)
(** ** Conjunction *)

(** The _conjunction_, or _logical and_, of propositions [A] and [B] is
    written [A /\ B]; it represents the claim that both [A] and [B] are
    true. *)

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.

(** To prove a conjunction, use the [split] tactic.  This will generate
    two subgoals, one for each part of the statement: *)

Proof.
  split.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 * 2 = 4 *) reflexivity.
Qed.

(** For any propositions [A] and [B], if we assume that [A] is true and
    that [B] is true, we can conclude that [A /\ B] is also true.  The Coq
    library provides a function [conj] that does this. *)

Check @conj : forall A B : Prop, A -> B -> A /\ B.

(** Since applying a theorem with hypotheses to some goal has the effect of
    generating as many subgoals as there are hypotheses for that theorem,
    we can apply [conj] to achieve the same effect as [split]. *)

Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply conj.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 + 2 = 4 *) reflexivity.
Qed.

(** **** Exercise: 2 stars, standard (plus_is_O) *)

Example plus_is_O :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** So much for proving conjunctive statements.  To go in the other
    direction -- i.e., to _use_ a conjunctive hypothesis to help prove
    something else -- we employ the [destruct] tactic. *)

(** When the current proof context contains a hypothesis [H] of the
    form [A /\ B], writing [destruct H as [HA HB]] will remove [H]
    from the context and replace it with two new hypotheses: [HA],
    stating that [A] is true, and [HB], stating that [B] is true.  *)

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

(** As usual, we can also destruct [H] right when we introduce it,
    instead of introducing and then destructing it: *)

Lemma and_example2' :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

(** You may wonder why we bothered packing the two hypotheses [n = 0] and
    [m = 0] into a single conjunction, since we could also have stated the
    theorem with two separate premises: *)

Lemma and_example2'' :
  forall n m : nat, n = 0 -> m = 0 -> n + m = 0.
Proof.
  intros n m Hn Hm.
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

(** For this specific theorem, both formulations are fine.  But
    it's important to understand how to work with conjunctive
    hypotheses because conjunctions often arise from intermediate
    steps in proofs, especially in larger developments.  Here's a
    simple example: *)

Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n m H.
  apply plus_is_O in H.
  destruct H as [Hn Hm].
  rewrite Hn. reflexivity.
Qed.

(** Another common situation is that we know [A /\ B] but in some context
    we need just [A] or just [B].  In such cases we can do a
    [destruct] (possibly as part of an [intros]) and use an underscore
    pattern [_] to indicate that the unneeded conjunct should just be
    thrown away. *)

Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q HPQ.
  destruct HPQ as [HP _].
  apply HP.  Qed.

(** **** Exercise: 1 star, standard, optional (proj2) *)
Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Finally, we sometimes need to rearrange the order of conjunctions
    and/or the grouping of multi-way conjunctions. We can see this
    at work in the proofs of the following commutativity and
    associativity theorems *)

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
    - (* left *) apply HQ.
    - (* right *) apply HP.  Qed.

(** **** Exercise: 1 star, standard (and_assoc)

    (In the following proof of associativity, notice how the _nested_
    [intros] pattern breaks the hypothesis [H : P /\ (Q /\ R)] down into
    [HP : P], [HQ : Q], and [HR : R].  Finish the proof.) *)

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Finally, the infix notation [/\] is actually just syntactic sugar for
    [and A B].  That is, [and] is a Coq operator that takes two
    propositions as arguments and yields a proposition. *)

Check and : Prop -> Prop -> Prop.

(* ================================================================= *)
(** ** Disjunction *)

(** Another important connective is the _disjunction_, or _logical or_,
    of two propositions: [A \/ B] is true when either [A] or [B] is.
    (This infix notation stands for [or A B], where
    [or : Prop -> Prop -> Prop].) *)

(** To use a disjunctive hypothesis in a proof, we proceed by case
    analysis -- which, as with other data types like [nat], can be done
    explicitly with [destruct] or implicitly with an [intros]
    pattern: *)

Lemma factor_is_O:
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  (* This pattern implicitly does case analysis on
     [n = 0 \/ m = 0] *)
  intros n m [Hn | Hm].
  - (* Here, [n = 0] *)
    rewrite Hn. reflexivity.
  - (* Here, [m = 0] *)
    rewrite Hm. rewrite <- mult_n_O.
    reflexivity.
Qed.

(** We can see in this example that, when we perform case analysis on a
    disjunction [A \/ B], we must separately satisfy two proof
    obligations, each showing that the conclusion holds under a different
    assumption -- [A] in the first subgoal and [B] in the second.

    The case analysis pattern [[Hn | Hm]] allows
    us to name the hypotheses that are generated for the subgoals. *)

(** Conversely, to show that a disjunction holds, it suffices to show that
    one of its sides holds. This can be done via the tactics [left] and
    [right].  As their names imply, the first one requires proving the left
    side of the disjunction, while the second requires proving the right
    side.  Here is a trivial use... *)

Lemma or_intro_l : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.

(** ... and here is a slightly more interesting example requiring both
    [left] and [right]: *)

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  (* WORKED IN CLASS *)
  intros [|n'].
  - left. reflexivity.
  - right. reflexivity.
Qed.

(** **** Exercise: 2 stars, standard (mult_is_O) *)
Lemma mult_is_O :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star, standard (or_commut) *)
Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** Falsehood and Negation

    Up to this point, we have mostly been concerned with proving "positive"
    statements -- addition is commutative, appending lists is associative,
    etc.  Of course, we are sometimes also interested in negative results,
    demonstrating that some given proposition is _not_ true. Such
    statements are expressed with the logical negation operator [~]. *)

(** To see how negation works, recall the _principle of explosion_
    from the [Tactics] chapter, which asserts that, if we assume a
    contradiction, then any other proposition can be derived.

    Following this intuition, we could define [~ P] ("not [P]") as
    [forall Q, P -> Q]. *)

(** Coq actually makes a slightly different (but equivalent) choice,
    defining [~ P] as [P -> False], where [False] is a specific
    un-provable proposition defined in the standard library. *)

Module NotPlayground.

Definition not (P:Prop) := P -> False.

Check not : Prop -> Prop.

Notation "~ x" := (not x) : type_scope.

End NotPlayground.

(** Since [False] is a contradictory proposition, the principle of
    explosion also applies to it. If we can get [False] into the context,
    we can use [destruct] on it to complete any goal: *)

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  (* WORKED IN CLASS *)
  intros P contra.
  destruct contra.  Qed.

(** The Latin _ex falso quodlibet_ means, literally, "from falsehood
    follows whatever you like"; this is another common name for the
    principle of explosion. *)

(** **** Exercise: 2 stars, standard (not_implies_our_not)

    Show that Coq's definition of negation implies the intuitive one
    mentioned above.

    Hint: while getting accustomed to Coq's definition of [not], you might
    find it helpful to [unfold not] near the beginning of proofs. *)

Theorem not_implies_our_not : forall (P:Prop),
  ~ P -> (forall (Q:Prop), P -> Q).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Inequality is a very common form of negated statement, so there is a
    special notation for it:

      Notation "x <> y" := (~(x = y)).
*)

(** For example: *)

Theorem zero_not_one : 0 <> 1.
Proof.
  (** The proposition [0 <> 1] is exactly the same as
      [~(0 = 1)] -- that is, [not (0 = 1)] -- which unfolds to
      [(0 = 1) -> False]. (We use [unfold not] explicitly here,
      to illustrate that point, but generally it can be omitted.) *)
  unfold not.
  (** To prove an inequality, we may assume the opposite
      equality... *)
  intros contra.
  (** ... and deduce a contradiction from it. Here, the
      equality [O = S O] contradicts the disjointness of
      constructors [O] and [S], so [discriminate] takes care
      of it. *)
  discriminate contra.
Qed.

(** It takes a little practice to get used to working with negation in Coq.
    Even though _you_ can see perfectly well why a statement involving
    negation is true, it can be a little tricky at first to see how to make
    Coq understand it!

    Here are proofs of a few familiar facts to help get you warmed up. *)

Theorem not_False :
  ~ False.
Proof.
  unfold not. intros H. destruct H. Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  (* WORKED IN CLASS *)
  intros P Q [HP HNP]. unfold not in HNP.
  apply HNP in HP. destruct HP.  Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  (* WORKED IN CLASS *)
  intros P H. unfold not. intros G. apply G. apply H.  Qed.

(** **** Exercise: 2 stars, advanced (double_neg_informal)

    Write an _informal_ proof of [double_neg]:

   _Theorem_: [P] implies [~~P], for any proposition [P]. *)

(* FILL IN HERE *)

(* Do not modify the following line: *)
Definition manual_grade_for_double_neg_informal : option (nat*string) := None.
(** [] *)

(** **** Exercise: 1 star, standard, especially useful (contrapositive) *)
Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star, standard (not_both_true_and_false) *)
Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star, advanced (not_PNP_informal)

    Write an informal proof (in English) of the proposition [forall P
    : Prop, ~(P /\ ~P)]. *)

(* FILL IN HERE *)

(* Do not modify the following line: *)
Definition manual_grade_for_not_PNP_informal : option (nat*string) := None.
(** [] *)

(** **** Exercise: 2 stars, standard (de_morgan_not_or)

    _De Morgan's Laws_, named for Augustus De Morgan, describe how
    negation interacts with conjunction and disjunction.  The
    following law says that "the negation of a disjunction is the
    conjunction of the negations." There is a dual law
    [de_morgan_not_and_not] to which we will return at the end of this
    chapter. *)
Theorem de_morgan_not_or : forall (P Q : Prop),
    ~ (P \/ Q) -> ~P /\ ~Q.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star, standard (not_S_inverse_pred)

    Since we are working with natural numbers, we can disprove that
    [S] and [pred] are inverses of each other: *)
Lemma not_S_inverse_pred : ~(forall n : nat, S (pred n) = n).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Since inequality involves a negation, it also requires a little
    practice to be able to work with it fluently.  Here is one useful
    trick.

    If you are trying to prove a goal that is nonsensical (e.g., the
    goal state is [false = true]), apply [ex_falso_quodlibet] to
    change the goal to [False].

    This makes it easier to use assumptions of the form [~P] that may
    be available in the context -- in particular, assumptions of the
    form [x<>y]. *)

Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  intros b H. destruct b eqn:HE.
  - (* b = true *)
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity.
  - (* b = false *)
    reflexivity.
Qed.

(** Since reasoning with [ex_falso_quodlibet] is quite common, Coq
    provides a built-in tactic, [exfalso], for applying it. *)

Theorem not_true_is_false' : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.          (* note implicit [destruct b] here *)
  - (* b = true *)
    unfold not in H.
    exfalso.                (* <=== *)
    apply H. reflexivity.
  - (* b = false *) reflexivity.
Qed.

(* ================================================================= *)
(** ** Truth *)

(** Besides [False], Coq's standard library also defines [True], a
    proposition that is trivially true. To prove it, we use the
    constant [I : True], which is also defined in the standard
    library: *)

Lemma True_is_true : True.
Proof. apply I. Qed.

(** Unlike [False], which is used extensively, [True] is used
    relatively rarely, since it is trivial (and therefore
    uninteresting) to prove as a goal, and conversely it provides no
    interesting information when used as a hypothesis. *)

(** However, [True] can be quite useful when defining complex [Prop]s using
    conditionals or as a parameter to higher-order [Prop]s. We'll come back
    to this later.

    For now, let's take a look at how we can use [True] and [False] to
    achieve an effect similar to that of the [discriminate] tactic, without
    literally using [discriminate]. *)

(** Pattern-matching lets us do different things for different
    constructors.  If the result of applying two different
    constructors were hypothetically equal, then we could use [match]
    to convert an unprovable statement (like [False]) to one that is
    provable (like [True]). *)

Definition disc_fn (n: nat) : Prop :=
  match n with
  | O => True
  | S _ => False
  end.

Theorem disc_example : forall n, ~ (O = S n).
Proof.
  intros n contra.
  assert (H : disc_fn O). { simpl. apply I. }
  rewrite contra in H. simpl in H. apply H.
Qed.

(** To generalize this to other constructors, we simply have to provide an
    appropriate variant of [disc_fn]. To generalize it to other
    conclusions, we can use [exfalso] to replace them with [False].

    The built-in [discriminate] tactic takes care of all this for us! *)

(** **** Exercise: 2 stars, advanced, optional (nil_is_not_cons) *)

(** Use the same technique as above to show that [nil <> x :: xs].
    Do not use the [discriminate] tactic. *)

Theorem nil_is_not_cons : forall X (x : X) (xs : list X), ~ (nil = x :: xs).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* 2024-11-21 15:04 *)
