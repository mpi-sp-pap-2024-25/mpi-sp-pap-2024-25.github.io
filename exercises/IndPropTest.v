Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From LF Require Import IndProp.

Parameter MISSING: Type.

Module Check.

Ltac check_type A B :=
    match type of A with
    | context[MISSING] => idtac "Missing:" A
    | ?T => first [unify T B; idtac "Type: ok" | idtac "Type: wrong - should be (" B ")"]
    end.

Ltac print_manual_grade A :=
    match eval compute in A with
    | Some (_ ?S ?C) =>
        idtac "Score:"  S;
        match eval compute in C with
          | ""%string => idtac "Comment: None"
          | _ => idtac "Comment:" C
        end
    | None =>
        idtac "Score: Ungraded";
        idtac "Comment: None"
    end.

End Check.

From LF Require Import IndProp.
Import Check.

Goal True.

idtac "-------------------  R_provability  --------------------".
idtac " ".

idtac "#> Manually graded: R.R_provability".
idtac "Possible points: 3".
print_manual_grade R.manual_grade_for_R_provability.
idtac " ".

idtac "-------------------  subsequence  --------------------".
idtac " ".

idtac "#> subseq_refl".
idtac "Advanced".
idtac "Possible points: 1".
check_type @subseq_refl ((forall l : list nat, subseq l l)).
idtac "Assumptions:".
Abort.
Print Assumptions subseq_refl.
Goal True.
idtac " ".

idtac "#> subseq_app".
idtac "Advanced".
idtac "Possible points: 2".
check_type @subseq_app (
(forall l1 l2 l3 : list nat, subseq l1 l2 -> subseq l1 (l2 ++ l3))).
idtac "Assumptions:".
Abort.
Print Assumptions subseq_app.
Goal True.
idtac " ".

idtac "#> subseq_trans".
idtac "Advanced".
idtac "Possible points: 3".
check_type @subseq_trans (
(forall l1 l2 l3 : list nat, subseq l1 l2 -> subseq l2 l3 -> subseq l1 l3)).
idtac "Assumptions:".
Abort.
Print Assumptions subseq_trans.
Goal True.
idtac " ".

idtac "-------------------  exp_match_ex1  --------------------".
idtac " ".

idtac "#> EmptySet_is_empty".
idtac "Possible points: 0.5".
check_type @EmptySet_is_empty ((forall (T : Type) (s : list T), ~ (s =~ @EmptySet T))).
idtac "Assumptions:".
Abort.
Print Assumptions EmptySet_is_empty.
Goal True.
idtac " ".

idtac "#> MUnion'".
idtac "Possible points: 0.5".
check_type @MUnion' (
(forall (T : Type) (s : list T) (re1 re2 : reg_exp T),
 s =~ re1 \/ s =~ re2 -> s =~ @Union T re1 re2)).
idtac "Assumptions:".
Abort.
Print Assumptions MUnion'.
Goal True.
idtac " ".

idtac "#> MStar'".
idtac "Possible points: 2".
check_type @MStar' (
(forall (T : Type) (ss : list (list T)) (re : reg_exp T),
 (forall s : list T, @In (list T) s ss -> s =~ re) ->
 @fold (list T) (list T) (@app T) ss [ ] =~ @Star T re)).
idtac "Assumptions:".
Abort.
Print Assumptions MStar'.
Goal True.
idtac " ".

idtac "-------------------  re_not_empty  --------------------".
idtac " ".

idtac "#> re_not_empty".
idtac "Possible points: 3".
check_type @re_not_empty ((forall T : Type, reg_exp T -> bool)).
idtac "Assumptions:".
Abort.
Print Assumptions re_not_empty.
Goal True.
idtac " ".

idtac "#> re_not_empty_correct".
idtac "Possible points: 3".
check_type @re_not_empty_correct (
(forall (T : Type) (re : reg_exp T),
 (exists s : list T, s =~ re) <-> @re_not_empty T re = true)).
idtac "Assumptions:".
Abort.
Print Assumptions re_not_empty_correct.
Goal True.
idtac " ".

idtac "-------------------  exp_match_ex2  --------------------".
idtac " ".

idtac "#> MStar''".
idtac "Possible points: 6".
check_type @MStar'' (
(forall (T : Type) (s : list T) (re : reg_exp T),
 s =~ @Star T re ->
 exists ss : list (list T),
   s = @fold (list T) (list T) (@app T) ss [ ] /\
   (forall s' : list T, @In (list T) s' ss -> s' =~ re))).
idtac "Assumptions:".
Abort.
Print Assumptions MStar''.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 18".
idtac "Max points - advanced: 24".
idtac "".
idtac "Allowed Axioms:".
idtac "functional_extensionality".
idtac "FunctionalExtensionality.functional_extensionality_dep".
idtac "plus_le".
idtac "le_trans".
idtac "le_plus_l".
idtac "add_le_cases".
idtac "Sn_le_Sm__n_le_m".
idtac "O_le_n".
idtac "".
idtac "".
idtac "********** Summary **********".
idtac "".
idtac "Below is a summary of the automatically graded exercises that are incomplete.".
idtac "".
idtac "The output for each exercise can be any of the following:".
idtac "  - 'Closed under the global context', if it is complete".
idtac "  - 'MANUAL', if it is manually graded".
idtac "  - A list of pending axioms, containing unproven assumptions. In this case".
idtac "    the exercise is considered complete, if the axioms are all allowed.".
idtac "".
idtac "********** Standard **********".
idtac "---------- R_provability ---------".
idtac "MANUAL".
idtac "---------- EmptySet_is_empty ---------".
Print Assumptions EmptySet_is_empty.
idtac "---------- MUnion' ---------".
Print Assumptions MUnion'.
idtac "---------- MStar' ---------".
Print Assumptions MStar'.
idtac "---------- re_not_empty ---------".
Print Assumptions re_not_empty.
idtac "---------- re_not_empty_correct ---------".
Print Assumptions re_not_empty_correct.
idtac "---------- MStar'' ---------".
Print Assumptions MStar''.
idtac "".
idtac "********** Advanced **********".
idtac "---------- subseq_refl ---------".
Print Assumptions subseq_refl.
idtac "---------- subseq_app ---------".
Print Assumptions subseq_app.
idtac "---------- subseq_trans ---------".
Print Assumptions subseq_trans.
Abort.

(* 2024-12-19 15:23 *)
