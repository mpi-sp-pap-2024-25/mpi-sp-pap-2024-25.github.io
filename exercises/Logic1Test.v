Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From LF Require Import Logic1.

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

From LF Require Import Logic1.
Import Check.

Goal True.

idtac "-------------------  plus_is_O  --------------------".
idtac " ".

idtac "#> plus_is_O".
idtac "Possible points: 2".
check_type @plus_is_O ((forall n m : nat, n + m = 0 -> n = 0 /\ m = 0)).
idtac "Assumptions:".
Abort.
Print Assumptions plus_is_O.
Goal True.
idtac " ".

idtac "-------------------  and_assoc  --------------------".
idtac " ".

idtac "#> and_assoc".
idtac "Possible points: 1".
check_type @and_assoc ((forall P Q R : Prop, P /\ Q /\ R -> (P /\ Q) /\ R)).
idtac "Assumptions:".
Abort.
Print Assumptions and_assoc.
Goal True.
idtac " ".

idtac "-------------------  mult_is_O  --------------------".
idtac " ".

idtac "#> mult_is_O".
idtac "Possible points: 2".
check_type @mult_is_O ((forall n m : nat, n * m = 0 -> n = 0 \/ m = 0)).
idtac "Assumptions:".
Abort.
Print Assumptions mult_is_O.
Goal True.
idtac " ".

idtac "-------------------  or_commut  --------------------".
idtac " ".

idtac "#> or_commut".
idtac "Possible points: 1".
check_type @or_commut ((forall P Q : Prop, P \/ Q -> Q \/ P)).
idtac "Assumptions:".
Abort.
Print Assumptions or_commut.
Goal True.
idtac " ".

idtac "-------------------  not_implies_our_not  --------------------".
idtac " ".

idtac "#> not_implies_our_not".
idtac "Possible points: 2".
check_type @not_implies_our_not ((forall P : Prop, ~ P -> forall Q : Prop, P -> Q)).
idtac "Assumptions:".
Abort.
Print Assumptions not_implies_our_not.
Goal True.
idtac " ".

idtac "-------------------  double_neg_informal  --------------------".
idtac " ".

idtac "#> Manually graded: double_neg_informal".
idtac "Advanced".
idtac "Possible points: 2".
print_manual_grade manual_grade_for_double_neg_informal.
idtac " ".

idtac "-------------------  contrapositive  --------------------".
idtac " ".

idtac "#> contrapositive".
idtac "Possible points: 1".
check_type @contrapositive ((forall P Q : Prop, (P -> Q) -> ~ Q -> ~ P)).
idtac "Assumptions:".
Abort.
Print Assumptions contrapositive.
Goal True.
idtac " ".

idtac "-------------------  not_both_true_and_false  --------------------".
idtac " ".

idtac "#> not_both_true_and_false".
idtac "Possible points: 1".
check_type @not_both_true_and_false ((forall P : Prop, ~ (P /\ ~ P))).
idtac "Assumptions:".
Abort.
Print Assumptions not_both_true_and_false.
Goal True.
idtac " ".

idtac "-------------------  not_PNP_informal  --------------------".
idtac " ".

idtac "#> Manually graded: not_PNP_informal".
idtac "Advanced".
idtac "Possible points: 1".
print_manual_grade manual_grade_for_not_PNP_informal.
idtac " ".

idtac "-------------------  de_morgan_not_or  --------------------".
idtac " ".

idtac "#> de_morgan_not_or".
idtac "Possible points: 2".
check_type @de_morgan_not_or ((forall P Q : Prop, ~ (P \/ Q) -> ~ P /\ ~ Q)).
idtac "Assumptions:".
Abort.
Print Assumptions de_morgan_not_or.
Goal True.
idtac " ".

idtac "-------------------  not_S_inverse_pred  --------------------".
idtac " ".

idtac "#> not_S_inverse_pred".
idtac "Possible points: 1".
check_type @not_S_inverse_pred ((~ (forall n : nat, S (Nat.pred n) = n))).
idtac "Assumptions:".
Abort.
Print Assumptions not_S_inverse_pred.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 13".
idtac "Max points - advanced: 16".
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
idtac "---------- plus_is_O ---------".
Print Assumptions plus_is_O.
idtac "---------- and_assoc ---------".
Print Assumptions and_assoc.
idtac "---------- mult_is_O ---------".
Print Assumptions mult_is_O.
idtac "---------- or_commut ---------".
Print Assumptions or_commut.
idtac "---------- not_implies_our_not ---------".
Print Assumptions not_implies_our_not.
idtac "---------- contrapositive ---------".
Print Assumptions contrapositive.
idtac "---------- not_both_true_and_false ---------".
Print Assumptions not_both_true_and_false.
idtac "---------- de_morgan_not_or ---------".
Print Assumptions de_morgan_not_or.
idtac "---------- not_S_inverse_pred ---------".
Print Assumptions not_S_inverse_pred.
idtac "".
idtac "********** Advanced **********".
idtac "---------- double_neg_informal ---------".
idtac "MANUAL".
idtac "---------- not_PNP_informal ---------".
idtac "MANUAL".
Abort.

(* 2024-11-21 15:04 *)
