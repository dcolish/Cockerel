Require Import HypError.

(* This language should be used to add new hypothesis
   without changing the goal state *)
Tactic Notation "Write" constr(A) "Using" tactic(B) := 
  assert (H:A); [tauto | B; clear H ] 
    || UNJUSTIFIED A B.

(* This language should be used to clear or modfiy goals *)
Tactic Notation "For" constr(A) "Use" tactic(B) :=
  let H:= fresh "H0" in
  assert (H:A); [B | tauto]
    || UNJUSTIFIED A B.
