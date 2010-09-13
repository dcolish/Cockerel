(* Error messages for Hypothetical Reasoning *)

Ltac FAILED A :=
  idtac A "will not solve this proof.".

Ltac NO_INTRO :=
  idtac "There are no more introductions possible".

Ltac UNJUSTIFIED A B :=
  idtac B "is not a valid justification for" A.
