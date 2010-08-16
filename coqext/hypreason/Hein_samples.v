Load HypTactics.

Lemma p374_6_8 A B C: (A \/ B) /\ (A \/ C) /\ ~A -> B /\ C.
Conditional_Proof.
Conditional_Proof.
Conditional_Proof.
DS H1 H3.
DS H2 H3.
Conj H4 H5.
Qed.

Lemma p375_6_9 A B C D: ((A \/ B) -> (B /\ C)) -> (B -> C) \/ D.
Universal_Intros.
Disjunc (((A \/ B) -> B /\ C) -> (B -> C)) (((A \/ B) -> B /\ C) -> (B -> C) \/ D).  (* Todo: revise interface for Disjunc so user isn't overwhelmed *)
(* Todo: Disjunc and Addition1 seem to do similar things, except the latter is broken.  Investigate.
Addition1 (((A \/ B) -> B /\ C) -> (B -> C)) D. 
*)
Conditional_Proof.
Conditional_Proof.
Addition2 H2 A.
Modus_Ponens H1 H3.
Simp_right H4. (* Todo: does too much at once.  Add C to hypotheses *)
Qed.

Lemma p377_6_12 (A B C D:Prop) : A /\ ((A -> B) \/ (C /\ D)) -> (~B -> C).
Conditional_Proof.
Conditional_Proof.
Conditional_Proof.
Conj H1 H3.
Admitted. (* Todo: finish this example *)
(*
Todo:
 1. define [T] tactic
 2. is there a way of eliminating the [Prop] declaration in the statement of this lemma?
T ...
*)
