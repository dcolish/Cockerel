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
Conditional_Proof.
Addition1 ((A \/ B) -> B /\ C) -> (B -> C)) D.
Conditional_Proof.
Add H2 A.
Modus_Ponens H1 H3.
Simp_right H4. (* Simp alone is too vague *)
Qed.

Lemma p377_6_12 (A B C D:Prop) : A /\ ((A -> B) \/ (C /\ D)) -> (~B -> C).
Conditional_Proof.
Conditional_Proof.
Conditional_Proof.
Conj H1 H3.
(*
Todo:
 1. define [T] tactic
 2. is there a way of eliminating the [Prop] declaration in the statement of this lemma?
T ...
*)
