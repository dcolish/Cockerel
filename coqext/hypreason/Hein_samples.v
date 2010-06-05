Load HypTactics.

Lemma p374_6_8 A B C: (A \/ B) /\ (A \/ C) /\ ~A -> B /\ C.
P_with_CP.
P_with_CP.
P_with_CP.
DS H1 H3.
DS H2 H3.
Conj H4 H5.
Qed.

Lemma p375_6_9 A B C D: ((A \/ B) -> (B /\ C)) -> (B -> C) \/ D.
P_with_CP.
bwd_Add.
P_with_CP.
Add H2 A.
MP H1 H3.
Simp_right H4. (* Simp alone is too vague *)
Qed.

Lemma p377_6_12 (A B C D:Prop) : A /\ ((A -> B) \/ (C /\ D)) -> (~B -> C).
P_with_CP.
P_with_CP.
P_with_CP.
Conj H1 H3.
(*
Todo:
 1. define [T] tactic
 2. is there a way of eliminating the [Prop] declaration in the statement of this lemma?
T ...
*)
