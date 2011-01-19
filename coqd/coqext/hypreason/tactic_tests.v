Require Import HypTactics.

Variables A B C D E: Prop.

(** Test Modus Ponens *)

Goal A -> (B -> ((A -> C) -> C)).
Conditional_Proof.
Conditional_Proof.
Conditional_Proof.
(* Test for arrow structure *)
Modus_Ponens H0 H1.
(* Test if domain of arrow matches argument type *)
Modus_Ponens H2 H1.
(* Correct usage: *)
Modus_Ponens H2 H0.
tauto.
Qed.

(** Test Modus Tollens *)

Goal (A -> B) -> (~B -> (~C -> (D -> ~A))).
CP.
CP.
CP.
CP.
MT H1 H2.
MT H0 H2.
MT H0 H3.
(* expansion of what macro should do:
assert (~A).
intro X.
apply H1.
apply H0.
apply X.
*)
MT H0 H1.
exact H4.
Qed.


