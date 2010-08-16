(* Lemmas directly from Hein's Book 
   There will eventually be a tactic to apply these 
   during the proof process *)

Require Import HypTactics.
Require Import HypNotation.


Axiom H0 : Prop.

(* Ltac Parse_Step A B := *)
(*   match goal with  *)
(*     | [|- A ] =>  assert(A); [B |tauto] *)
(*     | ?T => idtac "You must state a valid goal to make progress," A "is not valid" *)
(*   end. *)

(* a tactic sort of like this should work well to push through 
   any asserts we need for the forward style *)

(* add tactic for testing if a goal is trivial *)

Lemma ex_6_19 P : (~~P) <-> P. 
Universal_Intros.
Split_Eq.
  Conditional_Proof.
  For P Use IP.
  Contr H2 H1.
  assumption.
(*
  For False Use (Contr H2 H2).
*)
  Conditional_Proof.
  Conditional_Proof.
  For False Use (Contr H1 H2).
  assumption.
Qed.

Lemma ex_6_20 A B: (A \/ B) -> (~B -> A).
Conditional_Proof.
Conditional_Proof.
For A Use IP.
Write B Using (DS H1 H3).
For False Use (Contr H2 H4).
assumption.
Qed.

Lemma ex_6_21 (A B: Prop): A -> (B\/A).
Conditional_Proof.
Write (A\/B) Using (Addition1 H1 B).
Disjunc A (B\/A).
For A Use IP.
Write B Using (DS H2 H3).
For False Use (Contr H3 H1).
assumption.
Qed.

(** Proof of Modus Tollens (MT) *)
Lemma ex_6_22 (A B:Prop): (A -> B) -> (~B -> ~A).  
  Universal_Intros.
  Conditional_Proof.
  Conditional_Proof.
  For (~A) Use IP.
(*
  DN H3.
  Modus_Ponens H1 H4.
  Contr H2 H5.
*)
  Write A Using (DN H3). 
  Modus_Ponens H1 H4. 
  For False Use (Contr H2 H5).
  assumption.
Qed.


Lemma ex_6_23 (A B C:Prop): (A\/B) -> ((A -> C) -> ((B -> C) -> C)).
Universal_Intros. 
Conditional_Proof.
Conditional_Proof.
Conditional_Proof.
(*
Case H1.
rename H into H4.

info destruct H1.

refine (match H1 with
| or_introl x => _ x
| or_intror x => _ x
end). intro H4.
tauto.
info destruct H1.
*)
Case H1.
For C Use (Modus_Ponens H2 H4).
Solve_With H5.
For C Use (Modus_Ponens H3 H4).
Solve_With H5.
Qed.

(** Proof of Hypothetical Reasoning (HR) *)
Lemma ex_6_24 (A B C: Prop) : (A -> B) -> ((B -> C) -> (A -> C)).
Universal_Intros.
Conditional_Proof.
Conditional_Proof.
Conditional_Proof.
MP H1 H3.
(* broken
Write B Using (Modus_Ponens H1 H3). 
*)
For C Use (Modus_Ponens H2 H4).
Solve_With H5.
Qed.

(** Proof of Constructive Dilemma (CD) *)
Lemma ex_6_25 (A B D C: Prop) : (A\/B) -> ((A -> C) -> ((B -> D) -> (C\/D))).
  Universal_Intros.
  Conditional_Proof.
  Conditional_Proof.
  Conditional_Proof.
  Case H1.
  Disjunc C (C\/D).
  For C Use (Modus_Ponens H2 H4).
  Solve_With H5.
  Disjunc D (C\/D).
  For D Use (Modus_Ponens H3 H4). (* Todo: if you replace H4 with H5 (which doesn't yet exist) this tactic does the right thing!  Why? *)
  Solve_With H5.
Qed.
  
Lemma p374_6_8 A B C: (A \/ B) /\ (A \/ C) /\ ~A -> B /\ C.
Conditional_Proof.
Conditional_Proof.
Conditional_Proof.
Write B Using (DS H1 H3).
Write C Using (DS H2 H3).
For (B/\C) Use (Conj H4 H5). (* Todo: this solves the goal completely.  Instead, augment the hypotheses *)
Qed.


Lemma p375_6_9 A B C D: ((A \/ B) -> (B /\ C)) -> ((B -> C) \/ D).
Conditional_Proof.
Disjunc (B->C) (B->C \/D).
Conditional_Proof.
Write (A\/B) Using (Addition2 H2 A).
Modus_Ponens H1 H3.
(* broken:
Write (B/\C) Using (Modus_Ponens H1 H3).
*)
Simp_right H4. (* Todo: currently solves.  instead should augment the hypotheses *)
(* causes anomaly:
Write C Using (Simp_right H4). 
*)
Qed.


Lemma ex_6_28 P Q: (~P\/Q) <-> (P -> Q).
Universal_Intros.
Split_Eq.
  Conditional_Proof.
  Conditional_Proof.
  For Q Use (DS H1 H2).
  Conditional_Proof.
  Pose (~P) For P. (* Pose uses the excluded middle axiom, not ID. This might be bad later *)
  Modus_Ponens H1 H2.
(* broken
  Write Q Using (Modus_Ponens H1 H2).
*)
  Solve_With H3.
  Disjunc (~P) (~P \/ Q).
  Solve_With H3.
Qed.
