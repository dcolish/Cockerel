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
  P_with_CP.
  For P Use IP.
  For False Use (Contr H1 H2).
  P_with_CP.
  P_with_CP.
  For False Use (Contr H1 H2).
Qed.

Lemma ex_6_20 A B: (A \/ B) -> (~B -> A).
P_with_CP.
P_with_CP.
For A Use IP.
Write B Using (DS H1 H3).
For False Use (Contr H2 H4).
Qed.

Lemma ex_6_21 (A B: Prop): A -> (B\/A).
P_with_CP.
Write (A\/B) Using (Add1 H1 B).
Disjunc A (B\/A).
For A Use IP.
Write B Using (DS H2 H3).
For False Use (Contr H3 H1).
Qed.

Lemma ex_6_22 (A B:Prop): (A -> B) -> (~B -> ~A).  
  Universal_Intros.
  P_with_CP.
  P_with_CP.
  For (~A) Use IP.
  Write A Using (DN H3). 
  Write B Using (MP H1 H3). 
  For False Use (Contr H2 H4).
Qed.


Lemma ex_6_23 (A B C:Prop): (A\/B) -> ((A -> C) -> ((B -> C) -> C)).
Universal_Intros. 
P_with_CP.
P_with_CP.
P_with_CP.
Case H1.
For C Use (MP H2 H4 ).
Solve_With H1.
For C Use (MP H3 H5).
Solve_With H1.
Qed.

Lemma ex_6_24 (A B C: Prop) : (A -> B) -> ((B -> C) -> (A -> C)).
Universal_Intros.
P_with_CP.
P_with_CP.
P_with_CP.
Write B Using (MP H1 H3). 
For C Use (MP H2 H4).
Solve_With H5.
Qed.

Lemma ex_6_25 (A B D C: Prop) : (A\/B) -> ((A -> C) -> ((B -> D) -> (C\/D))).
  Universal_Intros.
  P_with_CP.
  P_with_CP.
  P_with_CP.
  Case H1.
  Disjunc C (C\/D).
  For C Use (MP H2 H4).
  Solve_With H1.
  Disjunc D (C\/D).
  For D Use (MP H3 H5).
  Solve_With H1.
Qed.
  
Lemma p374_6_8 A B C: (A \/ B) /\ (A \/ C) /\ ~A -> B /\ C.
P_with_CP.
P_with_CP.
P_with_CP.
Write B Using (DS H1 H3).
Write C Using (DS H2 H3).
For (B/\C) Use (Conj H4 H5).
Qed.


Lemma p375_6_9 A B C D: ((A \/ B) -> (B /\ C)) -> ((B -> C) \/ D).
P_with_CP.
Disjunc (B->C) (B->C \/D).
P_with_CP.
Write (A\/B) Using (Add2 H2 A).
Write (B/\C) Using (MP H1 H3).
Write C Using (Simp_right H4). 
Qed.


Lemma ex_6_28 P Q: (~P\/Q) <-> (P -> Q).
Universal_Intros.
Split_Eq.
  P_with_CP.
  P_with_CP.
  For Q Use (DS H1 H2).
  P_with_CP.
  Pose (~P) For P. (* Pose uses the excluded middle axiom, not ID. This might be bad later *)
  Write Q Using (MP H1 H2).
  Solve_With H3.
  Disjunc (~P) (~P \/ Q).
  Solve_With H3.
Qed.
