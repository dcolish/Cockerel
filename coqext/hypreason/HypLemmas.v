(* Lemmas directly from Hein's Book 
   There will eventually be a tactic to apply these 
   during the proof process *)

Require Export HypTactics.

Axiom H0 : Prop.

(* Ltac Parse_Step A B := *)
(*   match goal with  *)
(*     | [|- A ] =>  assert(A); [B |tauto] *)
(*     | ?T => idtac "You must state a valid goal to make progress," A "is not valid" *)
(*   end. *)

(* a tactic sort of like this should work well to push through 
   any asserts we need for the forward style *)

(* This language should be used to add new hypothesis
   without changing the goal state *)
Tactic Notation "Write" constr(A) "Using" tactic(B) := 
  assert (H:A); [tauto | B; clear H ].  

(* This language should be used to clear or modfiy goals *)
Tactic Notation "For" constr(A) "Use" tactic(B) :=
  let H:= fresh "H0" in
  assert (H:A); [B | tauto].

(* add tactic for testing if a goal is trivial *)

Lemma ex_6_19 P : (~~P) <-> P. 
Universal_Intros.
Split_Eq.
  P_with_CP.
  For P Use IP.
  For False Use (Contr H1 H2).
  P_with_CP.
  intro H2.
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
add1 H1 B.
fwd_Add.
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

Ltac Case A :=
  let H := fresh "H0" in
    let H' := fresh "H0" in
      destruct A as [H | H'].


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
  (* We'll need a tactic to allow the reasoning by cases here *)
  (* Pose A For (A-> (C\/D)). *)
  Case H1.
  bwd_Add.
  For C Use (MP H2 H4).
  Solve_With H1.
  fwd_Add.
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
bwd_Add.
P_with_CP.
Write (A\/B) Using (add2 H2 A).
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
  Pose (~P) For P. (* Pose uses the excluded middle axiom, not IP. This might be bad later *)
  Write Q Using (MP H1 H2).
  Solve_With H3.
  bwd_Add.
  Solve_With H3.
Qed.
