(* Lemmas directly from Hein's Book 
   There will eventually be a tactic to apply these 
   during the proof process *)

Require Import Tactics.

Lemma ex_6_19 P : (~~P) <-> P. 
Universal_Intros.
Split_Eq.
  P_with_CP.
  Pose (~P) For P.
  Contr H1 H.
  P_with_CP.
  Pose (~~P) For (~P).
  Contr H1 H.
  IP.
Qed.

Lemma ex_6_20 A B: (A \/ B) -> (~B -> A).
P_with_CP.
P_with_CP.
Pose (~A) For A.
DS H1 H4.
Contr H2 H3.
Qed.

Lemma ex_6_21 (A B: Prop): A -> (B\/A).
P_with_CP.
add1 H1 B.
Pose (~A) For (A). 
DS H2 H4.
add1 H3 A.
IP.
Qed.

Lemma ex_6_22 (A B:Prop): (A -> B) -> (~B -> ~A).  
  Universal_Intros.
  P_with_CP.
  P_with_CP.
  Pose(~~A) For (~A). 
  DN H4.
  MP H1 H4.
  Contr H2 H3.
Qed.

Lemma ex_6_23 (A B C:Prop): (A\/B) -> ((A -> C) -> ((B -> C) -> C)).
Universal_Intros. 
P_with_CP.
P_with_CP.
P_with_CP.
Pose (~C) For (C).
MT H2 H5.
DS H1 H5. 
MP H3 H4. 
IP.
Qed.

Lemma ex_6_24 (A B C: Prop) : (A -> B) -> ((B -> C) -> (A -> C)).
Universal_Intros.
P_with_CP.
P_with_CP.
P_with_CP.
MP H1 H3. 
MP H2 H4.
IP.
Qed.

Lemma ex_6_25 (A B D C: Prop) : (A\/B) -> ((A -> C) -> ((B -> D) -> (C\/D))).
  Universal_Intros.
  P_with_CP.
  P_with_CP.
  P_with_CP.
  (* We'll need a tactic to allow the reasoning by cases here *)
  (* Pose A For (A-> (C\/D)). *)
  destruct H1. MP H2 H. add1 H1 D. IP.
               MP H3 H. add2 H1 C. IP.
Qed.  
  
Lemma p374_6_8 A B C: (A \/ B) /\ (A \/ C) /\ ~A -> B /\ C.
P_with_CP.
P_with_CP.
P_with_CP.
DS H1 H3.
DS H2 H3.
Conj H4 H5.
Qed.


Lemma p375_6_9 A B C D: ((A \/ B) -> (B /\ C)) -> ((B -> C) \/ D).
P_with_CP.
bwd_Add.
P_with_CP.
add2 H2 A.
MP H1 H3.
Simp_right H4. (* Simp alone is too vague *)
Qed.


Lemma ex_6_28 P Q: (~P\/Q) <-> (P -> Q).
Universal_Intros.
Split_Eq.
  (* Case -> *)
  P_with_CP.
  P_with_CP.
  DS H1 H2.
  (* Case <- *)
  P_with_CP.
  (* Here is where the book starts to get it wrong, I have patched below*)
  (* Pose(~(~P\/Q)) For (~P\/Q). *)
  (* Pose (~P) For P. *)
  (* DS H H2. *)
  Pose (~P) For P.
  MP H1 H.
  IP.
  bwd_Add.
  IP.
Qed.
