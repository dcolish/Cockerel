
Require Import Classical.
Require Import HypError.

Notation "A -> B" := (A->B) (at level 84, no associativity).

Axiom excluded_middle: forall P:Prop, P \/ ~P.
Axiom ID : forall P:Prop, (~P -> False) -> P.

(* This axiom does not export correctly *)
Axiom H0 : Prop.

Ltac Universal_Intros :=
   (* Todo: insert a call to this macro into every tactic accessible by the student *)
   match goal with
   | [ |- forall _:Prop, _ ] => intro; Universal_Intros
   | _ => idtac
   end.
   (* || NO_INTRO. *)


Ltac Addition1 H B :=
   let H' := fresh "H0" in
   let A := type of H in
   assert (H' : A \/ B); [ left; try assumption | ].

Ltac Addition2 H B :=
   let H' := fresh "H0" in
   let A := type of H in
   assert (H' : B \/ A); [ right; try assumption | ].

(** Hein's "Proof by Cases", derived rule on p434 *)
(** Todo: this tactic introduces a spurious duplicate hypothesis called "x" -- remove it if possible, or parse around it *)
Ltac Case A :=
  let H := fresh "H0" in
  refine (match A with
          | or_introl x => _ x
          | or_intror x => _ x
          end); intro H.

(*
Ltac Case A :=
  let H := fresh "H0" in
    let H' := fresh "H0" in
      destruct A as [H | H'].
*)

Ltac Contr A B :=
  let H := fresh "H0" in
           (assert (H:False) ; [ exact (A B) | ] )
        || (assert (H:False) ; [ exact (B A) | ] )
        || let TA := type of A in
           let TB := type of B in 
           idtac "In order to contradict" TA "you can provide ~"TA ", in order to contradict" TB "you can provide ~"TB.


Ltac Conj L R :=
   Universal_Intros;
   let TL := type of L in
   let TR := type of R in
   let H := fresh "H0" in
   assert (H: TL /\ TR)
   ; [ apply conj; assumption | try assumption ]
   || FAILED (L/\R).



Ltac DS D N :=
   let H := fresh "H0" in
     match type of N with
       | ~ ?A' =>
         match type of D with
           | ?A \/ ?B =>
             match A with
               | A'  => idtac "Using ~"A' "to prove" B; assert(H:B); [tauto | try assumption]
             end ||
             match B with 
               | A' => idtac "Using ~"A' "to prove" A; assert (H:A); [tauto | try assumption]
             end ||
             idtac "1: This failed"
           | ?T => idtac "The justification" T "is expected to be a disjunction: _ \/ _"
         end
       | ?A' =>
         match type of D with
           | ?A \/ ?B =>
             match A with
               | ~A'  => idtac "Using" A' "to prove" B; assert(H:B); [tauto | try assumption]
             end ||
             match B with 
               | ~A' => idtac "Using" A' "to prove" A; assert (H:A); [tauto | try assumption]
             end ||
             idtac "2: This failed"
           | ?T => idtac "The justification" T "is expected to be a disjunction: _ \/ _"
         end
     end ||
     idtac "No such contradiction found in the current proof".


Ltac DN H :=
  Universal_Intros;
  let H1 := fresh "H0" in
  match type of H with
    | ~~?A => assert (H1:A); [ apply Classical_Prop.NNPP ; assumption | ]
    (* | H => intros H1; apply H1; try assumption *)
    | _ => idtac "Double Negation can not solve this problem" H
  end.


Ltac Disjunc A B :=
  match goal with
    | [ |- B ] => match B with 
                    | A \/ ?D => left
                    | ?C \/ ?D => right; Disjunc A D
                    | A => idtac
                    | _ => idtac "You must provide a disjunction, which" B "is not"
                  end
    | _ => idtac "Failed to find" B "in your current goal"
  end.

Ltac IP := 
  let H := fresh "H0" in 
  apply ID; intro H. (* || FAILED H; NO_INTRO. *)



Ltac raw_pose D N :=
  let H := fresh "H0" in 
    let H' := fresh "H0" in 
      match D with
        | ~N =>
          destruct(excluded_middle N) as [H | H'] ; [try right; try assumption |]
            | ~D => idtac "You cannot pose that" D
            | _ => idtac "Not matching" D N
      end.

Tactic Notation "Pose" constr(A) "For" constr(B) := raw_pose A B.

Ltac Simp_right C :=
   let H := fresh "H0" in
   let P := type of C in
   match P with
   | ?l /\ ?r => assert (H:r); [ destruct C; assumption | try assumption ]
   | _ => idtac "[insert appropriate error message]"
   end.

Ltac Solve_With H :=
  (* I'm not sure this is a tactic that should be pushed up *)
  apply H || FAILED H.


Ltac Split_Eq :=
  split || idtac "Cannot Split a non conjuctive statement".

(**
Tactics that reflect the inference rules in Hein 6.3.1
p422


*)


Ltac Conditional_Proof :=
   Universal_Intros;
   let H := fresh "H0" in
   let tmp := fresh "tmp" in
   match goal with
   (* Hein has one incredibly bizarre usage of CP on page ... (Todo) *)
   | [ |- ?a /\ ?b -> ?c ] => intros [H tmp]; generalize tmp; clear tmp
   (* The typical usage *)
   | [ |- ?a       -> ?c ] => intro H
   (* Todo: why is this here? *)
   | [ |- ~?a -> _ ] => intro H
   (* Todo: why is this here? *)
   | [ |- _ -> _ ] => intro H
   (* Todo: why is this here? *)
   | [ |- ~~?a ] => intro H
   (* Error handling *)
   | _ => idtac "[appropriate error message]"
   end.
   (* || FAILED H. *)

Ltac CP := Conditional_Proof.

(** A → B, A ⊦ B *)
Ltac Modus_Ponens f x :=
   let H := fresh "H0" in
   let Tf := type of f in
   match Tf with
   | ?A -> ?B => let Tx := type of x in
                 (assert (H : B); [ exact  (f x) | ]) || idtac "The antecedent (" A ") of the implication (" f ":" Tf ")  does not match the type (" Tx ")"
   | ?T        => idtac f "must refer to an implication (of the form _ -> _), but instead has the form " T
   end.

Ltac MP f x := Modus_Ponens f x.

(** A → B, ~B ⊦ ~A *)
Ltac Modus_Tollens H N := 
  let C := fresh "H0" in
  let X := fresh "X" in
    let TH := type of H in  
      match TH with
        | ?p -> ?q => 
          match type of N with
            (* This line is erroneous: it does an in-place substitution of one negation with another. 
            | ~q => assert (C: ~q -> ~p); intros; [tauto |] ; apply C in N; clear C
            * instead, we want to add a new hypothesis *)
            | ~q => assert (C: ~p); [ intro X; apply N; apply H; apply X | ]
            | ?T => idtac T "is not a negation of " q
          end
        | ?T => idtac "the first argument (" H ") needs to be an implication (_ -> " 
      end.

Ltac MT H N := Modus_Tollens H N.

(** Original Rules *)
(** Conjunction:               A, B ⊦ A ∧ B *)
(** Simplification L:         A ∧ B ⊦ A *)
(** Simplification R:         A ∧ B ⊦ B *)
(** Addition L:                   A ⊦ A ∨ B *)
(** Addition R:                   B ⊦ A ∨ B *)
(** Disjunctive Syllogism:  A∨B, ~A ⊦ B *)
(** Double Negation E:          ~~A ⊦ A *)
(** Double Negation I:            A ⊦ ~~A *)
(** Contradiction:            A, ~A ⊦ False *)
(** Indirect Proof: from ~A derive False ... conclude A *)

(** HS:    A→B, B→C ⊦ A→C *)
(** CD:    A∨B, A→C, B→D ⊦ C∨D *)
(** CD:    A∨B, A→C, B→D ⊦ C∨D *)


