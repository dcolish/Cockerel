
Require Import Classical.
Require Import HypError.

Notation "A -> B" := (A->B) (at level 84, no associativity).

Axiom excluded_middle: forall P:Prop, P \/ ~P.
Axiom ID : forall P:Prop, (~P -> False) -> P.

(* This axiom does not export correctly *)
Axiom H0 : Prop.




Ltac Add1 H B :=
   let H' := fresh "H0" in
   let A := type of H in
   assert (H' : A \/ B); [ left; try assumption | ].

Ltac Add2 H B :=
   let H' := fresh "H0" in
   let A := type of H in
   assert (H' : B \/ A); [ right; try assumption | ].

Ltac Case A :=
  let H := fresh "H0" in
    let H' := fresh "H0" in
      destruct A as [H | H'].

Ltac Contr A B:= 
  try (apply A in B; contradiction) || apply B in A; contradiction ||
    idtac "No such contradiction found in the current proof".


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
    | ?A' => 
      match A' with
        | ~~_ => apply NNPP in H; try assumption
      end
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
  apply ID; intro H || FAILED H; NO_INTRO.


Ltac MP f x :=
   let H := fresh "H0" in
   let T := type of (f x) in
   assert (H : T); [ apply  (f x) | ].

Ltac MT H N := 
  let C := fresh "H0" in
    let P := type of H in  
      match P with
        | ?p -> ?q => 
          match type of N with
            | ~q => assert (C: ~q -> ~p); intros; [tauto |] ; apply C in N; clear C
            | ?T => idtac T "is not a negation of " q
          end
        | ?T => idtac T "was expected to be an implication" 
      end.

Ltac P_with_CP :=
   Universal_Intros;
   let H := fresh "H0" in
   let tmp := fresh "tmp" in
   match goal with
   | [ |- ?a /\ ?b -> ?c ] => intros [H tmp]; generalize tmp; clear tmp
   | [ |- ?a       -> ?c ] => intro H
   | [ |- ~?a -> _ ] => intro H
   | [ |- ~~?a -> _ ] => intro H
   | _ => idtac "[appropriate error message]"
   end
   || FAILED H.

Ltac Pose D For N :=
  let H := fresh "H0" in 
    let H' := fresh "H0" in 
      match D with
        | ~N =>
          destruct(excluded_middle N) as [H | H'] ; [try right; try assumption |]
            | ~D => idtac "You cannot pose that" D
            | _ => idtac "Not matching" D N
      end.

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


Ltac Universal_Intros :=
   (* Todo: insert a call to this macro into every tactic accessible by the student *)
   match goal with
   | [ |- forall _:Prop, _ ] => intro; Universal_Intros
   | _ => idtac
   end
   || NO_INTRO.

