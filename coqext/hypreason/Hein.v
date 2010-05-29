(**
This is an attempt at partially formalizing one of the systems in Hein's
book.

Questions:
 - How widely applicable is this style of proof?
 - What other styles of proof does he use, and are they worth formalizing?
    - One is equational reasoning
 - Is another proof tool more appropriate?
    - Isabelle (which can be customized to a specific logic)
    - Alfa, which might be customizable, but regardless is really cool
      because it's a syntax-tree editor so syntax errors are (nearly)
      impossible

With this draft there are some issues.  The only reason these are issues
is because I'm making the assumption that we don't want to burdon the 
students with learning anything about the tool, and instead we want
something whose look and feel correspond to the text as close as possible.
  - Some tactics are slightly ambiguous: eg Simpl has to be made into
    Simpl_left and Simpl_right
  - Some tactics are highly ambiguous: eg T will need to have an
    explicit reference to the previous result
  - In order to reuse a previous result (for instance with Hein's
    "T") we need to generalize and then instantiate that previous
    result.  The simplest way is to explicitly list all props in 
    the declaration of the theorem.

Other things:
  - The tactic language Ltac allows us to give very good diagnostic
    messages when a student tries something inappropriate. (see DS).
  - We'd have to categorize the tactics as forward reasoning (eg Cong),
    backward reasoning (bwd_Add), and mixed (P_with_CP).  Might be
    initially confusing, but it's a good thing for students to
    understand

Related work.
 - we used a vastly simplified version of Mizar (http://mizar.uwb.edu.pl/)
   for an intro course at the U of Alberta.  It sucked, but only because
   students were challenged by their syntax errors, not by their logic
   errors.  
*)


(** The use of [H0] as an axiom name, together with the use of [fresh "H0"]
  in the tactics allows us to name intermediate results consistently with
  those in Hein's book.

  A proof a la Hein appears in one pane of the Coq browser (sadly,
  when you finish the proof, it disappears a bit too early).
*)

Require Import Classical.


Axiom H0 : Prop.
Variable P Q : Prop.


Ltac Universal_Intros :=
   (* Todo: insert a call to this macro into every tactic accessible by the student *)
   match goal with
   | [ |- forall _:Prop, _ ] => intro; Universal_Intros
   | _ => idtac
   end.

  Ltac Solve_With_Double_Negation :=
    Universal_Intros;
    let H := fresh "H0" in
    match goal with
    | [ |- ~ ?a <> ?a ] => intros H; apply H ; reflexivity
    | [ |- ?T ] => idtac "Double Negation could not be applied to" T
    end.

  Ltac Apply_Double_Negation D :=
    Universal_Intros;
    let H := fresh "H0" in
    match D with
    | ~~ ?A => apply NNPP in H
    | ?T => idtac "Double Negation could not be applied to" T
    end.



  Example Simple_Neg : ~~P = P. Solve_With_Double_Negation. Qed.
  
  Example More_Neg : ~~ (P /\ Q) -> P /\ Q. intro. Apply_Double_Negation H.
  

Ltac P_with_CP :=
   Universal_Intros;
   let H := fresh "H0" in
   let tmp := fresh "tmp" in
   match goal with
   | [ |- ?a /\ ?b -> ?c ] => intros [H tmp]; generalize tmp; clear tmp
   | [ |- ?a       -> ?c ] => intro H
   | _ => idtac "[appropriate error message]"
   end.

Ltac Conj L R :=
   Universal_Intros;
   let TL := type of L in
   let TR := type of R in
   let H := fresh "H0" in
   assert (H: TL /\ TR)
   ; [ apply conj; assumption | try assumption ]
   .


Ltac DS D N :=
   let H := fresh "H0" in
   match type of D with
   | ?A \/ ?B =>
      match type of N with
      | ~ A => idtac
              ; assert (H:B)
              ; [tauto | try assumption ]
      | ~ ?A' => idtac "[insert appropriate error message]"
      | ?T => idtac "The justification" N "proves" T "but is expected to be a negation: ~ _ "
      end
   | ?T => idtac "The justification" D "proves" T ", but is expected to be a disjunction: _ \/ _"
   end.

Ltac bwd_Add := left.

Ltac add H A :=
   let H' := fresh "H0" in
   let B := type of H in
   assert (H' : A \/ B); [ right; assumption | ].

Ltac MP f x :=
   let H := fresh "H0" in
   let T := type of (f x) in
   assert (H : T); [ apply  (f x) | ].

Ltac Simp_right C :=
   let H := fresh "H0" in
   let P := type of C in
   match P with
   | ?l /\ ?r => assert (H:r); [ destruct C; assumption | try assumption ]
   | _ => idtac "[insert appropriate error message]"
   end.

