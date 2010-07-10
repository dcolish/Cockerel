(* Main wrapper for all Hypotheical Reasoning Libraries *)
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


Require Export HypError.
Require Export HypNotation.
Require Export HypTactics.
Require Export HypLemmas.

(* Example or_swaps P Q :(P \/ Q) <-> (Q \/ P).  *)
(*   split; intro; destruct H; [right | left | right | left]; assumption. Qed. *)

(* Example ds_unit_1 P Q:  (P\/Q) -> (~P->Q).  *)
(* P_with_CP. P_with_CP. DS H1 H2. Qed. *)

(* Example ds_unit_2 P Q:  (~P\/Q) -> (P->Q).  *)
(* P_with_CP. P_with_CP. DS H1 H2. Qed. *)

(* Example ds_unit_3 P Q:  (P\/Q) -> (~Q -> P).  *)
(* P_with_CP. P_with_CP. DS H1 H2. Qed. *)

(* Example ds_unit_4 P Q:  (P\/~Q) -> (Q -> P).  *)
(* P_with_CP. P_with_CP. DS H1 H2. Qed. *)
