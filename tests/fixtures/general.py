

proof_responses = ("""
1 subgoal
  
  ============================
   forall A B  : Prop, A -> (~ ~ A)
""",
         """
1 subgoal
  
  ============================
   forall A B C : Prop, A -> ~ ~ A \/ B /\ C
""",
         """
1 subgoal
  A : Prop
  B : Prop
  C : Prop    
  ============================
   A -> ~ ~ A \/ B > C
""")
