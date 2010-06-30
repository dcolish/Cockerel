from parser.gram import parser


def do_parse(s):
    s = ' '.join(s.splitlines())
    print s

    result = parser.parse(s)
    print result


if __name__ == '__main__':

    s = ("""
1 subgoal
  
  ============================
   forall A B  : Prop, (A -> (~ ~ A) \/ B)
""",
         """
1 subgoal
  
  ============================
   forall A B C : Prop, A -> ~ ~ A \/ B /\ C
""",
         """
1 subgoal
  
  ============================
   forall A B C : Prop, A -> ~ ~ A \/ B > C
""")

    for x in s:
        do_parse(x)
