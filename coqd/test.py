from pprint import PrettyPrinter

from parser.gram import parser
from json import JSONEncoder

pp = PrettyPrinter(indent=4)


def do_parse(s):
    s = ' '.join(s.splitlines())
    print s

    result = parser.parse(s)
    pp.pprint(result)
    foo = JSONEncoder().encode(result)
    print foo

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
  A : Prop
  B : Prop
  C : Prop    
  ============================
   A -> ~ ~ A \/ B > C
""")

    for x in s:
        do_parse(x)
