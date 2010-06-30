from parser.gram import parser

# s = """1 subgoal  A : Prop  H : A  ============================   ~ ~ A"""


s = """
1 subgoal
  
  ============================
   forall A : Prop, A -> ~ ~ A
"""

s = ' '.join(s.splitlines())
print s

result = parser.parse(s)
print result
