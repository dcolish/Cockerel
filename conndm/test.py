from parser.gram import parser

# s = """1 subgoal  A : Prop  H : A  ============================   ~ ~ A"""


s = """
Theorem foo (A:Prop) : A -> ~~A.

 
1 subgoal
  
  ============================
   forall A : Prop, A -> ~ ~ A

 <prompt>foo < 2 |foo| 0 < </prompt> 
"""

s = ' '.join(s.splitlines())
print s

result = parser.parse(s)
print result
