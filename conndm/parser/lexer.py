from ply import lex


reserved = {'Theorem': 'THEOREM',
            'Goal': 'GOAL',
            'Proof': 'PROOF',
            'Prop': 'PROP',
            'forall': 'FORALL',
            'exists': 'EXISTS',
            'subgoal': 'SUBGOAL',
            'prompt': 'PROMPT',
            }


tokens = ('BSLSH',
          'CARET',
          'COLON',
          'COMMA',
          'DOT',
          'GOALINE',
          'HASH',
          'ID',
          'IMPL',
          'LARRW',
          'LPAREN',
          'LBRKT',
          'LBRAC',
          'NUMBER',
          'PIPE',
          'PLING',
          'QUERY',
          'RARRW',
          'RBRKT',
          'RBRAC',
          'RPAREN',
          'SCOL',
          'SEP',
          'SUBGOAL',
          'TERM',
          'TILDE',
          ) + tuple(reserved.values())


def t_ID(t):
    r'[a-zA-Z_][a-zA-Z_0-9]*'
    t.type = reserved.get(t.value, 'ID')    # Check for reserved words
    return t


t_ignore = ' \t\n'


def t_error(t):
    print "Illegal character '%s'" % t.value[0]
    t.lexer.skip(1)


def t_NUMBER(t):
    r'\d+'
    t.value = int(t.value)
    return t


def t_GOALINE(t):
    r'[\=]+'
    t.value = str(t.value)
    return t



t_BSLSH = r'/'
t_CARET = r'\^'
t_COLON = r':'
t_COMMA = r','
t_DOT = r'\.'
t_HASH = r'\#'
t_IMPL = r'->'
t_LARRW = r'\<'
t_LBRKT = r'\{'
t_LBRAC = r'\['
t_LPAREN = r'\('
t_PIPE = r'\|'
t_PLING = r'\!'
t_QUERY = r'\?'
t_RARRW = r'\>'
t_RBRAC = r'\]'
t_RBRKT = r'\}'
t_RPAREN = r'\)'
t_SCOL = r'\;'
t_TILDE = r'~'



lex.lex()

lex.input("""
Theorem foo (A:Prop) : A -> ~~A.

 
1 subgoal
  
  ============================
   forall A : Prop, A -> ~ ~ A

<prompt>foo < 2 |foo| 0 < </prompt> 
""")
# 1 subgoal
  
#   A : Prop
#   H : A
#   ============================
#    ~ ~ A

# """)






# # 1 subgoal
  
# #   ============================
# #    forall A : Prop, A -> ~ ~ A

# # """)

while True:
    tok = lex.token() 
    if not tok: 
        break
    print tok
