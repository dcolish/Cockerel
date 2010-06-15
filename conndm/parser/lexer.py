from ply import lex

tokens = (
          'GOALINE',
          'NUMBER',
          'SEP',
          'SUBGOAL',
          'TERM',
          )

t_ignore = ' \t\n'


def t_error(t):
    print "Illegal character '%s'" % t.value[0]
    t.lexer.skip(1)


def t_NUMBER(t):
    r'\d+'
    t.value = int(t.value)
    return t


def t_SEP(t):
    r'[\:\,\<\>\~\-]'
    t.value = str(t.value)
    return t


def t_SUBGOAL(t):
    r'subgoal'
    t.value = str(t.value)
    return t


def t_GOALINE(t):
    r'[\=]+'
    t.value = str(t.value)
    return t


def t_TERM(t):
    r'[a-zA-Z0-9]+'
    t.value = str(t.value)
    return t

lex.lex()


# lex.input("""
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

# while True:
#     tok = lex.token() 
#     if not tok: 
#         break
#     print tok
