"""
Lexer
-----
Token definitons for the Coqtop Output Language.

.. warning:: It is not meant to be used on its own and will not provide a useful
             language.

However you can use it with a parser by importing the tokens; to import the
tokens object::

  from coqd.parser.lexer import tokens

"""

from ply import lex

t_ignore = ' \t'

reserved = {'Theorem': 'THEOREM',
            'Goal': 'GOAL',
            'Proof': 'PROOF',
            'Prop': 'PROP',
            'completed': 'COMPLETED',
            'defined': 'DEFINED',
            'True': 'TRUE',
            'False': 'FALSE',
            'forall': 'FORALL',
            'exists': 'EXISTS',
            'subgoal': 'SUBGOAL',
            'prompt': 'PROMPT',
            'is': 'IS',
            'Exited': 'EXITED',
            'Qed': 'QED',
            }

tokens = ('OR',
          'CARET',
          'COLON',
          'COMMA',
          'DOT',
          'AND',
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
          'TERM',
          'TILDE',
          'BSLSH',
          ) + tuple(reserved.values())


def t_ID(t):
    # Ensure that reserved words are not overwritten with ID's
    r'[a-zA-Z_][a-zA-Z_0-9\']*'
    t.type = reserved.get(t.value, 'ID')    # Check for reserved words
    return t


def t_NUMBER(t):
    r'\d+'
    t.value = int(t.value)
    return t


def t_PROMPT(t):
    r'(<prompt>|</prompt>)'
    t.value = str(t.value)
    return t


def t_GOALINE(t):
    r'[\=]+'
    t.value = str(t.value)
    return t


def t_error(t):
    print "Illegal character '%s'" % t.value[0]
    t.lexer.skip(1)


def t_newline(t):
    r'\n+'
    t.lexer.lineno += len(t.value)


t_OR = r'\\/'
t_CARET = r'\^'
t_COLON = r':'
t_COMMA = r','
t_DOT = r'\.'
t_AND = r'/\\'
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
t_BSLSH = r'/'

lex.lex()


if __name__ == '__main__':

    # A little unit test for the lexer
    s = ("""
1 subgoal

  ============================
   forall A B  : Prop, A -> (~ ~ A) \/ B
<prompt>Unnamed_thm < 2 |Unnamed_thm| 0 < </prompt>
""",
"""
1 subgoal
  
  ============================
   True -> True

<prompt>Unnamed_thm < 2 |Unnamed_thm| 0 < </prompt> 
""",
)
    lex.input(s[1])

    while True:
        tok = lex.token()
        if not tok:
            break
        print tok
