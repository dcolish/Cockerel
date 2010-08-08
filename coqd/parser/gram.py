"""
Gram
____

To use import the parser module object like so::

  from coq.parser.gram import parser

The grammar for Coqtop interpreter output. Our grammar is the following::

   S' -> proofst
   proofst -> subgoal hyp goal term_prompt
   proofst -> subgoal goal term_prompt
   proofst -> sysmsg term_prompt
   subgoal -> NUMBER SUBGOAL
   hyp -> ID COLON PROP hyp
   hyp -> ID COLON expr hyp
   hyp -> ID COLON PROP
   hyp -> ID COLON expr
   goal -> GOALINE quantified_expr
   goal -> GOALINE expr
   quantified_expr -> forall
   quantified_expr -> exists
   forall -> FORALL idlist COLON ID COMMA expr
   forall -> FORALL idlist COLON PROP COMMA expr
   exists -> EXISTS idlist COLON ID COMMA expr
   expr -> expr IMPL expr
   expr -> expr AND expr
   expr -> expr OR expr
   expr -> expr LARRW expr
   expr -> expr RARRW expr
   expr -> LPAREN expr RPAREN
   expr -> LBRKT expr RBRKT
   expr -> idlist
   idlist -> ID idlist
   idlist -> TILDE idlist
   idlist -> PLING idlist
   idlist -> ID
   term_prompt -> PROMPT proverstate PROMPT
   sysmsg -> PROOF idlist DOT
   proverstate -> thmname LARRW NUMBER PIPE thmlist NUMBER LARRW
   statelist -> PIPE thmlist
   thmlist -> thmname PIPE thmlist
   thmlist -> thmname PIPE
   thmname -> ID
   thmname -> ID NUMBER

"""
from ply import yacc

from lexer import tokens

__all__ = ['tokens', 'parser', 'precedence']


def p_proofst(p):

    """proofst : subgoal hyp goal term_prompt
               | subgoal goal term_prompt
               | sysmsg term_prompt
    """
    if len(p) == 5:
        p[0] = dict(subgoal=p[1],
                    hyp=p[2],
                    goal=p[3],
                    prompt=p[4])
    elif len(p) == 4:
        p[0] = dict(subgoal=p[1],
                    hyp=[],
                    goal=p[2],
                    sysmsg=[],
                    prompt=p[3])
    else:
        p[0] = dict(subgoal=[],
                    hyp=[],
                    goal=[],
                    sysmsg=p[1],
                    prompt=p[2])


def p_subgoal(p):
    """subgoal : NUMBER SUBGOAL
               | SUBGOAL"""
    p[0] = ' '.join((str(p[1]), str(p[2])))


def p_hyp(p):
    """hyp : ID COLON PROP hyp
           | ID COLON expr hyp
           | ID COLON PROP
           | ID COLON expr
           """
    hyp = [dict(name=p[1],
                type=p[3])]
    if len(p) == 5:
        p[0] = hyp + [p[4]]
    else:
        p[0] = dict(name=p[1],
               type=p[3])


def p_goal(p):
    """goal : GOALINE quantified_expr
            | GOALINE expr
    """
    p[0] = p[2]


def p_quantified_expr(p):
    """quantified_expr : forall
                     | exists"""
    p[0] = dict(quantified_expr=p[1])


def p_forall(p):
    """forall : FORALL idlist COLON ID COMMA expr
              | FORALL idlist COLON PROP COMMA expr
    """
    p[0] = dict(quantifier=p[1],
                identifiers=p[2],
                type=p[4],
                expr=p[6])


def p_exists(p):
    """exists : EXISTS idlist COLON ID COMMA expr
    """
    p[0] = dict(quantifier=p[1],
                identifiers=p[2],
                type=p[4],
                expr=p[6])


def p_expr(p):
    """expr : expr IMPL expr
            | expr AND expr
            | expr OR expr
            | expr LARRW expr
            | expr RARRW expr
            | LPAREN expr RPAREN
            | LBRKT expr RBRKT
            | idlist
            """
    if len(p) == 2 and p[1] is not None:
        p[0] = str(p[1])
    elif len(p) == 4:
        # We only care about the middle expr
        if p[1] == '(' or p[1] == '{':
            p[0] = dict(expr=p[2])
        else:
            p[0] = dict(operator=p[2],
                        expr=(p[1], p[3]))


def p_idlist(p):
    """idlist : ID idlist
              | TILDE idlist
              | PLING idlist
              | TRUE
              | FALSE
              | ID
              """
    if len(p) == 3:
        p[0] = ' '.join((str(p[1]), str(p[2])))
    else:
        p[0] = str(p[1])


def p_term_prompt(p):
    """term_prompt : PROMPT proverstate PROMPT"""
    p[0] = dict(thm=p[2],
                thmstate=p[3])


def p_sysmsg(p):
    """sysmsg : PROOF idlist DOT
              | PROOF COMPLETED DOT
              | thmname IS DEFINED"""
    p[0] = dict(msg=' '.join(p[1:]))


def p_proverstate(p):
    """proverstate : thmname LARRW NUMBER PIPE thmlist NUMBER LARRW"""
    p[0] = dict(proverline=p[2],
                thmname=p[3],
                thmlin=p[4])


def p_thmlist(p):
    """thmlist : thmname PIPE thmlist
               | thmname PIPE
               | PIPE
               """
    if len(p) == 4:
        p[0] = dict(names=' ,'.join((p[1], p[3]['names'])))
    else:
        p[0] = dict(names=p[1])


def p_thmname(p):
    """thmname : ID
               | ID NUMBER"""
    if len(p) == 2:
        p[0] = p[1]
    else:
        p[0] = ''.join([p[1], str(p[2])])


def p_error(p):
    try:
        raise TypeError("unknown text at %r %s" % (p.value, p))
    except:
        raise TypeError("unknown text at %s" % (p))

precedence = (
    ('left', 'OR', 'AND'),
    ('left', 'IMPL', 'RARRW', 'LARRW'),
    )

parser = yacc.yacc(debug=True)
