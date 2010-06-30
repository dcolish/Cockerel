from ply import yacc

import lexer
from lexer import tokens


def p_proofst(p):
    '''proofst : subgoal hyp goal
            | subgoal goal'''
    if len(p) == 4:
        p[0] = dict(subgoal=p[1],
                    hyp=p[2],
                    goal=p[3])
    else:
        p[0] = dict(subgoal=p[1],
                    goal=p[2])


def p_subgoal(p):
    '''subgoal : NUMBER SUBGOAL'''
    p[0] = ' '.join((str(p[1]), str(p[2])))


def p_hyp(p):
    '''hyp : ID ':' TERM
           | ID ':' expr
           '''
    p[0] = ' '.join((p[1], p[3]))


def p_goal(p):
    '''goal : GOALINE quantified_expr
    '''
    p[0] = p[2]


def p_quantified_expr(p):
    '''quantified_expr : forall
                     | exists'''
    p[0] = p[1]


def p_forall(p):
    '''forall : FORALL idlist COLON ID COMMA expr
              | FORALL idlist COLON PROP COMMA expr
    '''
    p[0] = ' '.join((p[1], p[2], p[4], p[6]))


def p_exists(p):
    '''exists : EXISTS idlist COLON ID COMMA
    '''
    p[0] = ' '.join((p[1], p[2], p[4]))


def p_expr(p):
    '''expr : expr IMPL expr
            | expr AND expr
            | expr OR expr
            | expr LARRW expr
            | expr RARRW expr
            | LPAREN expr RPAREN
            | LBRKT expr RBRKT
            | idlist
            '''
    if len(p) == 2 and p[1] is not None:
        p[0] = str(p[1])
    elif len(p) == 3:
        p[0] = ' '.join((str(p[1]), str(p[2])))
    elif len(p) == 4:
        p[0] = ' '.join((str(p[1]), str(p[2]), str(p[3])))
    elif len(p) == 5:
        p[0] = ' '.join((str(p[1]), str(p[4])))


def p_idlist(p):
    '''idlist : ID idlist
              | TILDE idlist
              | PLING idlist
              | ID
              '''
    if len(p) == 3:
        p[0] = ' '.join((str(p[1]), str(p[2])))
    else:
        p[0] = str(p[1])


def p_error(p):
    raise TypeError("unknown text at %r %s" % (p.value, p))

precedence = (
    ('left', 'OR', 'AND'),
    ('left', 'IMPL', 'RARRW', 'LARRW'),
    )

parser = yacc.yacc(debug=True)
