from ply import yacc

from lexer import tokens

__all__ = ['tokens', 'parser', 'precedence']


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
    '''hyp : ID COLON PROP hyp
           | ID COLON expr hyp
           | ID COLON PROP
           | ID COLON expr
           '''
    hyp = [dict(name=p[1],
                type=p[3])]
    if len(p) == 5:
        p[0] = hyp + [p[4]]
    else:
        p[0] = dict(name=p[1],
               type=p[3])


def p_goal(p):
    '''goal : GOALINE quantified_expr
            | GOALINE expr
    '''
    p[0] = p[2]


def p_quantified_expr(p):
    '''quantified_expr : forall
                     | exists'''
    p[0] = dict(quantified_expr=p[1])


def p_forall(p):
    '''forall : FORALL idlist COLON ID COMMA expr
              | FORALL idlist COLON PROP COMMA expr
    '''
    p[0] = dict(quantifier=p[1],
                identifiers=p[2],
                type=p[4],
                expr=p[6])


def p_exists(p):
    '''exists : EXISTS idlist COLON ID COMMA expr
    '''
    p[0] = dict(quantifier=p[1],
                identifiers=p[2],
                type=p[4],
                expr=p[6])


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
    elif len(p) == 4:
        # We only care about the middle expr
        if p[1] == '(' or p[1] == '{':
            p[0] = dict(expr=p[2])
        else:
            p[0] = dict(operator=p[2],
                        expr=(p[1], p[3]))


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
