from ply import lex, yacc

import lexer
from lexer import tokens


def p_stmt(p):
    'stmt : expr GOALINE expr'''
    p[0] = p[1] + ' ' + p[3]


def p_expr(p):
    '''expr : termlist
            | subgoal termlist
            | subgoal'''
    if len(p) == 3:
        p[0] = p[1] + ' ' + p[2]
    else:
        p[0] = p[1]


def p_subgoal(p):
    'subgoal : NUMBER SUBGOAL'
    p[0] = 'subgoal: ' + str(p[1])


def p_seplist(p):
    '''seplist : SEP seplist
               | SEP'''
    if len(p) == 3:
        p[0] = p[1] + p[2]
    else:
        p[0] = p[1]


def p_termlist(p):
    '''termlist : TERM termlist
                | seplist termlist
                | TERM'''
    if len(p) == 3:
        p[0] = p[1] + ' ' + p[2]
    else:
        p[0] = p[1]


def p_error(p):
    print p
    print "Syntax error in input!"


parser = yacc.yacc(debug=True)
