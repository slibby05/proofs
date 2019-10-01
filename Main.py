from sys import argv
from AST import (truth_table, Var, true, false, And, Or, Not, Arrow)
from Parser import parse
from Exceptions import (ProofException, EvalException, ParseException, LexException)
from Proof import (clear, step, premise, andI, andEL, andER, \
                   orIL, orIR, orE, assume, assumed, arrowI, arrowE, \
                   notI, notE, TI, FE, LEM)

def main():
    try:
        andComm().print_proof()
        orComm().print_proof()
        doubleNeg().print_proof()
    except (ProofException) as e:
        e.print()

####################################################
# Example of a proof of the commutativity of A && B
# 
# The proof of this would be
#
# A && B     A && B
# ------/\ER ------ /\EL
#    B         A
# ---------------- /\I
#      B && A
#
# Note: we need to stare every proof with clear()
# This is a hack to get things to work out right.
####################################################
def andComm():
    clear()
    a = Var("A")
    b = Var("B")
    p1 = premise(And(a,b))

    # The proof itself looks different, but it's really just on it's side.
    #
    # each proof rule is written as rule(support, expression)
    # since the andI rule B && A needs two pieces (B and A), we need the two proofs
    # the proof for B is andER, and the proof of A is andEL
    return andI(andER(p1, b), \
                andEL(p1, a), \
                And(b,a))
    
    # If we wanted, we could also write this proof as a linear proof
    # a = Var("A")
    # b = Var("B")
    # p1 = premise(And(a,b))
    # l1 = andEL(p1, a)
    # l2 = andER(p1, b)
    # l3 = andI(l2,l1,And(b,a))
    # return l3
    
def orComm():
    clear()
    x = Var("x")
    y = Var("y")
    p1 = premise(Or(x,y))
    l1 = assume(x)
    l2 = assumed(x)
    l3 = orIR(l2, Or(y,x))
    l4 = arrowI(l1,l3, Arrow(x,Or(y,x)))
    l5 = assume(y)
    l6 = assumed(y)
    l7 = orIL(l6, Or(y,x))
    l8 = arrowI(l5,l7, Arrow(y,Or(y,x)))
    l9 = orE(p1,l4,l8,Or(y,x))
    return l9

def doubleNeg():
    clear()
    a = Var("a")
    p1 = premise(Not(Not(a)))
    l1 = LEM(Or(a,Not(a)))
    l2 = assume(a)
    l3 = assumed(a)
    l4 = arrowI(l2,l3,Arrow(a,a))
    l5 = assume(Not(a))
    l6 = assumed(Not(a))
    l7 = notE(l6,p1,false())
    l8 = FE(l7,a)
    l9 = arrowI(l5,l8,Arrow(Not(a),a))
    l10 = orE(l1,l4,l9,a)
    return l10

if __name__ == "__main__":
    main()
