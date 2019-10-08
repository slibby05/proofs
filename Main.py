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
        arrTrans().print_proof()
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
    

def arrTrans():
    a = Var("A")
    b = Var("B")
    c = Var("C")

    p1 = premise(Arrow(a,b))
    p2 = premise(Arrow(b,c))

    a1 = assume(a)

    return arrowI(a1, \
                  arrowE(arrowE(assumed(a), \
                                p1, \
                                b), \
                         p2, \
                         c), \
                  Arrow(a,c))

    # linear (3-column) proof
    # l1 = assumed(a)
    # l2 = arrowE(l1, p1, b)
    # l3 = arrowE(l2, p2, c)
    # l4 = arrowI(a1, l3, Arrow(a,c))
    # return l4


if __name__ == "__main__":
    main()
