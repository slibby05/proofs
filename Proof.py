from Match import unify
from AST import(Node,And,Or,Arrow,Not,Var,true,false)
from Exceptions import ProofException

####################################################################################
# This is a very small, and probably bad, proof checker for propositional logic
# The proof rules are the same ones we have in class.
#
#  A  B     A && B      A && B 
# ------/\I ------ /\EL ------/\ER
# A && B       A          B
#
#    A         B        A || B A -> C B -> C
# ------\/IL ------\/IR -------------------- \/E
# A || B     A || B              C
# 
# [A] B        A  A -> B
# ------ ->I  ----------- ->E
# A -> B           B
# 
# A -> F      A  ~A
# ------ ~I  ------- ~E
#   ~A          F
# 
#               F
# ----- TI   ------ FE  --------- LEM
#   T           A        A || ~A
#
# Each of the proof rules have a corresponding function
# so AndI() is the function for /\I rule
####################################################################################

##########################################
# 
# ------- Premise
#    A
#
# input e: any expression
# ouput: a proof of e
# careful, this will be added to the premises list
# so really you're proving e |- e
##########################################
def premise(e):
    global premises
    s = step(e,"Premise", [])
    premises.append(s)
    return s

##########################################
#  A  B     
# ------/\I
# A && B
#
# input a: a proof for A
# input b: a proof for B
# input ab: the expression And(A,B)
# output: a proof for And(a,b)
#
##########################################
def andI(a, b, ab):
    ret = step(ab, "/\I", [a,b])
    u = unify(And(Var("a"),Var("b")), ab)
    if u is None:
        raise ProofException("/\\I", ab, "conclusion is not in the form A /\\ B", ret)
    if u["a"] != a.expr:
        raise ProofException("/\\I", a, "left hand side doesn't match conclusion", ret)
    if u["b"] != b.expr:
        raise ProofException("/\\I", a, "right hand side doesn't match conclusion", ret)
    return ret

##########################################
# A && B     
# ------ /\EL
#    A       
#
# input ab: a proof for And(A,B)
# input a: the expression A
# output: a proof for A
#
##########################################
def andEL(ab, a):
    ret = step(a,"/\\EL", [ab])
    u = unify(And(Var("a"),Var("b")), ab.expr)
    if u is None:
        raise ProofException("/\\EL", ab.expr, "premise is not in the form A /\\ B", ret)
    if u["a"] != a:
        raise ProofException("/\\EL", a, "conslusion doesn't match left hand side of premise", ret)
    return ret

##########################################
# A && B     
# ------ /\ER
#    B       
#
# input ab: a proof for And(A,B)
# input b: the expression B
# output: a proof for B
#
##########################################
def andER(ab, b):
    ret = step(b,"/\\ER", [ab])
    u = unify(And(Var("a"),Var("b")), ab.expr)
    if u is None:
        raise ProofException("/\\ER", ab.expr, "premise is not in the form A /\\ B", ret)
    if u["b"] != b:
        raise ProofException("/\\ER", b, "conslusion doesn't match right hand side of premise", ret)
    return ret

##########################################
#    A      
# ------\/IL
# A || B    
#
# input a: a proof for A
# input ab: the expression Or(A,B)
# output: a proof for Or(A,B)
#
##########################################
def orIL(a, ab):
    ret = step(ab,"\\/IL", [a])
    u = unify(Or(Var("a"),Var("b")), ab)
    if u is None:
        raise ProofException("\\/IL", ab, "conclusion is not in the form A /\\ B", ret)
    if u["a"] != a.expr:
        raise ProofException("\\/IL", a.expr, "left hand side of conclusion doesn't match premise", ret)
    return ret

##########################################
#    B      
# ------\/IR
# A || B    
#
# input a: a proof for B
# input ab: the expression Or(A,B)
# output: a proof for Or(A,B)
#
##########################################
def orIR(b, ab):
    ret = step(ab,"\\/IL", [b])
    u = unify(Or(Var("a"),Var("b")), ab)
    if u is None:
        raise ProofException("\\/IR", ab, "conclusion is not in the form A /\\ B", ret)
    if u["b"] != b.expr:
        raise ProofException("\\/IR", b.expr, "right hand side of conclusion doesn't match premise", ret)
    return ret

##########################################
# A||B A->C B->C
# ---------------\/E
#       C              
#
# input ab: a proof for Or(A,B)
# input ac: a proof for Arrow(A,C)
# input bc: a proof for Arrow(B,C)
# input c: the expression C
# output: a proof for C
#
##########################################
def orE(ab, ac, bc, c):
    ret = step(c, "||R", [ab, ac, bc])
    uab = unify(Or(Var("a"),Var("b")), ab.expr)
    uac = unify(Arrow(Var("a"),Var("c")), ac.expr)
    ubc = unify(Arrow(Var("b"),Var("c")), bc.expr)
    if uab is None:
        raise ProofException("\\/E", ab, "premise doesn't match A \\/ B", ret)
    if uac is None:
        raise ProofException("\\/E", ac, "premise doesn't match A -> C", ret)
    if ubc is None:
        raise ProofException("\\/E", bc, "premise doesn't match B -> C", ret)
    if uab["a"] != uac["a"]:
        raise ProofException("\\/E", ab.expr, "A doesn't match: %s != %s" % (str(uab["a"]), str(uac["a"])), ret)
    if uab["b"] != ubc["b"]:
        raise ProofException("\\/E", ab.expr, "B doesn't match: %s != %s" % (str(uab["b"]), str(ubc["b"])), ret)
    if uac["c"] != ubc["c"]:
        raise ProofException("\\/E", ac.expr, "C doesn't match: %s != %s" % (str(uac["c"]), str(ubc["c"])), ret)
    if uac["c"] != c:
        raise ProofException("\\/E", c, "C doesn't match conclusion", ret)
    return ret

##########################################
# used in ->I rule
# 
# -----Assume
#   a        
#
# input a: an expression A
# output: a proof that we assumed A
#
##########################################
def assume(a):
    assumptions.append(a)
    return step(a, "assume", [])

##########################################
# 
# -----Assumed
#   a        
#
# input a: an expression A
# output: a proof that we have already assumed A
# Note: this will fail we we haven't already assumed A in the proof
#
##########################################
def assumed(a):
    ret = step(a, "assumed", [])
    if a not in assumptions:
        raise ProofException("assumption", a, "conclusion has not yet been assumed", ret)
    return ret

##########################################
# [A] B     
# ------ ->I
# A -> B    
#
# input a: a proof that we've assumed a
# input b: a proof of B that can use the assumption A
# input ab: a an expression A -> B
# output: a proof of A -> B
# Note: the removes A from the possible assumtions
#
##########################################
def arrowI(a, b, ab):
    ret = step(ab, "->I", [a,b])
    u = unify(Arrow(Var("a"),Var("b")),ab)
    if u is None:
        raise ProofException("->I", ab, "conclusion doesn't match A -> B", ret)
    if u["a"] != a.expr:
        raise ProofException("->I", a.expr, "left hand side doens't match conclusion", ret)
    if u["b"] != b.expr:
        raise ProofException("->I", b.expr, "right hand side doens't match conclusion", ret)
    if assumptions[-1] != a.expr:
        raise ProofException("->I", a, "A was not the last assumption made", ret)
    assumptions.pop()
    return ret

##########################################
#  A  A->B     
# --------- ->E
#    B
#
# input a: a proof a A
# input ab: a proof of A -> B
# input b: an expression B
# output: a proof of B
#
##########################################
def arrowE(a, ab, b):
    ret = step(b, "->E", [a,ab])
    u = unify(Arrow(Var("a"),Var("b")),ab.expr)
    if u is None:
        raise ProofException("->E", ab, "premise doesn't match A -> B", ret)
    if u["a"] != a.expr:
        raise ProofException("->E", a.expr, "left hand side doens't match", ret)
    if u["b"] != b.expr:
        raise ProofException("->E", b.expr, "conclusion doens't match right hand side", ret)
    return ret

##########################################
# A -> F   
# ------ ~I
#   ~A     
#
# input af: a proof of A -> F
# input na: a expression ~A
# output: a proof of ~A
#
##########################################
def notI(af, na):
    ret = step(na, "~I", [af])
    u = unify(Arrow(Var("a"),false()),af.expr)
    if u is None:
        raise ProofException("~I", af, "premise doesn't match A -> F", ret)
    if Not(u["a"]) != na:
        raise ProofException("~I", na, "conclusion doesn't match premise", ret)
    return ret
        
##########################################
#  A  ~A    
# ------- ~E
#    F      
#
# input a: a proof of A
# input na: a proof of ~A
# input f: a expression F
# output: a proof F
#
##########################################
def notE(a, na, f):
    ret = step(f, "~E", [a,na])
    u = unify(Not(Var("a")), na.expr)
    if u is None:
        raise ProofException("~E", na, "premise doesn't match ~A", ret)
    if u["a"] != a.expr:
        raise ProofException("~E", a, "premises don't match", ret)
    if f != false():
        raise ProofException("~E", f, "conclusion must be false", ret)
    return ret

#               F
# ----- TI   ------ FE  --------- LEM
#   T           A        A || ~A
##########################################
#           
# ------- TI
#    T      
#
# input t: the expression T
# output: a proof of T
#
##########################################
def TI(t):
    ret = step(t,"TI",[])
    if t != true():
        raise ProofException("TI", t, "conclusion must be true", ret)
    return ret

##########################################
#    F
# ------ FE
#    A     
#
# input f: a proof of F
# input a: an expression A
# output: a proof of A
#
##########################################
def FE(f, a):
    ret = step(a,"FE",[f])
    if f.expr != false():
        raise ProofException("FI", f.expr, "premise must be flase", ret)
    return ret

##########################################
# 
# --------- LEM
#  A || ~A
#
# input a: a expression (A || ~A)
# output: a proof of (A || ~A)
#
##########################################
def LEM(a):
    ret = step(a,"LEM",[])
    u = unify(Or(Var("a"),Not(Var("a"))), a)
    if u is None:
        raise ProofException("LEM", a, "conclusion doens't match A \\/ ~A", ret)
    return ret

#######################################################################################################
# You don't need to look at any of this.
# It's just internals the make the proof checker run.
#######################################################################################################


#######################################3
# These are global variables that
# make the proof checker work correctly.
# Really don't touch these.
#######################################3
premises = []
assumptions = []

# reset the global variables
def clear():
    global premises
    global assumptions
    premises = []
    assumptions = []


# This represents a step in a proof
# each step has an expression (the thing under the bar in the proof rule)
# the rule that was used
# and support (the proofs above the bar)
# While the expr is an expression, the support must all be steps
#
# Note: Since each of the supports is a step, this means that Step in an inductively defined structure.
# That means that Step is really a tree.
# So, our proofs are really trees, even though we're printing them out as a list of steps
class step():
    def __init__(self,expr,rule,support):
        self.expr = expr
        self.rule = rule
        self.support = support
        # used for printing the proof
        self.line = 0
 
    # reset the line numbers for this proof
    def reset(self):
        line = 0
        for s in self.support:
            s.reset()

    def max_assumptions(self):
        if self.rule == "assume":
            return 1
        return max([s.max_assumptions() for s in self.support], default=0)

    # prints out a proof
    # first we print what we've actually proven
    # then we do a preorder traversal of the proof tree to print the proof out
    def print_proof(self):
        global premises

        # print out the theorem that was actually proven
        # this might be different than you expect
        print("%s |- %s" % (", ".join([str(p.expr) for p in premises]), self.expr))

        # start the preorder traversal on line 1
        self.print_step(1, 0, self.max_assumptions())

        # Reset ourselfs, so we're consistent
        self.reset()

    def print_step(self, line_no, asms, max_asms):

        # print the children out first
        # since they were earlier steps in the proof
        for s in self.support:
            (line_no,asms) = s.print_step(line_no, asms, max_asms)

        # If we make a new assumption, the put it on the assumption stack
        if self.rule == "assume":
            asms += 1

        # If we are done with an assumption, then remove it from the assumption stack
        if self.rule == "->I":
            asms -= 1

        # set what line we're on
        # this is needed for any later steps
        self.line = line_no

        # print out a bar for each assumption we've made at this point
        for i in range(max_asms):
            if i < asms:
                print("|", end="")
            else:
                print(" ", end="")

        # print the actual step out in the form "line : expr | support"
        print("%5d: %60s | %10s" % (line_no, str(self.expr), self.rule), end = " ")
        for s in self.support:
            print("%d," % s.line, end=" ")
        print("")
        
        # move onto the next line
        return (line_no + 1, asms)

