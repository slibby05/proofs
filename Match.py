from AST import(Node,And,Or,Arrow,Not,Var,true,false)

###################################################################
# This file contains code for pattern matching
# If I want to know if an expression e matches
# And(a,b)
# Then I call unify(And(a,b), e)
# If I get anything back, then they match
# Furthermore I'll get back a "unifyer"
# This is just a dictionary that tells me the expression
# each variable matched with
# so if mgu = unify(And(a,b), And(Or(c,d), Not(d))
# then mgu["a"] == Or(c,d)
# and mgu["b"] == d
###################################################################

def unify(a, b):
    # if one side is a variable, we're done
    # I should probably do an occurrs check, but eh.
    if a.type() == Node.VAR:  return {a.name : b}
    if b.type() == Node.VAR:  return {b.name : a}

    # If the types of nodes are different, then they don't unify
    if a.type() != b.type():
        return None

    # if both nodes are a not, then we only need to check one subterm
    if a.type() == Node.NOT:
        return unify(a.lhs, b.lhs)

    # for any binary node, we need to check both subterms
    # and we need to merge their unifiers together
    if a.type() in [Node.AND, Node.OR, Node.ARROW]:
        return merge(unify(a.lhs,b.lhs), unify(a.rhs,b.rhs))

    # if they're literals, then we check the values
    if a.type() == Node.LIT and a.val == b.val:
        return {}

    # These are the only possibilities for unification, so if we get here we failed.
    return None

# Find all occurrences of a variable v in e, and replace them with sigma[v]
def sub(e, sigma):

    # our substitution is empty, so we just give up.
    if sigma is None:
        return None

    # we found a variable in our substitution, so replace it.
    if e.type() == Node.VAR and e.name in sigma:
        return sigma[e.name]

    # in any other case, just substitute the subterms
    if e.type() == Node.AND:   return And(  sub(e.lhs, sigma), sub(e.rhs, sigma))
    if e.type() == Node.OR:    return Or(   sub(e.lhs, sigma), sub(e.rhs, sigma))
    if e.type() == Node.ARROW: return Arrow(sub(e.lhs, sigma), sub(e.rhs, sigma))
    if e.type() == Node.NOT:   return Not(  sub(e.lhs, sigma))

    # if we made it here, there's no subterms, so we're done
    return e

# Merge two substitutions together
# this is tricky, because they might share variables
def merge(sl, sr):
    # at least on substitution is empty.
    # We failed, so we give up.
    if sl is None or sr is None:
        return None

    # our new substitution
    s = {}
    # variables shared between the two
    shared = set(sl) & set(sr)

    # for each shared varible, try to unify them
    # If they can't be unified, then give up
    # If they can, then the substitution should really be
    # The unification of the two variables.
    for k in shared:
        t = unify(sl[k],sr[k])
        if t is None:
            return None
        else:
            s[k] = sub(sl[k], t)


    # for any unshared variable, we can just add it in.
    for k in set(sl) - shared:
        s[k] = sl[k]

    for k in set(sr) - shared:
        s[k] = sr[k]

    return s

