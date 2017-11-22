Additional statistics
1. Unique names in ConstExp
   - reason: feasibility/size of the embedding matrix
2. Meta-level sharing, e.g., App(e, e) sharing
   - reason: for each ast, computation as distribution, unshared, vs size)
3. Object-level sharing, e.g., let x = 5 in let x = x + x in x
   - reason: show that substituting naively is either computationally feasible, or more likely, that this thing blows up

PL stuff:
1. A(e, e) metavariable
2. object vs. meta language
3. anormal/cps (probably don't need this)
4. description of ast (see code)

Tricks:
1. || e - f(e) || as regularization for fix-point
