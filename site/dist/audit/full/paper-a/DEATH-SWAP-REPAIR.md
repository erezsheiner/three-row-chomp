# Independent correction of the death-swap identity

This corrects the all-mortal reading of catalogue entry `q-death-swap-gate`; it does not prove the open gate's sign.

Fix a mortal owner a, p=sigma_a. Let P be the physical hosts of private predeath p services, let V={h<a:sigma_h<=a+1}, S=P intersect V, and M={h<a:sigma_h>a+1 and h not in P}. Immortal death times are infinity. Put K=A(p)+A(a+1)-a.

The exact all-mortal identity is

    K = |S|-|M| + 1[p=a+1].

Proof. P is contained in {0,...,a-1} and |P|=A(p): p is served exactly on the predeath rows t<p with d(t)>p, one host per row and with no host reused. All diagonal values at most p have their owners below p, so the count of these rows is p-R(p)=A(p). Hosts precede a by the whole-history victim-host exclusion (at times before a this is automatic, at birth use FFD, and later use victim propagation).

Every blocker t<=a+1 has a unique victim s(t)<t. If t<=a then s(t)<a. The only possible victim among these that is not strictly below a is the victim a at t=a+1. It occurs if and only if p=a+1. Distinct blockers have distinct victims, because a column remains frozen after its death. Therefore |V|=A(a+1)-1[p=a+1].

P union V has complement M inside the a-element universe of older columns; P intersect V is S. Inclusion-exclusion gives |P|+|V|=a-|M|+|S|. Substitution proves the displayed identity. This covers a=1 and all immediate-death cases without a silent endpoint assumption.

When p>a+1 the indicator vanishes, recovering the original source's explicitly restricted identity. A C event implies a<t<sigma_h<p, hence p>=a+3, so the original C-to-gate consumer lies in this restricted branch. Nothing in this correction proves K>=0, an injection M to S, A1, or Q=o(n).

Exact boundary counterexample to the unrestricted catalogue formula: the first three canonical rows are [1], [2,3], [3,2,4]. At a=1, column1 dies at p=2. P={0}, V={}, S={}, M={}; A(2)=1. Thus K=1+1-1=1 whereas |S|-|M|=0. The missing indicator is exactly 1.

Publication correction: replace the current displayed formula by the all-mortal identity above and explicitly define P,V,S,M and p=sigma_a; alternatively retain the simpler displayed formula with the hypothesis p>a+1. Keep the proposed inequality K>=0 separately open.
