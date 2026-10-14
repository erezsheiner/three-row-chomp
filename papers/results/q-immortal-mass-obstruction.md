# Mortal-only matching cannot pay the required short-block endpoint budget

**Statement.** Let I_imm count the J and immortal-H2 residual tokens. Then I_imm([ceil(N/7),2N))>=N^2/98-O(N). Any matching that only adds mortal-owner edges leaves these isolated and cannot have U([q, q+ceil(sqrt q)-1])=O(q) uniformly for all large q.

## Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Ghost tokens, owner transport and the exact unpaid endpoints](../supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

## Hypotheses and scope

- Canonical positive-MEX/COPY three-row Chomp history, with the structural facts proved in the shared canonical foundation review.
- Canonical history; Imm(x) counts immortal indices strictly below x.
- The obstruction is specific to mortal-only completion, not to all matchings or Q=o(n).

## Argument

1. P50 derivation: predeath p_j hosts plus earlier frozen hosts cover[0, s_j), giving s_j<=2j-1. A mortal victim s_i never awards above p_i+s_i; if p_i+s_i<p, it is below s(p) by P43 and cannot be a p host. Hence s(p)>=A(p)+#{i:p_i+s_i<p}. Under A>=alpha x-C, p_i<=(i+C)/alpha and s_i<=2i-1; use p_j>=2j to obtain s_j>=((1+4alpha)/(1+2alpha))j-O(1). Counting distinct victim ranks below x yields Imm(x)>=2alpha/(1+4alpha)x-O(1); alpha1/3 gives2/7.

2. For immortal h<a, diagonal deadline y=d(a) forces a unique private y service at h before y. It is not at birth a. If service time t>a, assign actual J cell(t, h); if t<a, assign H2(a, t), which exists by d(t)>y. Row injectivity and diagonal injectivity make ordered pairs(h, a) inject into these tokens. Token date lies[a,2a].

3. Restrict both immortal indices to[b, N), b=ceil(N/7). Their count>=2N/7-b-O(1)>=N/7-O(1). The binomial number of ordered earlier/later pairs is>=N^2/98-O(N), with dates in[b,2N).

4. The annulus is covered by O(sqrt N) consecutive legal forward sqrt-window blocks, allowing final overhang. Uniform U=O(q)=O(N) would total O(N^(3/2)), contradicting quadratic isolated mass. This uses uniformity over all large q, not one favorable sequence of windows.

## Review and supporting evidence

- Historical original-claim verdict: accepted.
- This statement was independently audited on paper. The audit did not produce a new Lean formalization of the derived statement; its listed formal dependencies have separate verification receipts.
- [Renewed statement and proof-completeness review](../../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../../audit/full/paper-a/q-immortal-mass-obstruction.json)
- [Shared canonical foundation and exact Lean bridges](../../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Ghost tokens, owner transport and the exact unpaid endpoints](../supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)
