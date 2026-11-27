# Phase quotients, one-sided phase order, and a binary defect equation

## 1. Phase-identification algebra

Use H=(0,0,0,1,0,0,1), physical impulses H[p+1]-H[p], and normalized positive height z. U grows on even z and shrinks on odd z; T grows on odd z and shrinks on even z. In either branch the update is (m*z+s)/2, s=z mod 2, m=3 iff s=H[p]. Both letters are surjective on positive integers by their shrink inverses S_U(y)=2y-1 and S_T(y)=2y. Let P_p(z) be the actual capture indicator of the known phased cycle (1,1,1,1,2,3,2).

Invariance gives P_p=P_(p+1) composed with M_p. If H[i]=H[j], then P_i=P_j iff P_(i+1)=P_(j+1). The same equivalence holds with pointwise <= in place of equality (precomposition preserves order; surjectivity permits its cancellation). This uses the true fixed physical rule only.

A proposed equality P_i=P_j gives a phase equivalence partition by transitivity and forward/backward transport across equal letters. Quotient the seven phase vertices by these identities. The original tick edges become labeled edges in the quotient graph. For any closed word at a quotient vertex, the label at that class is invariant under the corresponding composition of U/T maps. A move between different representatives of a class is justified only by the hypothesized equality and its valid consequences. It is NOT a physical phase jump, and a controller word need not be a legal history of the original fixed map.

### All 21 phase comparisons suffice

The six comparisons (0,4),(1,4),(1,5),(2,5),(2,6),(3,6) force all seven phases equal by pure finite closure. Once all labels coincide, at each height choose whichever of U or T shrinks, giving ceil(z/2). This terminates at z=1, whose phase-zero label is 1.

For every other comparison, the exact verifier constructs a finite disjoint dyadic partition on which there is a closed quotient word with a strictly smaller positive endpoint, except an explicitly bounded initial portion of the ray. Those finite exceptions are directly captured at phase i in the original fixed physical system. Hence strong induction on z proves capture at phase i conditional on the initial universal equality. Every other phase reaches phase i within six true ticks.

The consumer generates the closure, enumerates closed words at depth k and refines only unresolved cylinders. At stride M=2^k a closed word of length k has exact affine output a*v+b' on z=M*v+b, 1<=b<=M. Accept a<M on the complete tail v>=max(0,floor((b'-b)/(M-a))+1). For the finitely many smaller v use literal capture. Each accepted word is independently replayed in the signed physical coordinate with the *conditional* sequence of height bits; this verifies the numerical composition, while the quotient graph validates every label-preserving jump. The partition is checked by lifting all accepted residues to the largest depth, checking pairwise disjointness and exact coverage. Counts: 223 whole-ray rules, 41 literal finite-base checks (repeated base cases across different comparisons counted again), maximum depth 15. Six pure-closure comparisons need no rays. No failed or hypothetical rule is credited. Neither the count nor the word lengths are claims of optimality.

**Theorem.** For this fixed word, for EVERY distinct i,j in {0,...,6}, global capture is equivalent to the universal equality P_i(z)=P_j(z) for z>=1. This is an equivalent frontier, not a proof of its premise.

Example: P0=P1 implies P0=P1=P2=P3 by the consecutive U's. Denote their common label by L. Then L is invariant under U and the chronological word W=TUUT (from phase3 to phase0). For odd z>=3, U(z)<z. For even z=16v+r, r in {2,4,6,10,12,14,16}, W(z) is respectively 3v+2,3v+1,9v+5,v+1,9v+8,3v+3,9v+9, all smaller except z=2. For z=32v+8, W(U(z))=27v+8 (<z if v>0); for z=32v+24 it is 9v+7. The remaining z=2,8 are captured by literal histories (or conditional U,W compositions). This explains the small conditional controller by the actual two U-block structure.

Generalize the same construction to arbitrary periodic binary words: quotient by a proposed phase relation and certify a terminating control policy at a quotient class. The checker explores several other schedules through depth15. For alternate TUTUTUU, all 21 conditional affine-tail controllers close by depth10, six by pure closure; finite bases were not replayed there. For the two other two-T gap patterns TTUUUUU and TUTUUUU, respectively 18 and16 out of21 pairs close at the selected cap. These are conditional numerical control tests, not a ranking of actual convergence difficulty, and not all-seed results. The UTT two-cycle negative control passes all three conditional affine-tail tests; two disjoint true cycles are independently replayed. A conditional phase-controller theorem cannot establish its premise on that control.

## 2. Stronger one-sided phase order for this word

For Boolean indicators ordered by 0<1, assume P4<=P0 on every positive height. Forward equal-letter transport across phases 4,0 and then 5,1 gives P5<=P1 and P6<=P2. Backward transport at the two T phases 3,6 gives P3<=P6. Backward transport across 2,5 then 1,4 gives P2<=P5<=P1<=P4 (specifically P2<=P5 and P1<=P4). Combining yields the exact total chain

    P3 <= P6 <= P2 <= P5 <= P1 <= P4 <= P0.

At phase3 the next letter is T, successor phase4. For even z, P3(z)=P4(z/2)>=P3(z/2). For odd z, write y=(3z+1)/2, so P3(z)=P4(y). If y is even, P4(y)>=P3(y)=P4(y/2)>=P3(y/2). If y is odd, P4(y)=P5((y+1)/2)>=P3((y+1)/2). Thus in both odd cases P3(z)>=P3(ceil(y/2)); ceil((3z+1)/4)<z for odd z>=5. The finite bases z=1,2,3 at phase3 are literally captured. Strong induction gives P3=1, then the total chain and phase alignment give global capture.

**Theorem.** Global capture iff P4(z)<=P0(z) for every z>=1. Equivalently, any noncapture forces at least one height captured from phase4 but not phase0. This is logically weaker than the equality premise. The opposite order alone is not shown sufficient here. In particular do not replace a directed inequality by symmetric phase jumps. The verifier checks the directed closure and the four residue classes of the two-step contraction, plus literal bases. This reduction uses the specific locations of the two T letters and the fact that the successor of the minimum-label T phase is a U phase above it in the derived order.

A genuine limitation: no literal uniform whole-affine physical comparison between two different phases at the *same* height av+b can prove such equality on an infinite free ray by fixed meeting clocks k,l. Equality of affine slopes gives 3^g/2^k=3^h/2^l and unique factorization implies k=l and g=h, whereas phase alignment requires k-l=i-j mod7. The same obstruction applies to composition of such physical paths using the same free parameter. This does not prohibit pointwise unequal-clock joins, unbounded refinement, conditional phase moves, or direct basin-label reasoning. Do not mistake the new phase condition for an easier symbolic merger target.
