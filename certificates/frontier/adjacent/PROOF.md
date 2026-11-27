# Ternary induction from the adjacent discrepancy

Let P denote the phase-indexed capture label and J(v) the XOR of the phase-one labels at normalized heights 18v+2 and 18v+3. The free integer v is nonnegative.

## 2. Complete direct digit machine from J alone

At slope cap 4,000,000, enumerate every conditional J edge a=2^(7i)*3^j<=cap, 0<=b<a, in the canonical phase-2 graph. First a fixed ternary level e=5 gave 724 of 729 children connecting to a state of level 5. Five offsets 20,165,376,377,686 remained missing (`digit_adj.cpp`, `digit_counts.jsonl`). Instead choose the minimum canonical node (ordered by exponent then offset) in each graph component, starting with f(9w+b), b=0,...,8, and recursively add their digit children. `minimax_machine.cpp` orders edge groups by increasing a and constructs a union forest. By the standard threshold property of Kruskal's algorithm, a selected path minimizes its largest conditional-argument slope among paths in the enumerated graph for those endpoints; this does not optimize total weight or all possible representations. In the chosen cap the graph search enumerated 14,231,484 input edges and closed the machine at 63 states, exponents 2..5. The path certificate is `minimax_machine.json`. Graph generation is not a trust requirement: `verify_machine.py` checks every selected affine path with independent signed physical formulas.

The 63 states are h_q(w)=f(3^e_q*w+b_q). Entry f(9w+b) is exactly its designated state for each b=0..8 (no conditional edge at entry). Every transition is an unconditional identity of labels and errors:

    h_q(3w+d) = h_delta(q,d)(w) XOR XOR_{(a,b) in S[q,d]} J(a*w+b).

Here S is the parity-cancelled multiset of path arguments. There are 189 complete transitions, 9360 selected edge occurrences, 4465 distinct edges, maximum path length 247, maximum argument slope A=3981312. All 63 base heights b_q+1 have a verified actual capture path of <=66 ticks. Four corruptions are rejected. Thus if J is identically zero, ordinary ternary digit induction proves every phase-2 label 1. Any other phase reaches phase 2 after finitely many ticks. Conversely global capture implies J=0. This direct independent implication replaces the need to invoke the PR30 chain or the earlier root e digit machine; it is not a proof that J vanishes.

For a given phase-2 z the exact support can be computed by reading digits of (z-1)//9. Each argument is < A*(floor((z-1)/27)+1). Hence if J(j)=0 for 0<=j<N, all z with A*(floor((z-1)/27)+1)<=N are captured. Use the exact support rather than this coarse bound in applications.

