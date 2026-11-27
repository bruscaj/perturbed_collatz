# Signed phase-error balance and restricted one-sided adjacent transfer

## 1. Coordinates and sound certificate algebra

Let H=(0,0,0,1,0,0,1), d_p=H[p+1]-H[p], phase modulo 7, z=n+1-H[p]>=1, x=z-1>=0. The physical step is the ordinary shortcut Collatz map on n followed by d_p. In x coordinates, on x=2y+r, the shrink is y iff r=H[p], and the grow is 3y+1+r otherwise. P_p(z) is the actual capture indicator of the known phased cycle (1,1,1,1,2,3,2). Labels are invariant along physical edges.

Write L(a,b,p;w)=P_p(aw+b+1), a>0, 0<=b<a, w>=0. If a is even its entire ray has one physical branch. Apply exactly v2(a) ticks to remove all dyadic factors from the slope, giving a canonical affine triple with odd slope; every tick is physical and safe. Equal resulting triples certify equal actual labels. This does NOT assert that two unequal triples cannot have the same actual label.

For fixed i,j, draw an edge from the canonical triple of (a,b,i) to that of (a,b,j); the signed label drop on it is e_ij(aw+b)=P_i(aw+b+1)-P_j(aw+b+1). The edges are comparison identities, not physical phase jumps. Along a directed path the signed drops telescope. If the starting label is 1 and the terminal label 0, at least one path argument has e_ij=+1; a path in the opposite direction controls the opposite endpoint discrepancy using the SAME +1 sign. Reverse all edges to use the -1 sign instead. All arguments are injective affine functions of w. Search is not trusted: the consumer independently replays every edge in original signed n coordinates and checks path chaining, congruences, positivity and endpoints.

## 2. All 21 signed balance identities

For each i<j there is a verified path from (1,0,j) to (1,0,i), all comparison arguments aw+b with a>=2. Thus, for x>=0,

    e_ij(x) + sum_edges e_ij(a*x+b) = 0.

For e=P4-P0 the explicit seven-term balance is

    e(x)+e(2*x+1)+e(8*x+4)+e(12*x+7)+e(16*x+8)
        +e(32*x+16)+e(64*x+36)=0.

Every nonzero e_ij(x) at x>=1 implies an opposite sign at a strictly larger argument. All seven phase labels at x=0 are literally captured; clocks (0,0,0,0,8,7,6). Hence a nonzero sign forces both signs infinitely often; eventual one-sided phase order is equivalent to identically zero phase discrepancy. With N_+ and N_- counting signs for 0<=x<X, N_-(X)<=k N_+(C X) and symmetrically, for the selected path length k and max slope C (b<a). Across all pairs 294 edges, max slope 512. No minimality claim.

Separate undirected affine paths, for each pair, connect (1,0,0) to (1,0,4); 99 edges, slope <=64, longest path 9. Their signed identity transfers the support of the phase-0/4 defect into a union of affine pullbacks of the chosen pair's two sign supports. Combining with the balance identities controls it by just one sign.


## 3. Direct one-sign transfer to adjacent J and the restricted ternary class

Let J(v)=P1(18v+2) XOR P1(18v+3). One physical tick gives the canonical pair (27,2,2) and (9,1,2) in x coordinates. The exact adapter follows because H[1]=0, x=18v+1 grows to 27v+2 while x=18v+2 shrinks to 9v+1.

For each of the 21 pairs i<j, the consumer finds directed paths BOTH ways between these canonical triples using only e_ij comparison edges. 329 selected directed edges in total, maximum slope 512. The same signed support controls J regardless of its endpoint orientation. In particular, there is no reliance on the phase quotient reduction or the four-state parent-error machine for this implication.

More importantly restrict all arguments of the comparison edges to x=3t+2, i=2,j=6. Two paths of 14 and 21 edges are verified, slope cap 8192, every a divisible by 3 and b congruent 2 modulo 3. Consequently define

    A(t) = 1[P2(3t+3)>P6(3t+3)].

For J(v)=1, at least one of the 35 affine arguments a*v+b has the positive phase error, so

    J(v) <= sum_edges A((a*v+b-2)/3).

The bound is deterministic and pointwise; duplicate terms are harmless. Thus if N_A(X)=sum_{0<=t<X} A(t), then N_J(X)<=35 N_A(8192 X) for integer X>=1, and finite supports transfer to finite supports. Reverse all paths for the opposite sign. This ternary restriction uses a genuine grow image (both preceding phase letters U); it is not just padding a full comparison with a common all-shrink prefix.
