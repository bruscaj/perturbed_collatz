# Frozen abstract prefix/depth specification

Source/model reviewer: separate AI context, 2026-11-27. This is a supporting
integer theorem, not a formalization of M4, R8, R9 or O3′. Intended toolchain:
official Lean 4.35.0, Std only. The parent implementation must record its actual
build and checker commands; writing this specification records no successful
build or independent kernel replay.

`Definitions.lean` and `ExpectedTypes.lean` contain no theorem holes or custom
axioms. `Challenge.lean` deliberately contains five named specification holes;
it is a separate challenge input and MUST NOT be imported by accepted proofs.
The solution may import the first two files. Freeze their exact bytes and
challenge bytes before implementation, using `freeze.json`. A changed definition
or type invalidates this freeze and requires another statement review.

## Meaning and expected theorem names

| Declaration | Exact scope |
| --- | --- |
| `floorDepthEquivalence` | Every integer floor profile L with L(0)=0 and every cumulative profile K: floor-capped positive increments ending at L(n) are equivalent to zero-endpoint nonnegative depth J=L−K satisfying J(t+1)≤J(t)+L(t+1)−L(t)−1. |
| `depthInvolution` | Reflection K↦L−K is an involution on all functions Nat→Int. |
| `closingFloorEquivalence` | For n>0 and unit-or-larger floor increments, replacing K(n) by K(n)−1 takes closing endpoint L(n)+1 with interior caps to the floor model, in both directions. |
| `floorRaiseSoundness` | For n>0, raising a floor-admissible endpoint by one gives a closing-admissible profile, without assuming unit increments for L. |
| `endpointInverses` | Raising and lowering the same endpoint are inverse operations on all profiles. |

Profiles remain arbitrary after n; both transports alter only index n. Caps
are required at t≤n in the floor model and t<n in the closing model. Positive
integer increments are encoded exactly as K(t)+1≤K(t+1), not nondecrease.
Since all quantities are Int, subtraction is ordinary signed subtraction.

The floor/depth theorem includes n=0. Its sole L(0)=0 hypothesis is necessary
to translate K(0)=0 to J(0)=0. The closing transport explicitly excludes n=0,
where start and end conflict. Its unit-increment hypothesis is material:
with n=1, L(0)=L(1)=0, K(0)=0,K(1)=1, the closing prefix is admissible but
lowering its endpoint creates a zero increment and fails the floor predicate.

This specification is source-matched only as abstract arithmetic. Instantiating
L(t)=floor(t log₂3), proving its increments, infinite rungs, the exact rational
word/reward identity, final-letter weight, pressure/density limits and the
external problem statements are separate unproved obligations. The literal
closing model has depth −1 at n; only the transported floor model has depth 0.
No accepted theorem may silently rename these models.
