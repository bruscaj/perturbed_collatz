# Odd-pair connectivity and a single affine residual obligation

The distinguished cycle and the physical update are fixed throughout.

## 1. Model and exact statement

For phase `p`, let the physical update be `n -> T(n)+d[p]`, followed by phase `p+1 mod 7`, where `T` is the shortcut Collatz map and `d=(0,0,1,-1,0,1,-1)`. Safe zero continues evolving. Put `h=(0,0,0,1,0,0,1)` and `z=n+1-h[p]`. The normalized positive map uses `UUUTUUT`:

- `U(z)=3z/2` if even, `(z+1)/2` if odd;
- `T(z)=z/2` if even, `(3z+1)/2` if odd.

Let `P(z)` denote capture of normalized positive `z` at phase 2 by the distinguished physical cycle `(0,0,0,1,1,2,2)`. Capture status is unchanged by a finite forward path. Write `x ~ y` for `P(x) iff P(y)` at phase 2. This equivalence relation is weaker than simultaneous coalescence, but actual common-future identities imply it.

**Theorem.** Global positive-state capture is equivalent to the single proposition

```
forall n >= 1, P(n) iff P(27*n-22).
```

Equivalently, global capture follows if all adjacent odd pairs `(128v+17,128v+19)` at phase 2 have equal capture status, for every integer `v>=0`. Synchronous pair coalescence is sufficient, but is not required. Both sides of the displayed equivalence have the same phase. This is not a theorem for ordinary Collatz.

### Proof A: seed the odd-pair connectivity relation

The independent signed-physical checker verifies 19 full odd residue classes `r mod 128` for which `(128v+r,128v+r+2)` merge after seven updates. The hypothesized class is `r=17`; its two seven-tick images are `27v+5` and `v+1`. Hence its assumption is exactly the affine obligation above with `n=v+1`.

The 11 rows of `LINKS` give further whole-ray implications in their listed order. For each row `(r,A,B,E,L,K)`, the verifier proves that the two source launches meet the corresponding alternate launches `Av+B`, `Av+E` after clocks `L,K`. Both clocks are multiples of seven. The alternate pair is an odd chain with `128 | A`; every edge is a previously proved or assumed residue class. Symmetry and transitivity of `~` prove the desired link. There is no recursive dependence on a not-yet-established link. The result is exactly 31 universally valid odd-pair residue classes, conditional on the single root.

For example the class `r=9` transfers after 7/14 ticks to the pair `(16384v+1297,16384v+1299)`. Its lower endpoint is 17 modulo 128. This use of the hypothesis can involve a much larger parameter, so it must not be mistaken for descent in the root parameter.

### Proof B: complete block induction rather than prove all remaining links

Cut the ordered odd positive integers at each missing residue-class edge. There are 33 periodic block types (plus the initial singleton `{1}`). Their offsets are the consecutive ranges `[r+2,s]` of odd numbers, where `r,s` are consecutive missing edge residues, using `s=first+128` across the seam. Thus the blocks translated by `128v` partition every odd integer >=3, and every member of any block has the same capture status under the hypothesis. Rank a block by its least member.

For every block and both parameter parities, the checker constructs one of three forms of descent:

1. 37 entire block-parity types have a direct or unequal-clock common-future certificate to a smaller odd positive seed using at most one physical lap on the representative.
2. 19 remaining block-parity types are split by `v mod 256` (128 subrays each). On every one of these 2,432 infinite affine rays the checker constructs an odd representative and a smaller odd alternate meeting after at most two physical laps on the representative. The exact rank comparison is against the original block minimum, not against the most recent state. All 2,432 comparisons hold even at the affine parameter zero in the observed verification run.
3. The 10 exceptional entire block-parity types use the explicit `BRIDGES` bank. Each bridge is a chain of common-future identities and same-block equivalences. Intermediate states can grow. The final odd endpoint is strictly below the original block minimum for every parameter.

The program regenerates the witnesses from the normalized recurrence, then separately checks them on whole affine rays using the signed physical recurrence. Equality of coefficients and constant terms proves the identity for every integer parameter; divisibility of each slope by two guarantees the full parity guard. The checker rejects a missing block ray, bad clock, incorrect endpoint, or nondecreasing original rank. It does not infer whole-ray validity from samples.

A useful example is the formerly difficult odd-parameter block `[128v+125,128v+127]`, `v=2w+1`. The representative `256w+255` maps to `162w+162` in seven ticks. The following are two exact common-future bridge steps:

```
run14(98304w+97043) = 162w+162
run14(98304w+97041) = 4374w+4320
run14(32768w+32353) = 4374w+4320
run14(32768w+32355) = 162w+161
```

The first alternate pair has lower endpoint `17 mod 128` and uses the one residual hypothesis. The second has lower endpoint `97 mod 128`, already derived from that hypothesis in `LINKS`. The final odd seed `162w+161` is strictly below the *original block minimum* `256w+253`. This entire infinite block-parity family is eliminated by one finite compositional certificate, not by increasing a bounded census.

The initial odd seed 1 is already on the target cycle. By strong induction on the least member of each block, all odd positive phase-2 seeds capture. The `r=19` seven-tick identity gives an odd positive antecedent `128z-109` for **every** positive phase-2 seed `z` (substitute `v=z-1`). Thus all positive phase-2 states capture. From every other phase a positive state reaches phase 2 within at most six updates. This proves the forward implication. The reverse implication of the theorem is immediate because global capture makes every instance of `P` true.

## 2. Independent reset-subsystem reduction

The complete seven-tick affine classifier of `(x,x+2)` at phase 2 yields exactly four infinite same-type returns, all preserving order:

| source | new lower coordinate |
|---|---|
| `128v+36` | `243v+72` |
| `128v+56` | `81v+36` |
| `128v+98` | `81v+63` |
| `128v+111` | `81v+72` |

There are 21 whole merger rows and one isolated same-type return at `x=7`. All other whole-ray endpoints are checked for possible isolated equality or difference +/-2 by solving the exact affine equation, not by sampling. The earlier PR21 two-loop picture was not an exhaustive classifier of this pair type.

Every one of the four infinite returns produces a multiple of nine. Their expanding factor is at most 2 and all three contracting factors at most 2/3. Also

```
run14(16384v+1569) = 729v+72
run14(16384v+1571) = 729v+74.
```

The alternative source has lower residue 33 modulo 128, outside the four loops. Whenever F follows any loop, its input is divisible by 9 and its output is 72 modulo 729, so this bridge applies. If all non-loop D2 pairs synchronize, all D2 pairs synchronize by strong induction on x: contraction decreases x; an initial F followed by a non-loop goes to a proved case; FF or FKF goes to the alternative non-loop ancestor; FKK decreases the original x by at least the factor bound 8/9. The finite isolated return is included in the non-loop hypothesis (or can be handled by direct capture). The theorem does not prove every non-loop pair synchronizes. It removes arbitrary switching of these four loops as an independent conditional obstacle. The single-root block proof above is a different, stronger interface and does not need this conditional result.

## 3. First exact reductions inside the single remaining root

Use `R(n) := P(n) iff P(27n-22)` at phase 2. On `n=128v+120`, the synchronized seven-step images are

```
27v+26, 27*(27v+26)-22.
```

Hence `R(n)` is equivalent to `R(27v+26)` with strictly smaller positive parameter. At 14 updates the exact whole-ray classifier gives 206 merger rays and 38 strictly smaller self-return rays (including reversed orientation). Combining the one-lap guard gives 371 distinct residue classes modulo 16384 in the accepted reduction union, leaving 16,013 classes outside that union. The code reconstructs each formula and inequality. By strong induction on n, it suffices to establish `R(n)` on the complement of these guards. This is scoped to this new root-specific screen, not a net-coverage comparison against the previous B1 bank, and not capture density. Recursive reduction is not unconditional capture.

The next substantive attack is to exploit the exact affine shape `R(n)`, especially whether variable-length paired rules can transfer it to smaller `R(m)` on whole parity/valuation families. Do not assume an arbitrary invocation of the root relation in the block proof uses a smaller parameter: the large alternate slopes in `LINKS` and `BRIDGES` demonstrate otherwise. A second direction is to extract exact root-parameter dependencies of block certificates and search for a common well-founded rank on those dependencies. Any refinement must preserve the original source/alternate phases and prove its rank across all switches.

## 4. Reproduction and limitations

```
python3 verify.py > report.json
python3 -O verify.py > report.optimized.json
cmp report.json report.optimized.json
```

The checked receipt is `verification.json`. Both runs passed and were byte-identical. This is a written mathematical proof supported by exhaustive whole-affine arithmetic checking and explicit negative controls. It is not a Lean kernel proof, a replay of the full historical suite, a literature novelty determination, or the discharge of the remaining root proposition. The one-root theorem is not claimed to improve the intrinsic difficulty over the B1-only capture equivalence in PR19; its value is the new pair relation and block induction that avoids controlling every residual trajectory individually. The two-ray multi-hop bridge and the complete partition are new working results relative to the inspected PR21/22 descriptions, not a claim of priority over all previous work.
