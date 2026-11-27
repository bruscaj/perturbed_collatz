# Seven-step research update

Jake S. Brusca · 26 November 2026

A B1 launch starts at physical height `6t−1` in phase one, with integer `t ≥ 1`. Safe zero continues evolving. Capture means reaching the distinguished cycle at its correct phase. The manuscript gives the five guards and the induction on the original B1 parameter. [Manuscript section](../../tex/frontier.tex)

| Question | Evidence to inspect | Scope |
| --- | --- | --- |
| Why does B1 alone suffice? | [189-ray entry checker](b1_entry/verify_b1_entry.py), [Lean equivalence and final obligation](../../lean/frontier/Collatz/SevenStepCertificate/B1FinalObligation.lean) | The all-phase arithmetic cover takes at most 30 updates. Lean uses 27 phase-one ancestor rays and forward alignment. |
| Which parameters remain? | [Guard definitions and whole-ray witness](../../lean/frontier/Collatz/SevenStepCertificate/B1ComplementWitness.lean), [unbounded repayment](b1_repayment/verify.py) | Every positive parameter outside the five guards still needs capture in this formulation. Individual parameters there can have other certificates. |
| How do the ranks and exits fit? | [Independent common-Q and W replay](common_rank/verify_certificates.py), [A3 terminal theorem](../../lean/frontier/A3SharedComponent.lean), [legal repayment](../../lean/frontier/RepaymentPhysical.lean), [B1 selector](selector/b1_selector.py) | Q and W have different sections. For B1 induction a partner must have a smaller positive parameter. The composed selector can return an unhandled result. |
| What follows for most neighboring starts? | [Renewal proof](paired_switching/PROOF.md), [pair-chain and growing-block proofs](paired_recurrence/PROOF.md), [exact prefix selector](paired_recurrence/prefix_selector.py) | The truncated grammar and full density-one merger theorem have different acceptance sets. The power bound counts unresolved candidates for a specific selector. The eventual basin label is still undetermined. |
| Why allow two clocks? | [Excess-growth obstruction and two-clock proofs](basin_frontier/PROOF.md), [exact selector](basin_frontier/two_clock.py) | Infinitely many captured parameters defeat the equal-clock, equal-grow-count format. Exhaustiveness of the finite search requires both clock budgets and the partner-stride condition. The analytic gap estimate in this supplement assumes the stated inverse floor. |
| Where are ancestors found? | [Interval theorem and basin-boundary criterion](intervals/PROOF.md), [exact connector and rotation nets](intervals/verify.py), [precision-14 potential checker](potential/root_inverse_exponent.py) | Every target has a B1 ancestor in every sufficiently large proportional band. Local abundance at exponent 17/20 additionally uses the positive potential. To infer global capture from homogeneous bands one needs a fixed positive relative width and an unbounded sequence. |
| Can one use an affine root instead? | [Phase-two proof](affine_root/PROOF.md), [block checker and negative controls](affine_root/verify.py) | The equality of capture labels at `n` and `27n−22` for all positive `n` remains a hypothesis. The odd-pair reduction is a written theorem with exact arithmetic checks. |

The later regular-domain proof gives explicit entry into the set of parameters with even binary digit sum. A separate phase comparison shows that eventual absence of either sign of the capture-label difference for *one full phase pair* would suffice. The restricted ternary comparison controls adjacent discrepancies through 35 affine arguments. [Regular domains](regular_domain/PROOF.md) · [Phase quotients](phase_quotient/PROOF.md) · [Signed balance](phase_balance/PROOF.md)

## Source selection and review

The initial public snapshot is commit `8ed6c128c48fa17375aab7ea4adf828002c7edd6`. The sweep closes at the pinned #32 integration snapshot. The research pins below identify the source versions used for this update. The code and proofs linked above can be read and checked from this repository alone.

| Research source | Commit | Disposition |
| --- | --- | --- |
| Integrated certification | `cd9dc0b4addc68787fcdf4bdca44b158d4bf3a09` | Physical classifiers, compatible-Q cover, and positive-scale inverse potential. The independent formal classifier is included through its later B1 continuation. |
| B1 continuation, #19 | `4440ea81d21bb423a607d4f6b0050b5892f9013e` | Entry, strict internal progress, refined three-family and single-family equivalences, repayment and complement witness. |
| Passage audit, #20 | `ad3474c2a249152936d9ba2238b5be80cf60e642` | Corrected the three-family table caption. Its rank change is the penultimate column. Later pair and interval results have separate evidence. |
| Residual termination, #21 | `6742fbeea79e7f2990a80ce90b2bb084d50ece4f` | Four Lean modules, including the standalone five-guard arithmetic audit, local counter theorem and A3 exit. |
| Cover composition, #22 | `d90c89db6e96c0f01df3e5e4eaeb22c5f3a87f20` | Six Lean modules and the executable composed selector. The seven frozen Lean files in the selector inputs are reference data and are counted only once in the mathematical module inventory. |
| Recurrent packets, #23 | `a7927d1e8dd108ed9c4b99973b970d4658ee8b42` | Written packet and renewal arguments with exact replay. |
| Affine recurrence, #24 | `659f774ea63b38c1aadac4ea08090fb70ab3b5a4` | Written pair and block results, recurrence replay and prefix query. The optional numerical block-screen experiment is outside the release. |
| Basin frontier, #25 | `15afed0fc7540ecfa3334a89a9fb8fa8922bb24c` | Exact selector, obstructions, and the written conditional basin analysis. |
| Interval steering, #26 | `5f74b94d154a8d7e3fe581b2f956ce07d19fb19c` | Written inverse and boundary results, including a two-basin negative control for inference from inverse abundance. |
| Affine-root thread, #27 | `324306ed3bdc60f0e3b24cbd92f40942f691a986` | Adopted stage 1, whose verifier and full proof are supplied. At the later cutoff `5df2e50e99c10f24a056b41cba9917c641b7f493`, the branch contains the original archives and additional parent-tree, shadow, adjacency and phase-order work. The stage-one sources match the earlier pin. The public single-root theorem uses stage one. Also included the later [63-state adjacent-error digit proof](adjacent/PROOF.md) and its 189-transition certificate. The separate parent-tree and quantitative error-tail results are deferred. |
| Configuration and root-error continuations, #28 | `b5ef15f72d9caf930103931bc0d151ab32e9a693` | Replayed seven all-depth rational-shadow constructions under their pinned digit-error identities and captured-base premises. The broader historical guard percentages and finite searches are outside the public theorem inventory. [Proof and hypotheses](error_shadows/PROOF.md) |
| Regular-domain continuation, #29 | `e42d372290659245057cb1a13fa7a8192bf256f3` | Adopted the positive-upper-density regular-domain sufficiency proof and the complete 30-tick even-digit-sum entry cover. The proof automata, finite stack barrier and group experiments are separate. |
| Phase quotients and transfer obstructions, #30 | `64efe6243d49d13748fa11430e74f4f0e2dff238` | Adopted the phase-quotient criterion with the extracted source and exact reference receipt. Conditional transport of a label requires the equality premise. The larger digit-bank and cut-flow experiments are outside this release. |
| Signed phase errors, #31 | `c98306f7741cbdcf240faf3fb6272fbe476a77e9` | Replayed all 21 balance identities and the directional transfer to the restricted ternary support. Together with the stage-eight digit machine, absence of every restricted positive error is equivalent to global capture. Its actual sign counts remain open. |
| Integrated research and readiness, #32 | `6452c02274fca65a3329cf66bfbcb6f52fa5a462` | Compared the integrated manuscript payload to its reviewed source and the seven-step formal files to #19. The release-affecting mathematical-table edit is the caption repair already included above. |

The critic review tested the A3 terminal congruence against a near miss, replayed both printed two-clock identities on whole signed affine rays, and checked rejection of a nonpositive potential scale. The review distinguished acceptance by a guard from capture, and identified the different premises of the single-ancestor theorem and the local power-law count. It was AI-assisted technical review.

## Reproduction

From the release root, `python3 scripts/verify.py --mode all` runs the published certificate replays, builds the pinned Lean projects from source, checks their theorem inventory and axiom dependencies, and compiles the paper. Each supplemental proof identifies which conclusions use an infinite argument. Comparing a finite receipt alone does not prove those conclusions.

The precision-14 potential uses 33,480,783 inequalities. All-mode CI regenerates and checks this potential. Running just that stage requires about 268 MB for the vector, additional working memory, and a little-endian system. From this directory:

```sh
c++ -O3 -std=c++17 potential/root_inverse_potential.cpp -o /tmp/perturbed-potential
/tmp/perturbed-potential 14 554549 1410889 800 /tmp/perturbed-potential.bin
python3 -B potential/root_inverse_exponent.py --pruned --exponent 17/20 --file /tmp/perturbed-potential.bin
```
