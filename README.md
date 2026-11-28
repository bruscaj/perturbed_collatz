# Periodic forcing of the shortcut Collatz map

> **Personal project · work in progress.** I am not an expert in this field. I am exploring these ideas for fun and to learn, and this is still a work in progress. Corrections, counterexamples, and suggestions are welcome.

**Public research draft, 26 November 2026.** Read [the paper (PDF)](paper.pdf), [its TeX source](paper.tex), or the compact [claim-to-evidence map](claims.json). **Author: Jake S. Brusca** ([bruscaj](https://github.com/bruscaj)). OpenAI’s ChatGPT assisted with exploring proof ideas, writing and revising the manuscript, preparing code and Lean proofs, and reviewing this release. Reuse terms remain pending.

This repository studies the shortcut Collatz map with fixed periodic integer impulses and an explicit forcing phase. The dynamics continue through zero. It contains a self-contained manuscript, the selected Lean proof projects, and exact arithmetic certificates with their reproduction programs.

## The current seven-step result

Every safe phased state is captured **if and only if** each positive B1 launch outside five explicit guards is captured. Here B1 means starting at physical height `6t−1` in phase one. The Lean proof verifies the equivalence, including a whole progression outside the guards. Proving capture on that complement remains open. [The exact Lean theorem](lean/frontier/Collatz/SevenStepCertificate/B1FinalObligation.lean) · [Manuscript section](tex/frontier.tex)

Almost every B1 parameter in each fixed progression merges with its smaller neighbor. The parameters for which the argument gives no merger still matter for universal capture. A separate theorem puts an ancestor of each target inside every sufficiently large interval of fixed relative width. The release also includes regular-domain entry, signed phase comparisons, an alternative phase-two criterion, complete two-clock examples, and the independently replayable proof supplements. [Research update and evidence](certificates/frontier/README.md)

## Results and limits

The [external-problem research register](papers/external_problems/README.md)
now includes candidate answers to Polson–Sokolov **M4, R8, R9 and O3′**.
They remain draft candidates, with no complete headline Lean proofs or human
expert refereeing. Exact finite source-model checks and five abstract integer
supporting lemmas are included. M4's unrestricted and rung formulations are
tracked separately; none is advertised here as a solved open problem.
The [depth-one Syracuse proof draft](papers/finite_information_lyapunov/README.md)
includes its density argument, exact infimum formula and nonattainment argument,
with its incomplete formal coverage stated explicitly.
The [near-extremal entropy draft](papers/arithmetic_bridge_pressure/README.md)
gives the proposed rung pressure and entropy argument behind R9; it remains
unformalized and covers only part of M4 and R8.

| Result | Evidence here | What remains outside the claim |
| --- | --- | --- |
| Classification of admissible conservative impulse words and binary-height coordinates | Complete analytical proof and direct Lean support for the conservative classification, height/safety, and conjugacy | Does not prove capture for every admissible word; primitive-period comparisons remain written arguments |
| Sharp base-launch peak and period bounds for 2, 4, 6, and 8 impulses | Exhaustive core censuses, exact ordinary-tail exhaustion, proof covering all gaps | Entry into the base from arbitrary seeds is not proved |
| A logarithmic-period word synchronizes any fixed finite interval from every phase | Complete analytical proof, including drift and all-rotation argument | The word can depend on the interval; there is no universal word conclusion |
| Backward-orbit growth in every progression for forcing `(1,0,-1)`, with `0.535 < δ < 0.536` | Exact 24-step branch certificate and full counting/steering proof | Inverse abundance does not prove universal forward capture |
| Global capture for forcing `(0,0,1,-1,0,1,-1)` is equivalent to capture of four explicit infinite families | Whole-domain exact arithmetic reconstruction, independent implementation, complete induction proof | All four remaining universal capture obligations are open |
| A second section reduces the same global-capture question to three explicit infinite families | Complete 43-domain partition and independent physical replay; the positive-seed equivalence is also proved in Lean | All three universal obligations remain open; the two sections use separate ranks |
| Limitations of phase-affine direct first-return ranks | Exact finite slope constraints and proofs for each section | Does not exclude residue-dependent ranks, later meetings, or other methods |
| Both known three-step integer basins occur in every progression; a binary tile is an exact copy of the dynamics | Inverse theorem, exact zoom identities, supporting Lean declarations | No natural basin density or global integer capture follows |
| Five attracting cycles, a classified real segment, and a phase-dependent complex launch for a specified cosine continuation | Exact rational capture disks, complete interval covers, and complex-ball trajectories | Numerical basin pixels are illustrations; neither the attractor list nor the global basin boundary is claimed exhaustive |

**This is not a proof of the ordinary Collatz conjecture.** No implication transferring the forced-map conclusions to that conjecture is established here. The complete paper is also **not fully formalized in Lean**.

## Relation to earlier work

The paper now includes **51 cited references** and a detailed related-work discussion, with attribution beside the relevant results. Classical parity coding, the translated companion map `U = P T P⁻¹`, arithmetic-progression sufficiency, inverse counting, synchronization, and continuous Collatz extensions are distinguished from the specific forced statements proved here. The general integer-cycle attraction result is explicitly presented as an application of an earlier generalized-map theorem after a checked coordinate and derivative comparison.

Every entry in [claims.json](claims.json) includes its literature relationship and the limit of any proposed transfer. Almost-all results, single-state control, and results for a different analytic interpolation do not remove the paper's open hypotheses. Source versions and limited-access comparisons are identified in the manuscript; precise priority for the forced results remains under review. The bibliography is selective and makes no claim to exhaust the Collatz literature.

## Lean coverage

The four legacy Lean projects contain 51 mathematical modules. Their clean builds compare 825 named public theorem declarations and the module-wide axiom audits against the committed inventory. The frontier project includes the single-B1 equivalence, guarded exits, repayment, and a counterexample to coverage by the five guards. A separate Lean 4.35.0 project proves five abstract integer prefix/depth supporting statements; it proves none of the external headline claims. [Lean coverage](lean/README.md) · [Exact theorem inventory](lean/inventory.json)

The pinned versions are Lean **4.24.0** for `frontier`, `inverse`, and `sprint`, and **4.19.0** for `perturbed`. No mathlib dependency is needed. The audited theorem dependencies use only `propext`, `Quot.sound`, and `Classical.choice`; no `sorryAx` or custom axiom occurs. The four legacy projects have not had independent kernel replay. The five newer abstract prefix/depth supporting statements passed sandboxed proof-closure replay, frozen-statement comparison and independent checkers; [exact scoped receipts](verification/external_prefix/README.md) state the checked source commit and limitations.

The new signed physical modules prove the conservative classification, height/safety identities, arithmetic cycle gain, and conditional three-family capture implication. [ReleaseBridge.lean](lean/inverse/Collatz/ReleaseBridge.lean) proves the matching equivalence for every positive physical seed at every phase. **Its three universal family hypotheses remain open.** The original four-family theorem, complete inverse-growth/progression theorem, synchronization, support censuses, and analytic geometry are not thereby formalized.

Read the scope table before reusing an older theorem: one older module makes zero absorbing; another uses a different seven-step word; an escaping-basin theorem assumes an escaping target; and progression steering retains an additional divisibility guard. The geometry's arithmetic multiplier inequality has Lean support, but its smooth derivatives, capture disks, real interval proof, and complex traces remain exact arithmetic checks with written analytic proofs.

## Reproduce

Run commands from this repository's root. Requirements are Python 3.10 or later, Node.js 18 or later for the rational-shadow checker, a C++17 compiler for the exhaustive impulse censuses, Lean via elan with both pinned versions for formal checks, and a working TeX installation with `latexmk`, Latin Modern, AMS, geometry, microtype, graphicx, placeins, hyperref, cleveref, booktabs, and enumitem for the paper. Mathematical verification uses the Python standard library and does not download mathematical data. Building the paper uses the committed figure PDFs.

```sh
# Exact small and worked-example checks, stored-shard validation,
# both seven-step reconstructions, rational geometry, and hostile inputs.
# This does NOT rerun every large census.
python3 scripts/verify.py --mode quick

# Also regenerate all 1,271,626 inverse formulas, the complete six-impulse
# census, and two complete eight-impulse implementations.
python3 scripts/verify.py --mode full

# Also build/audit every Lean project and compile the manuscript from scratch.
python3 scripts/verify.py --mode all --report /tmp/collatz-verification.json

# Individual components:
python3 lean/verify.py --check-inventory lean/inventory.json
python3 scripts/build_paper.py

# Optional: regenerate all eight figures (separate plotting dependencies).
python3 -m pip install -r requirements-figures.txt
python3 scripts/render_figures.py
```

Install the toolchains, if needed, with `elan toolchain install leanprover/lean4:v4.19.0` and `elan toolchain install leanprover/lean4:v4.24.0`. For installations without elan, the verification runner accepts `--toolchain-419 /path/to/lean-4.19.0` and `--toolchain-424 /path/to/lean-4.24.0`.

Full reproduction checks **2,416,542** rooted six-impulse words and **2,383,451,629** rooted eight-impulse words. These are rooted representations, not distinct cyclic words. Exact acceleration makes the scans practical on a conventional machine, but runtime varies. The runner uses at most four workers; `--workers 1` reduces concurrency. A failed tool, unresolved trajectory, missing partition, overflow, or mismatched certificate fails the run. Assertion-based checks refuse Python optimization mode.

The eight-impulse quick checker validates every stored local witness and partition, including fields an earlier checker failed to validate. **Attaining witnesses and histogram consistency alone do not establish the universal upper bounds**; use full reproduction and the manuscript's exhaustive reduction. The independent arithmetic checkers are not described as Lean certificates.

## Figures and their interpretation

The paper contains eight reproducible figures: phase-indexed integer cycles, the eight affine return branches, a binary basin atlas and exact zoom, a finite-ensemble synchronization example, complex basin views, the real separator, three launch-phase sheets, and the seven-step merger.

Integer samples are labeled by exact finite replay. Complex raster colors are floating-point observations with an explicit magnitude guard and iteration limit; guard hits and budget exhaustion stay separately unresolved. The five attractors and the highlighted phase-dependent launch have independent rational certificates. The figure generator is not used to accept a mathematical proof.

`figures/figure_inputs.json` records domains, budgets, exact input summaries, numerical class counts, and raster digests. The optional plotting versions are pinned in `requirements-figures.txt` and require Python 3.11 or later (tested with Python 3.12.14). Repeated rendering in that environment produced identical bytes for all eight PDFs and the input JSON. Different plotting libraries, fonts, or platform math libraries may produce different bytes or boundary pixels without changing the exact certificates.

## Layout and integrity

`paper.tex` and `tex/` form the complete manuscript. `paper.pdf` is compiled from those sources. `lean/` contains pinned projects and the theorem inventory. `certificates/` contains exact data, checkers, and independent replays. `scripts/` supplies the unified entry points. `MANIFEST.json` lists every released file except itself with its size and SHA-256 hash. Hashes detect mismatches; they do not establish mathematical correctness.

The workflow in `.github/workflows/verify.yml` runs the all-mode command when this payload is placed at a GitHub repository root. Each result is traceable through [claims.json](claims.json), and material release changes belong in [CHANGELOG.md](CHANGELOG.md). The README and manuscript identify the author and describe ChatGPT’s assistance.
