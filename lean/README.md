# Lean certificates

This directory contains every committed Lean source file from the research
snapshot `b8c9d31dac329b296d25042cc0b3300fd2b615f4`: eighteen mathematical modules,
the upstream import and audit files, and the adversarial examples. All are
copied without changes. The original twelve mathematical modules still match
the earlier `4d14cd975006fad4e172b1522cd81bdec4d81773` snapshot byte for byte.
The initial three independent Lake projects preserve their original Lean versions and
keep the two unrelated modules named `Collatz.lean` separate.

The new signed seven-step formalization proves that three explicit universal
family-capture hypotheses imply capture for every positive physical integer at
every launch phase. A separately labeled release-only module,
`inverse/Collatz/ReleaseBridge.lean`, supplies the immediate converse, proving
the manuscript's equivalence. The three family hypotheses remain unresolved;
neither unconditional seven-step capture nor the ordinary Collatz conjecture
is proved. The inverse-tree results retain their separate existential-seed
scope.

The fourth project, [frontier](frontier/), proves the single-B1 equivalence, the explicit five-guard complement theorem, unbounded guarded reductions and legal repayment. Its 32 source modules are audited alongside the original three projects. The original snapshot description above applies to those three projects.

## Reproduce the checks

Install [elan](https://github.com/leanprover/elan) and Python 3.10 or later. The
pinned Lean distributions contain every dependency; these projects do not use
Mathlib or third-party Lake packages. From the release root, run:

```sh
python3 lean/verify.py --check-inventory lean/inventory.json --output lean-verification.json
```

The runner builds clean temporary copies of all four projects. It discards
ambient Lean search paths, checks the version, runs the namespace axiom audit,
and extracts every named public source theorem's elaborated type and transitive
axiom dependencies. It additionally audits **every theorem declaration in each of the
51 mathematical modules**, including the release bridge, unused private theorems and
generated theorem helpers. The runner rejects an omitted source module, a mismatch
between named source theorems and the Lean inventory, unexpected axioms, and a
mismatch with the saved inventory. A Python text scan enforces the simple
single-namespace layout of this particular source snapshot; Lean supplies the
types and dependency information.

The runner also checks all 21 examples in `inverse/SevenAdversarial.lean` with
Lean. They include false row coefficients, phases, times and domain guards;
missing and duplicate coverage; a large-integer mutation; the wrong cycle
phase; and signed/general-admissibility boundary cases. These examples are
validation fixtures, not additional named research theorems.

For already unpacked official toolchains, use:

```sh
python3 lean/verify.py \
  --toolchain-419 /path/to/lean-4.19.0-linux \
  --toolchain-424 /path/to/lean-4.24.0-linux \
  --check-inventory lean/inventory.json \
  --output lean-verification.json
```

The two path arguments name installation roots containing `bin/lake`, not the
`bin` directories. The commands work without a checkout of the research repo.
The output report is generated evidence and need not be committed.

To inspect a project directly, change to its directory and run:

```sh
lake build
lake env lean -DwarningAsError=true Audit.lean
lake env lean -DwarningAsError=true Inventory.lean
```

In the `inverse/` project, run `lake build Collatz.ReleaseBridge` and
`lake env lean -DwarningAsError=true SevenAdversarial.lean` before the inventory
command. The original upstream `Collatz.lean` import file remains unchanged;
the extra build target makes the release-only bridge available to the full
inventory. The top-level Python runner performs all of these steps.

`Inventory.lean` prints JSON lines prefixed by `RELEASE_THEOREM` and a final
`RELEASE_AUDIT` summary. The collected types are the authoritative account of
quantifiers and hypotheses; the summaries below are a reading guide.

## Scope and model conventions

| Project | Lean | Mathematical modules | Named public theorems | Private source theorems |
| --- | --- | ---: | ---: | ---: |
| `inverse/` | 4.24.0 | 10 upstream + 1 release bridge | 110 | 37 |
| `perturbed/` | 4.19.0 | 6 | 86 | 43 |
| `sprint/` | 4.24.0 | 2 | 5 | 0 |
| `frontier/` | 4.24.0 | 32 | 624 | 8 |
| **Total** | two pinned versions | **51** | **825** | **88** |

The source counts count explicit `theorem` declarations. Generated equations,
induction helpers, and private declarations are audited too, but they are not
counted as additional named public results. `inventory.json` records the exact
statements, source locations, hashes, and axiom closures for the 825 named public
theorems, together with the complete-module audit counts.

### General signed physical foundations

The project directory retains its historical name `inverse/`, but now includes
general foundations and the signed seven-step reduction. `Collatz.Physical.Word`
encodes an arbitrary nonempty periodic word of integer impulses. A physical
state is stored as **(phase, integer)**, whereas the manuscript displays
**(integer, phase)**. `step` applies the impulse at the current phase and then
advances the phase. Zero continues through the same signed recurrence.

| Declaration in `Collatz.Physical` | Exact coverage |
| --- | --- |
| `admissible_iff_floor` | For arbitrary integer impulses, admissibility is equivalent to the existence of a binary height with `h(i+1)-h(i) ≤ d_i`; no conservativity assumption. |
| `admissible_conservative_iff_binary_height` | Admissibility together with zero sum is equivalent to a binary gradient representation. |
| `conservative_admissible_iff_alternating` | Under zero sum, admissibility is equivalent to the unit alphabet and cyclic alternation of consecutive nonzero impulses. |
| `height_unique`, `safe_iff_height` | For a nonzero word with a binary gradient, the height is unique and `Safe s ↔ h(phase) ≤ value`. The nonzero assumption handles the ambiguity of constant heights for the zero word. |
| `coordinate_conjugacy`, `coordinate_orbit`, `cycle_correspondence`, `rotation_admissible` | Exact signed height conversion, complete orbit and return correspondence, and admissibility under rotation. |
| `signed_parity_lift` | Every depth-`k` signed dyadic lift has the same phase and a positive odd affine multiplier, for every integer lift parameter, including crossings of zero. |
| `cycle_multiplier_lt_one` | Any nonempty return on a safe orbit of an admissible conservative word satisfies `3^oddCount < 2^k`. |

The arbitrary-impulse theorem is stated in binary-floor form, not literally as
the manuscript's separation-of-negative-impulses criterion. The cyclic
alternation theorem directly matches its conservative specialization. The
formal parity lift does not state the entire parity-word/residue-class
bijection or name its multiplier as `3^j`. Equality of primitive height and
forcing periods, and the scalar-versus-augmented primitive-period argument,
are not separate declarations here. The cycle multiplier theorem is arithmetic;
the cosine derivative calculation and local analytic attraction are not
formalized in Lean.

### Signed seven-step conditional capture

The exact chronological impulse word is `[0,0,+1,-1,0,+1,-1]`, with height
`[0,0,0,1,0,0,1]`. The distinguished physical cycle has scalar values
`[0,0,0,1,1,2,2]` at phases zero through six. Section states have
`z = n+1-h_i = 3m > 0` and phase in `{1,2,3,5}`. The section rank has weights
`(4,7,4,5)`. All assumptions and conclusions use the same signed dynamics.

| Module | Exact coverage |
| --- | --- |
| `Collatz/SevenStep.lean` | Cycle closure, primitive forcing, admissibility, physical/height conversion, section definitions and soundness of the signed affine first-hit checker for every natural parameter. |
| `Collatz/SevenFrontier.lean` | Section entry within **six** ticks for every strictly positive physical seed at every phase; strict first-return descent outside the three families for `m ≥ 6`; captured small cases; well-founded conditional global capture. |
| `Collatz/SevenRows.lean` | All 43 first-return rows, their unique exhaustive domain partition, full parameter representation, rank changes and classification, the five finite captured exceptions, and a positive seed attaining the six-tick entry bound. |
| `Collatz/ReleaseBridge.lean` | The release-only theorem `Collatz.ReleaseBridge.global_capture_iff_three`: capture of every positive physical seed at every phase **if and only if** the three hypotheses below hold. |

Writing `site i m = (i, 3m-1+h_i)`, the exact remaining hypotheses are

```text
B1  : ∀ t : Nat, 0 < t → Captured (site 1 (2*t))
A3  : ∀ t : Nat, Captured (site 3 (4*t+3))
N03 : ∀ t : Nat, Captured (site 5 (8*t+2))
```

The upstream theorem `Collatz.SevenStep.global_capture_of_three` proves the
implication from those hypotheses. Its conclusion quantifies over every
`i : Fin 7` and `n : Int` subject to `0 < n`. The release bridge's converse
uses only positivity of the three family launches; it adds no assumptions.

`Row.sound` proves the stated arrival time and absence of every earlier
strictly positive-time section visit. `partition` selects one row, while
`parameter_of_applies` requires `0 < m` to recover its unrestricted natural
parameter. The rank differences are in physical signed coordinates:
`signedRank = weight * z = 3W` on the section. Positive scaling preserves every
strict comparison. For zero residues, Lean takes the first positive multiple
as the base, whereas the paper uses a parameter starting at one; the two
parameterizations give the same rays. All 43 endpoints, times, domains and rank
changes have been cross-checked under this conversion.

The manuscript separately proves an eleven-update entry bound for **all safe
states** through its phase-zero reconstruction. The stronger six-update Lean
statement is explicitly about **strictly positive physical seeds**; it should
not be cited with an expanded zero-state domain. The older four-family section,
its relational merger rules, and the optimality obstruction for positive
phase-affine ranks are not formalized by these modules. No remaining universal
family hypothesis is discharged.

### Three-step inverse branches and trees

The shortcut map is `T(n) = n/2` for even `n`, and `(3n+1)/2` for odd `n`.
`Collatz.Phase` follows the offsets `(+1, 0, -1)`. Values are natural numbers;
`Safe` permits zero in the plus phase and requires positivity in the other
phases. `step_safe`, `step_faithful`, and `run_safe` connect the natural-number
implementation to signed addition and rule out silent truncation on the stated
safe domain. Every positive initial seed is safe.

| Module | Principal declarations and scope |
| --- | --- |
| `Collatz/Branches.lean` | `A_parent`, `B_parent`, `A_good`, `B_good`, growth and size bounds certify two exact six-step inverse branches on the eligible set. |
| `Collatz/Tree.lean` | `endpoint_injective`, `endpoint_returns`, `endpoint_weighted_bound`, and `fixed_depth_lower_bound` certify distinct finite inverse paths, their return, and quantitative bounds. |
| `Collatz/Coverage.lean` | `all_phase_preimages` gives `2^k` distinct positive predecessors of every **safe phase-tagged target**, with an explicit size bound and a common return time. |
| `Collatz/BinaryZoom.lean` | `residue_return` certifies a designated residue cylinder obtained by repeated inverse lifts `n ↦ 8n+6`. |

`all_phase_preimages` quantifies over launch phase, target phase, safe target,
and depth. Its conclusion is an existential family of seeds. It says neither
that every seed belongs to this family nor that the stated return time is the
first visit. A periodic target therefore has a large basin of explicitly
constructed predecessors; universal attraction remains a separate statement.

### Perturbed project: six related, distinct components

**Zero conventions differ across these modules.** `PerturbedCollatz.step` in
`Collatz.lean` explicitly makes zero absorbing. Its orbit-lift theorem requires
strict positivity of the original orbit throughout the lifted prefix.
`BasinGrowth.lean` and the signed arithmetic modules use integer-valued updates
that continue through zero. A theorem from one model cannot be transferred to
the other without a proved bridge on an appropriate domain.

| Module | Principal result | Hypotheses and boundary |
| --- | --- | --- |
| `Collatz.lean` | `orbit_seed_lift`, `adaptive_growth`, `unbounded_iff_escape`, `nonperiodic_parity_escapes` | Absorbing-zero natural dynamics for the orbit definitions. The last two results concern abstract deterministic paths with finitely many phase values. Nonperiodicity is assumed where required. Adaptive growth uses a state-dependent controller. |
| `BasinGrowth.lean` | `many_preimages`, `many_escaping`, `not_least_of_meeting` | Signed word `[-1,0,0,+1,0,0,0]`. Every positive target has `4^depth` distinct positive predecessors bounded by `128^depth * target`. `many_escaping` assumes that the target escapes. |
| `InverseBranch.lean` | `three_laps_preimages` | A mixed binary height word and a nonnegative target yield two distinct nonnegative preimages after three laps in the stated normalized dynamics. |
| `ResidueTrack.lean` | `balanced_obstruction` | A finite signed word, every offset at most one, sum zero, and a nonzero entry. It classifies a circular residue obstruction versus a gate within three inverse laps. |
| `TernaryPump.lean` | `exists_ge_geomSum_mod` and lifting lemmas | Arithmetic of geometric sums when the base is one modulo three. These support residue control; they do not assert trajectory capture. |
| `ProgressionSteering.lean` | `progression_steering` | Modulus `n+1` coprime to six; arbitrary padding and two residue classes. The target must satisfy both its requested residue class and an additional congruence `3^n ∣ z-c`. |

For `ProgressionSteering.progression_steering`, the word and integer `c` are
chosen before the universally quantified target `z`. The theorem supplies a
seed in the requested other residue class and exact replay for targets satisfying
both guards. It does not remove the ternary guard, assert capture for all seeds,
or directly establish positivity for unrestricted integer targets. The separate
`target_le_seed` theorem provides a bound under its own nonnegativity and
admissibility assumptions. The residue permutation construction uses classical
choice through noncomputable definitions; this is a proof, without an extracted
routing algorithm supplied here.

The signed word in `BasinGrowth.lean` differs from the newer research schedule
`[0,0,+1,-1,0,+1,-1]`. Its certificates must retain their own schedule label.

### Sprint project: local seven-step ingredients

`RootInverseHeight.lean` proves positivity and exact replay of one inverse step
under a positive target and the required ternary guard. It also proves
`3^(grows word) * replay word z ≤ 2^(length word) * z` for the syntactic inverse
word. The inequality alone does not assert that every branch of that word is
legal: legal replay still requires the stepwise guards.

`RootPacket.lean` proves `packet_guard_and_image`, a universal arithmetic identity
for the parameterized contracting packet and the displayed growing-macro image.
The Lean declaration itself does not define the full seven-step return map,
certify every return-domain guard, or prove global termination.

Neither sprint file formalizes a full first-return classification or universal
capture theorem. The separate signed seven-step modules above now formalize
the three-family section and its conditional reduction. They do not turn the
sprint packet identity into a proved whole-domain merger rule.

## Verification record and trust boundary

On 2026-11-26, fresh temporary builds of all four projects succeeded with their
pinned official Lean toolchains. The normal Lean checker accepted all included
proofs and the original 21 adversarial examples and the frontier fixtures. The full audits covered 6273 theorem
constants, including private declarations and generated helpers; this diagnostic
count is not a count of distinct mathematical results. The complete-module
theorem dependency audits accepted only `propext`,
`Quot.sound`, and `Classical.choice`; the exact subset for each named theorem is
in `inventory.json`. No `sorryAx`, custom axiom, or native-evaluation axiom is
accepted by the audit.

This verifies the formal declarations and their dependencies under Lean's
usual trusted implementation and standard axioms. No independent kernel checker
or separate proof-object comparator was run. Matching these declarations to the
intended informal claims remains a mathematical review task, especially at the
zero boundary, phase changes, normalized coordinates, branch guards, and
conditional statements described above. A passing build is not a proof of a
stronger sentence in the manuscript.

## External problem supporting project

`external_problems/` is a separate Lean 4.35.0, Std-only project with five
abstract integer prefix/depth statements and 29 generated theorem helpers.
It proves no M4/R8/R9/O3′ headline result. Its separately frozen specifications,
raw elaborated types and helper axiom closures are in
[`external_problems/inventory.json`](external_problems/inventory.json).
The [supporting verification protocol](external_problems/VERIFICATION.md)
requires the separate mandatory CI `external-support` job in addition to the
legacy verification above. Challenge holes are isolated specification inputs,
never accepted proof imports. Local clean build alone is partial assurance.
