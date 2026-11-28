# External research drafts

These are ChatGPT-assisted written candidates by Jake S. Brusca, offered for
scrutiny as part of a personal research project. They have not been refereed by
a human expert or fully formalized. No external open problem is certified as
solved. The existing [core paper](../paper.pdf) retains its separate scope.

| Draft | Mathematical development | Limit |
| --- | --- | --- |
| [Finite-information Syracuse potentials](finite_information_lyapunov/README.md) | Literal odd-seed density for arbitrary depth-one corrections; exact infimum and nonattainment proof | All 14 depth-one frozen targets have Lean proofs; full checker CI passed at8524770; not the full arbitrary-depth O3′ problem |
| [Near-extremal word entropy](arithmetic_bridge_pressure/README.md) | Source/depth correspondence, large-tilt pressure, matching entropy lower bound and proposed R9 expansion | Near-one rung M4 and large-tilt convergence only; not full M4 or R8 |

The [four-problem source/status register](external_problems/README.md) gives the
exact interpretation of M4, R8, R9 and O3′, evidence tiers and unresolved gates.
Both drafts have TeX sources and visually reviewed PDFs: [potentials](finite_information_lyapunov/paper.pdf) and [entropy](arithmetic_bridge_pressure/paper.pdf). Rebuild with `python3 papers/build.py`; `--check` additionally checks byte identity on the recorded toolchain. The full release remains unfinished.

The common finite foundation is
[`lean/external_problems`](../lean/external_problems/README.md): abstract integer
prefix/depth equivalence and final-endpoint adjustment. Instantiation at the
irrational logarithmic slope and all infinite analytic conclusions still require
full proofs. The [exact finite consumers](../certificates/external_problems/verify.py)
use literal source words and Syracuse strides independently of the Lean model.

No public build depends on a private clone. Review in separate AI contexts is
disclosed assistance, not human expert validation, author acknowledgment or a
priority claim. The owner's final merge and release decisions remain pending.

The separate [depth-one analytic package](../lean/external_analysis/README.md) proves the literal Syracuse model for h=1. Its dedicated `external-analysis-h1` CI job passed full replay, comparison and hostile fixtures at8524770; source-pinned receipts are in `verification/external_analysis/`. Later final-head regressions remain required.

A [complete finite-depth density reconstruction](../lean/external_population/GENERAL_DENSITY_PROOF.md) now accompanies the depth-one paper. Its separate formal library proves all22frozen source/density targets with ordinary clean-build/axiom checks; independent full checker CI is pending. The rate and higher-depth optimization remain separate unfinished parts.
