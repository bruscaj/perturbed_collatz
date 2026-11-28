# Optimization independent assurance

All seven mandatory jobs passed [run 46111672437](https://github.com/bruscaj/perturbed_collatz/actions/runs/46111672437) at source `b5dcda3404b14b43e1985c2e31219ce811e46881`, tree `76ee312e9f756a0dceba6ea3d900dd81b7858168`.

The optimization project covered all 15 frozen required statements,49 modules and 952 own/reused theorem/helper closures. Fresh complete proof export/replay and trusted frozen-statement comparison each received acceptance from Lean default, Lean paranoid, lean4lean, nanoda, con-leche and con-ron. Only propext, Quot.sound and Classical.choice occur in the audited theorem closures. The exported closure had103,158,206 bytes, SHA256 `1bb90a10488f0a22e713b19b2a2d2e2fd728ce33f6101fd950b54901aa9ea01c`.

Eighteen controls were rejected. The full positive15-target pipeline passed again before the actual comparator rejection of a True wrapper, the audit rejection of a hidden imported optimizer axiom, and Lean rejection of the corrupted production executable. The positive executable proves optimizer(0,0,0)=1; changing its cycle base from3 to2 makes that same decidable proposition false. Hash/coverage controls are separately identified and are not presented as semantic comparator tests.

[CI_ARTIFACTS.json](CI_ARTIFACTS.json) records all 63 source/configuration/documentation digests, coverage, declaration counts and archive hashes. `ci_artifacts/` preserves all seven complete GitHub ZIP artifacts, verified against their original archive digests; this retains full reports and losslessly compressed logs without duplicating verbose dumps. For example run `python3 -m zipfile -e ci_artifacts/external-optimization.zip /tmp/optimization-ci-evidence` to inspect every optimizer report and log. Other archives preserve the full regression receipts, including43 legacy checks.

The artifact-name suffix is GitHub's synthetic PR event SHA. The actual checked source/tree are recorded above and in the source-tree receipts. Historical receipts certify those exact inputs; later documentation or source changes require their own regression. Subsequent README/inventory updates do not retroactively change this checked snapshot.

These results are independently machine-checked against the specified formal statements. They do not establish novelty or human expert refereeing. The complete M4/R8/R9 research program remains unfinished.
