# O3′: exact source requests and proved answers

The pinned primary statement is Polson–Sokolov, edition1 v1.4.0, [prob:ch11:o3p, lines65–71](https://github.com/VadimSokolov/collatz/blob/5840497a23fc0d64127b850aea68862d7c93f2b7/book/chapters/ch11_open.tex#L65-L71). Read with its block proposition and depth-two exercise, the information consists of the current remaining run and the next h−1 post-exit block lengths. The correction is an arbitrary real function of that h-tuple, with no boundedness, regularity, computability or integrability assumption. Exit valuations are not extra correction inputs. Failure is nondecrease at the next Syracuse stride, including equality; density is relative natural density among positive odd seeds. The map continues at 1.

The literal density theorem is proved before optimization: every allowed correction has an actual odd-seed density equal to the exact cylinder-weight expression. No independence along a single integer orbit or integer convergence is assumed. The infimum p_h is taken over these actual achieved densities.

| Explicit source request | Proved answer |
| --- | --- |
| Determine the depth-h infimum | A total computable scheme determines p_h uniformly in positive h and requested dyadic accuracy b. With M=J=h+b+2 it computes the exact finite graph numerator A, and q=A/2^(J+hM) satisfies q≤p_h≤q+2^(−b). |
| Does it tend to zero? | Yes: p_h→0 as h→∞. Each fixed-depth population density was proved first; no interchange of the seed and depth limits is asserted. |
| How fast? | 1/[4(h+33)]≤p_h≤5/(2h), hence p_h=Θ(1/h). No optimal leading constant is claimed. |

The first answer is algorithmic determination by terminating, certified rational enclosures. It does not say p_h is rational or provide a short symbolic formula. The exhaustive program has no practical complexity bound, and no higher-depth numerical table is supplied. Closed general-depth formulas, efficient algorithms, sharp constants and attainment at h≥2 are additional questions rather than explicit requirements of the source's three requests.

At h=1 there is also an exact series, strict nonattainment over every correction, and an 80-term rational enclosure of width2^(−81), approximately 0.14313725116205436. Compatibility with the general-depth model is formally proved.

[The manuscript](../finite_information_lyapunov/paper.pdf) and its public density, rate and optimization companions contain the theory and explicit algorithms. [Full source-pinned assurance at b5dcda3](../../verification/external_optimization/README.md) covers all 15 optimization statements / 952 theorem-helper closures, six checker modes in both replay and comparison, eighteen controls, and the full seven-job regression.

These results answer the three stated questions for this precise run-length-only class in the algorithmic sense above. They do not enlarge the correction to inspect exit labels, arbitrary launch digits or an infinite window. No ordinary Collatz convergence, external author endorsement, novelty certification or independent human expert refereeing follows. ChatGPT assisted with proof construction, implementation, writing and separate-context reviews; the proof authors and some reviewers overlap.
