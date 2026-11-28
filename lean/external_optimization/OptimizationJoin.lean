import OptimizationCycleCode
import OptimizationAccuracy

/-! The executable optimizer equals the original canonical minimum. -/
namespace ExternalO3OptimizationJoin
open ExternalO3OptimizationCode ExternalO3OptimizationDraft
open ExternalO3OptimizationAlgorithm ExternalO3OptimizationCycleCode
open ExternalO3OptimizationArithmetic

theorem optimizer_eq_numerator (p : Input) :
    optimizer p = optimalNumerator (ExternalO3RateDraft.succDepth p.1) (base p) (cap p) := by
  have hM : 2 ≤ base p := by unfold base; omega
  have hJ : 2 ≤ cap p := by unfold cap; omega
  have hmin := numerator_minimum_well_posed
    (ExternalO3RateDraft.succDepth p.1) (base p) (cap p) hM hJ
  apply Nat.le_antisymm
  · obtain ⟨D, hD, hvalue⟩ := hmin.2.1
    obtain ⟨mask, hbound, hmask⟩ := maskSubset_surjective p D
    have hsafe : safe p mask = true := by
      apply (safe_iff_cycle_safe p mask).mpr
      simpa only [hmask] using hD
    calc
      optimizer p ≤ cost p mask := (optimizer_spec p).2.1 mask hbound hsafe
      _ = deletionUnits (ExternalO3RateDraft.succDepth p.1) (base p) (cap p)
          (maskSubset p mask) := cost_eq_deletionUnits p mask
      _ = deletionUnits (ExternalO3RateDraft.succDepth p.1) (base p) (cap p) D := by rw [hmask]
      _ = optimalNumerator (ExternalO3RateDraft.succDepth p.1) (base p) (cap p) := hvalue
  · obtain ⟨mask, _, hsafe, hvalue⟩ := optimizer_attains p
    have hD := (safe_iff_cycle_safe p mask).mp hsafe
    calc
      optimalNumerator (ExternalO3RateDraft.succDepth p.1) (base p) (cap p) ≤
          deletionUnits (ExternalO3RateDraft.succDepth p.1) (base p) (cap p)
            (maskSubset p mask) := hmin.2.2 _ hD
      _ = cost p mask := (cost_eq_deletionUnits p mask).symm
      _ = optimizer p := hvalue.symm

theorem computable_exact_optimizer : ComputableExactOptimizer := by
  refine ⟨optimizer, computable_optimizer, ?_⟩
  intro h0 m0 j0
  simpa only [base, cap] using optimizer_eq_numerator (h0, m0, j0)

theorem computable_dyadic_approximation : ComputableDyadicApproximation :=
  ExternalO3OptimizationAccuracy.computable_exact_optimizer_implies_dyadic_approximation
    computable_exact_optimizer

end ExternalO3OptimizationJoin
