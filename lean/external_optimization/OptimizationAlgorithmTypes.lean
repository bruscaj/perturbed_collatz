import OptimizationExpectedTypes
import Mathlib.Computability.Partrec

/-! UNFROZEN genuine computability targets. No algorithm is implemented here.
Outputs are natural numerators, not noncomputable real logarithms.
-/
namespace ExternalO3OptimizationDraft
open ExternalO3GeneralDraft

/-- The input triple uses the standard Primcodable natural-product encoding.
The h, M, J parameters are h0+1, m0+2, j0+2 respectively. -/
def ComputableExactOptimizer : Prop :=
  ∃ A : (ℕ × ℕ × ℕ) → ℕ, Computable A ∧
    ∀ h0 m0 j0 : ℕ,
      A (h0, m0, j0) = optimalNumerator (ExternalO3RateDraft.succDepth h0) (m0 + 2) (j0 + 2)

/-- A total computable rational bracket at any requested dyadic accuracy.
The numerator is tied to the precise finite graph, so an arbitrary oracle-like
approximation is not substituted for the cycle-deletion optimization. -/
def ComputableDyadicApproximation : Prop :=
  ∃ A : (ℕ × ℕ) → ℕ, Computable A ∧
    ∀ h0 b : ℕ,
      let h := ExternalO3RateDraft.succDepth h0
      let M := h.val + b + 2
      A (h0, b) = optimalNumerator h M M ∧
      let q : ℝ := (A (h0, b) : ℝ) / ((2 : ℕ) ^ commonExponent h M M : ℝ)
      q ≤ ExternalO3RateDraft.failureInfimum h ∧
      ExternalO3RateDraft.failureInfimum h ≤ q + (2 : ℝ) ^ (-(b : ℤ))

end ExternalO3OptimizationDraft
