import OptimizationAlgorithmTypes
import OptimizationDensity

/-! Dependency preparation only: an unconditional explicit tail estimate and
a conditional reduction from the exact computable optimizer to A02.
No unconditional ComputableDyadicApproximation theorem is asserted here. -/
namespace ExternalO3OptimizationAccuracy
open ExternalO3OptimizationDraft ExternalO3GeneralDraft
open ExternalO3OptimizationDeletion ExternalO3OptimizationDensity

theorem accuracy_cap_tail_bound (h : Depth) (b : ℕ) :
    tailAllowance h (h.val + b + 2) (h.val + b + 2) ≤ (2 : ℝ) ^ (-(b : ℤ)) := by
  have hn : h.val + 2 ≤ 2 ^ (h.val + 2) := le_of_lt Nat.lt_two_pow_self
  have hr : (h.val : ℝ) + 2 ≤ (2 : ℝ) ^ (h.val + 2) := by exact_mod_cast hn
  have hp : (0 : ℝ) ≤ (2 : ℝ) ^ (-((h.val + b + 2 : ℕ) : ℤ)) := by positivity
  unfold tailAllowance
  calc
    _ = ((h.val : ℝ) + 2) * (2 : ℝ) ^ (-((h.val + b + 2 : ℕ) : ℤ)) := by ring
    _ ≤ (2 : ℝ) ^ (h.val + 2) * (2 : ℝ) ^ (-((h.val + b + 2 : ℕ) : ℤ)) :=
      mul_le_mul_of_nonneg_right hr hp
    _ = (2 : ℝ) ^ (-(b : ℤ)) := by
      rw [← zpow_natCast (2 : ℝ) (h.val + 2), ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      congr 1
      push_cast
      ring

/-- h=h0+1 and M=J=h+b+2 correspond to optimizer cap offsets h0+b+1. -/
def accuracyInput (p : ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (p.1, p.1 + p.2 + 1, p.1 + p.2 + 1)

theorem accuracy_input_computable : Computable accuracyInput := by
  have hs : Primrec (fun p : ℕ × ℕ => p.1 + p.2 + 1) :=
    Primrec.succ.comp (Primrec.nat_add.comp Primrec.fst Primrec.snd)
  exact (Primrec.fst.pair (hs.pair hs)).to_comp

/-- This explicit A01 hypothesis must be supplied by a real optimizer proof
before the parent can assemble an unconditional A02 result. -/
theorem computable_exact_optimizer_implies_dyadic_approximation
    (hexact : ComputableExactOptimizer) : ComputableDyadicApproximation := by
  obtain ⟨A, hA, hcorrect⟩ := hexact
  refine ⟨fun p => A (accuracyInput p), hA.comp accuracy_input_computable, ?_⟩
  intro h0 b
  let h := ExternalO3RateDraft.succDepth h0
  let M := h.val + b + 2
  have hM : 2 ≤ M := by dsimp [M]; omega
  have hcap : (h0 + b + 1) + 2 = M := by
    dsimp [M, h, ExternalO3RateDraft.succDepth]
    omega
  have hvalue : A (accuracyInput (h0, b)) = optimalNumerator h M M := by
    change A (h0, h0 + b + 1, h0 + b + 1) = optimalNumerator h M M
    simpa only [hcap] using hcorrect h0 (h0 + b + 1) (h0 + b + 1)
  change A (accuracyInput (h0, b)) = optimalNumerator h M M ∧
    (A (accuracyInput (h0, b)) : ℝ) / ((2 : ℕ) ^ commonExponent h M M : ℝ) ≤
      ExternalO3RateDraft.failureInfimum h ∧
    ExternalO3RateDraft.failureInfimum h ≤
      (A (accuracyInput (h0, b)) : ℝ) / ((2 : ℕ) ^ commonExponent h M M : ℝ) +
        (2 : ℝ) ^ (-(b : ℤ))
  refine ⟨hvalue, ?_⟩
  rw [hvalue, ← finiteOptimum_real]
  have hsandwich := literal_infimum_sandwich h M M hM hM
  have htail : tailAllowance h M M ≤ (2 : ℝ) ^ (-(b : ℤ)) := accuracy_cap_tail_bound h b
  refine ⟨hsandwich.1, ?_⟩
  linarith [hsandwich.2]

end ExternalO3OptimizationAccuracy
