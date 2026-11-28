import PressureAnalyticExpectedTypes
import Mathlib.Analysis.Subadditive

namespace ExternalBridgePressureAnalyticFekete
open ExternalBridgePressureAnalyticDraft
open Filter Set
open scoped Topology
noncomputable section

/-- Fekete for actual positive-volume ratios, with a finite linear roof. -/
theorem superadditive_tendsto_sSup (a : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hroof : ∀ n : ℕ, a n ≤ C * n)
    (hadd : ∀ m n : ℕ, a m + a n ≤ a (m+n)) :
    Tendsto (fun n : ℕ => a n/(n : ℝ)) atTop
      (nhds (sSup {v : ℝ | ∃ L : ℕ, 1 ≤ L ∧ v = a L/(L : ℝ)})) := by
  have hneg : Subadditive (fun n => -a n) := by
    intro m n
    dsimp
    linarith [hadd m n]
  have hbdd : BddBelow (Set.range (fun n : ℕ => -a n/(n : ℝ))) := by
    refine ⟨-C, ?_⟩
    rintro y ⟨n, rfl⟩
    by_cases hn : n = 0
    · simp [hn]
      exact hC
    · have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      apply (le_div_iff₀ hnR).2
      nlinarith [hroof n]
  let S : Set ℝ := {v : ℝ | ∃ L : ℕ, 1 ≤ L ∧ v = a L/(L : ℝ)}
  have hset : ((fun n : ℕ => -a n/(n : ℝ)) '' Set.Ici 1) = -S := by
    ext y
    simp only [Set.mem_image, Set.mem_Ici, Set.mem_neg, S, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨n, hn, by ring⟩
    · rintro ⟨n, hn, hy⟩
      refine ⟨n, hn, ?_⟩
      rw [neg_div]
      linarith
  have hlim : -hneg.lim = sSup S := by
    rw [Subadditive.lim, hset, Real.sInf_neg, neg_neg]
  have h := (hneg.tendsto_lim hbdd).neg
  simpa only [neg_div, neg_neg, hlim] using h

/-- Conditional integration helper: actual finite infimum facts remain to be proved.
This theorem alone does not discharge the frozen FeketeCandidateLimit root. -/
theorem fekete_candidate_limit_of_phase_infimum_facts
    (hwell : PhaseInfimumWellPosed) (hadd : PhaseInfimumSuperadditivity) :
    FeketeCandidateLimit := by
  intro lam hlam
  have hC : 0 ≤ Real.log 4 + lam := add_nonneg (Real.log_nonneg (by norm_num)) hlam
  have hroof : ∀ n : ℕ, phaseInfimum n lam ≤ (Real.log 4+lam)*(n : ℝ) := by
    intro n
    obtain ⟨_, _, _, _, hn, _, _⟩ := hwell.2 lam hlam n
    simpa only [mul_comm] using hn
  have h := superadditive_tendsto_sSup (fun n => phaseInfimum n lam)
    (Real.log 4+lam) hC hroof (hadd lam hlam)
  simpa only [candidatePressure, ite_eq_left hlam, pressureValues] using h

end
end ExternalBridgePressureAnalyticFekete
