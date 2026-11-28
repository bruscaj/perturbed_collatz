import Arithmetic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Exact literal logarithmic increments and their vanishing positive error. -/
namespace ExternalO3Gains
open ExternalO3Spec ExternalO3Arithmetic Filter
open scoped Topology

noncomputable def logError (x : ℕ) : ℝ :=
  Real.log (1 + 1 / (3 * (x : ℝ)))

theorem logError_positive (x : ℕ) (hx : 0 < x) : 0 < logError x := by
  have hxR : (0 : ℝ) < (x : ℝ) := Nat.cast_pos.mpr hx
  have hf : (0 : ℝ) < 1 / (3 * (x : ℝ)) := one_div_pos.mpr (by positivity)
  apply Real.log_pos
  linarith

theorem literal_log_increment (x : ℕ) (hx : IsOddSeed x) :
    Real.log (stride x : ℝ) - Real.log (x : ℝ) =
      Real.log 3 - (strideValuation x : ℝ) * Real.log 2 + logError x := by
  have hxR : (0 : ℝ) < (x : ℝ) := Nat.cast_pos.mpr hx.1
  have hd := (valuation_foundation x hx).2.1
  have hs : (stride x : ℝ) = (3 * (x : ℝ) + 1) / (2 : ℝ) ^ strideValuation x := by
    unfold stride
    rw [Nat.cast_div_charZero hd]
    simp
  have hp : (0 : ℝ) < (2 : ℝ) ^ strideValuation x := pow_pos (by norm_num) _
  have hf : (3 : ℝ) * (x : ℝ) + 1 =
      (3 * (x : ℝ)) * (1 + 1 / (3 * (x : ℝ))) := by
    field_simp
  have h3x : (3 : ℝ) * (x : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have herr : (1 : ℝ) + 1 / (3 * (x : ℝ)) ≠ 0 := ne_of_gt (by positivity)
  unfold logError
  rw [hs, Real.log_div (by positivity) (ne_of_gt hp), Real.log_pow, hf,
    Real.log_mul h3x herr, Real.log_mul (by norm_num) (ne_of_gt hxR)]
  ring

theorem ascending_increment (φ : Correction) (x : ℕ) (hx : IsOddSeed x)
    (hr : 2 ≤ blockLength x) :
    rawPotential φ (stride x) - rawPotential φ x =
      ascendingGain φ (blockLength x) + logError x := by
  have hk := valuation_one_of_long_block x hx hr
  have hb := block_decrements x hx hr
  have hb' : blockLength (stride x) = blockLength x - 1 := by omega
  have hg := literal_log_increment x hx
  rw [hk] at hg
  simp only [Nat.cast_one, one_mul] at hg
  unfold rawPotential ascendingGain
  rw [hb', Real.log_div (by norm_num) (by norm_num)]
  linarith

theorem block_one_of_exit (x : ℕ) (hx : IsOddSeed x)
    (hk : 2 ≤ strideValuation x) : blockLength x = 1 := by
  have hp := block_length_positive x hx
  by_contra hne
  have hr : 2 ≤ blockLength x := by omega
  have := valuation_one_of_long_block x hx hr
  omega

theorem exit_increment (φ : Correction) (x : ℕ) (hx : IsOddSeed x)
    (hk : 2 ≤ strideValuation x) :
    rawPotential φ (stride x) - rawPotential φ x =
      exitGain φ (strideValuation x) (blockLength (stride x)) + logError x := by
  have hb := block_one_of_exit x hx hk
  have hg := literal_log_increment x hx
  unfold rawPotential exitGain
  rw [hb]
  linarith

theorem logError_tendsto_zero : Tendsto logError atTop (𝓝 0) := by
  have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hfrac : Tendsto (fun n : ℕ => (1 : ℝ) / (3 * (n : ℝ))) atTop (𝓝 0) := by
    simpa [one_div, mul_inv_rev, mul_comm] using hinv.const_mul ((3 : ℝ)⁻¹)
  have hsum : Tendsto (fun n : ℕ => (1 : ℝ) + 1 / (3 * (n : ℝ))) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hfrac
  change Tendsto (fun n : ℕ => Real.log (1 + 1 / (3 * (n : ℝ)))) atTop (𝓝 0)
  have hlog : Tendsto (fun n : ℕ => Real.log (1 + 1 / (3 * (n : ℝ))))
      atTop (𝓝 (Real.log 1)) :=
    (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hsum
  simpa only [Real.log_one] using hlog

theorem seed_logError_tendsto_zero :
    Tendsto (fun n : ℕ => logError (2 * n + 1)) atTop (𝓝 0) := by
  apply logError_tendsto_zero.comp
  exact tendsto_atTop.2 (fun b => eventually_atTop.2 ⟨b, fun n hn => by omega⟩)

theorem stable_seed_error (g : ℝ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (0 ≤ g + logError (2 * n + 1) ↔ 0 ≤ g) := by
  by_cases hg : 0 ≤ g
  · refine ⟨0, fun n _ => ?_⟩
    exact ⟨fun _ => hg, fun _ =>
      add_nonneg hg (le_of_lt (logError_positive (2 * n + 1) (by omega)))⟩
  · have hlt : g < 0 := lt_of_not_ge hg
    have he : ∀ᶠ n : ℕ in atTop, logError (2 * n + 1) < -g :=
      (tendsto_order.1 seed_logError_tendsto_zero).2 (-g) (by linarith)
    rcases eventually_atTop.1 he with ⟨N, hN⟩
    refine ⟨N, fun n hn => ?_⟩
    have hs := hN n hn
    constructor
    · intro h
      linarith
    · intro h
      exact False.elim (hg h)

theorem fails_iff_increment (φ : Correction) (x : ℕ) (hx : IsOddSeed x) :
    FailsAt φ x ↔ 0 ≤ rawPotential φ (stride x) - rawPotential φ x := by
  simp only [FailsAt, hx, true_and, sub_nonneg]

theorem ascending_stabilizes (φ : Correction) (a : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → blockLength (2 * n + 1) = a + 2 →
      (FailsAt φ (2 * n + 1) ↔ 0 ≤ ascendingGain φ (a + 2)) := by
  rcases stable_seed_error (ascendingGain φ (a + 2)) with ⟨N, hN⟩
  refine ⟨N, fun n hn hb => ?_⟩
  have hx : IsOddSeed (2 * n + 1) := ⟨by omega, by omega⟩
  rw [fails_iff_increment φ _ hx,
    ascending_increment φ _ hx (by omega), hb]
  exact hN n hn

theorem exit_stabilizes (φ : Correction) (a b : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      strideValuation (2 * n + 1) = a + 2 →
      blockLength (stride (2 * n + 1)) = b + 1 →
      (FailsAt φ (2 * n + 1) ↔ 0 ≤ exitGain φ (a + 2) (b + 1)) := by
  rcases stable_seed_error (exitGain φ (a + 2) (b + 1)) with ⟨N, hN⟩
  refine ⟨N, fun n hn hk hr => ?_⟩
  have hx : IsOddSeed (2 * n + 1) := ⟨by omega, by omega⟩
  rw [fails_iff_increment φ _ hx,
    exit_increment φ _ hx (by omega), hk, hr]
  exact hN n hn

end ExternalO3Gains
