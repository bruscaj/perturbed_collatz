import UnrestrictedExpectedTypes
import BridgeArithmetic

/-! Actual-slope bounds and deterministic three-step rotation estimates. -/
namespace ExternalM4UnrestrictedRotation
open ExternalFiniteBridgeDraft ExternalM4UnrestrictedDraft

theorem slope_bounds : SlopeBounds := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlo : (3 : ℝ) * Real.log 2 < 2 * Real.log 3 := by
    have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 2 ^ 3)
      (by norm_num : (2 : ℝ) ^ 3 < 3 ^ 2)
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hhi : (3 : ℝ) * Real.log 3 < 5 * Real.log 2 := by
    have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 3 ^ 3)
      (by norm_num : (3 : ℝ) ^ 3 < 2 ^ 5)
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  constructor
  · change (3 / 2 : ℝ) < Real.log 3 / Real.log 2
    apply (lt_div_iff₀ htwo).mpr
    nlinarith
  · change Real.log 3 / Real.log 2 < (5 / 3 : ℝ)
    apply (div_lt_iff₀ htwo).mpr
    nlinarith

theorem fract_sub_nat_eq (x : ℝ) (n : ℕ)
    (hlo : 0 ≤ x - (n : ℝ)) (hhi : x - (n : ℝ) < 1) :
    Int.fract x = x - (n : ℝ) := by
  rw [← Int.fract_sub_natCast x n]
  exact Int.fract_eq_self.mpr ⟨hlo, hhi⟩

theorem triple_rotation_high_low : TripleRotationHighLow := by
  intro β y hβlo hβhi hylo hyhi
  have hy : Int.fract y = y := Int.fract_eq_self.mpr ⟨hylo, hyhi⟩
  constructor
  · by_cases hhalf : 1 / 2 ≤ y
    · refine ⟨0, ?_⟩
      simpa only [Fin.val_zero, Nat.cast_zero, zero_mul, add_zero, hy] using hhalf
    · have hylow : y < 1 / 2 := lt_of_not_ge hhalf
      by_cases hwrap : y + β < 1
      · refine ⟨1, ?_⟩
        have hf : Int.fract (y + β) = y + β :=
          Int.fract_eq_self.mpr ⟨by linarith, hwrap⟩
        norm_num only [Fin.val_one, Nat.cast_one, one_mul]
        rw [hf]
        linarith
      · refine ⟨2, ?_⟩
        have hf := fract_sub_nat_eq (y + 2 * β) 1 (by norm_num; linarith)
          (by norm_num; linarith)
        norm_num
        rw [hf]
        norm_num
        linarith
  · by_cases hhalf : y < 1 / 2
    · refine ⟨0, ?_⟩
      simpa only [Fin.val_zero, Nat.cast_zero, zero_mul, add_zero, hy] using hhalf
    · have hyhigh : 1 / 2 ≤ y := le_of_not_gt hhalf
      have hf1 := fract_sub_nat_eq (y + β) 1 (by norm_num; linarith)
        (by norm_num; linarith)
      by_cases hz : y + β - 1 < 1 / 2
      · refine ⟨1, ?_⟩
        norm_num only [Fin.val_one, Nat.cast_one, one_mul]
        rw [hf1]
        simpa using hz
      · refine ⟨2, ?_⟩
        have hf2 := fract_sub_nat_eq (y + 2 * β) 2 (by norm_num; linarith)
          (by norm_num; linarith)
        norm_num
        rw [hf2]
        norm_num
        linarith

theorem phase_shift (n j : ℕ) :
    Int.fract (Int.fract ((n : ℝ) * slope) + (j : ℝ) * beta) =
      Int.fract (((n + j : ℕ) : ℝ) * slope) := by
  rw [Int.fract_fract_add]
  have he : (n : ℝ) * slope + (j : ℝ) * beta =
      ((n + j : ℕ) : ℝ) * slope - (j : ℝ) := by
    unfold beta
    push_cast
    ring
  rw [he, Int.fract_sub_natCast]

theorem high_phase_count_lower : HighPhaseCountLower := by
  classical
  intro r
  have hb : 1 / 2 < beta ∧ beta < 2 / 3 := by
    unfold beta
    have h := slope_bounds
    rcases h with ⟨hl, hu⟩
    constructor <;> linarith
  have exists_high : ∀ q : Fin (r / 3),
      ∃ t : {t : Fin r // (1 / 2 : ℝ) ≤ Int.fract ((t.val : ℝ) * slope)},
        t.val.val / 3 = q.val := by
    intro q
    obtain ⟨j, hj⟩ := (triple_rotation_high_low beta
      (Int.fract (((3 * q.val : ℕ) : ℝ) * slope)) hb.1 hb.2
      (Int.fract_nonneg _) (Int.fract_lt_one _)).1
    rw [phase_shift] at hj
    have hbound : 3 * (r / 3) ≤ r := by omega
    have ht : 3 * q.val + j.val < r := by omega
    refine ⟨⟨⟨3 * q.val + j.val, ht⟩, hj⟩, ?_⟩
    dsimp
    omega
  let f : Fin (r / 3) → {t : Fin r // (1 / 2 : ℝ) ≤ Int.fract ((t.val : ℝ) * slope)} :=
    fun q => Classical.choose (exists_high q)
  have hf : Function.Injective f := by
    intro q q' h
    have hq := Classical.choose_spec (exists_high q)
    have hq' := Classical.choose_spec (exists_high q')
    change (f q).val.val / 3 = q.val at hq
    change (f q').val.val / 3 = q'.val at hq'
    apply Fin.ext
    rw [← hq, ← hq', h]
  have hc := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_fin, highPhaseCount] using hc

theorem large_defects_unbounded : LargeDefectsUnbounded := by
  intro R
  have hb : 1 / 2 < beta ∧ beta < 2 / 3 := by
    unfold beta
    have h := slope_bounds
    rcases h with ⟨hl, hu⟩
    constructor <;> linarith
  obtain ⟨j, hj⟩ := (triple_rotation_high_low beta
    (Int.fract (((R + 1 : ℕ) : ℝ) * slope)) hb.1 hb.2
    (Int.fract_nonneg _) (Int.fract_lt_one _)).2
  rw [phase_shift] at hj
  let r := R + 1 + j.val
  have hr : R < r := by dsimp [r]; omega
  have hni := ExternalFiniteBridgeArithmetic.source_slope_nonintegral r (by omega)
  have hnz : Int.fract ((r : ℝ) * slope) ≠ 0 := by
    intro hzero
    obtain ⟨z, hz⟩ := Int.fract_eq_zero_iff.mp hzero
    exact hni ⟨z, hz.symm⟩
  refine ⟨r, hr, ?_⟩
  change 1 / 2 ≤ (Int.ceil ((r : ℝ) * slope) : ℝ) - (r : ℝ) * slope
  rw [Int.ceil_sub_self_eq hnz]
  change Int.fract ((r : ℝ) * slope) < 1 / 2 at hj
  linarith

end ExternalM4UnrestrictedRotation
