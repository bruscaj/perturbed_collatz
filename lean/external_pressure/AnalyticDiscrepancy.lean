import AnalyticCircleGrid
import AnalyticAveraging

/-! Actual irrational rotation discrepancy, uniformly over starts and half-open intervals. -/
namespace ExternalBridgePressureAnalyticDiscrepancy
open ExternalFiniteBridgeDraft ExternalBridgePressureDraft
open ExternalBridgePressureWordDraft ExternalBridgePressureAnalyticDraft
open ExternalBridgePressureAnalyticRotation ExternalBridgePressureAnalyticRotationGrid
open ExternalBridgePressureAnalyticCircleGrid ExternalBridgePressureAnalyticAveraging
open scoped BigOperators
noncomputable section
local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem phase_return_grid (x : ℝ) (t j r : ℕ) (B : ℤ) (δ : ℝ)
    (hreturn : (r : ℝ)*slope = δ-B) :
    phaseShift x (t+j*r) = Int.fract (phaseShift x t+(j : ℝ)*δ) := by
  change Int.fract (x+((t+j*r : ℕ) : ℝ)*slope) =
    Int.fract (Int.fract (x+(t : ℝ)*slope)+(j : ℝ)*δ)
  rw [Int.fract_fract_add]
  have hid : x+((t+j*r : ℕ) : ℝ)*slope =
      (x+(t : ℝ)*slope+(j : ℝ)*δ)-((j : ℤ)*B : ℤ) := by
    push_cast
    nlinarith [hreturn]
  rw [hid, Int.fract_sub_intCast]

theorem shifted_count_sum (x a b : ℝ) (n : ℕ) :
    (shiftedIntervalCount x a b n : ℝ) =
      ∑ t ∈ Finset.range n, chi a b (phaseShift x t) := by
  unfold shiftedIntervalCount chi
  simp

/-- Frozen A02. The return/grid is fixed before choosing the averaging length. -/
theorem uniform_shifted_interval_discrepancy : UniformShiftedIntervalDiscrepancy := by
  intro eps heps
  obtain ⟨r, hr, B, δ, hδ, hsmall, hreturn⟩ := small_positive_return (eps/20) (by positivity)
  let T : ℕ := ⌈1/δ⌉₊
  have hT : 0 < T := Nat.ceil_pos.mpr (by positivity)
  have hTp : (0 : ℝ) < T := by exact_mod_cast hT
  have hcover : 1 ≤ (T : ℝ)*δ := by
    exact (div_le_iff₀ hδ).mp (Nat.le_ceil (1/δ))
  have hover : (T : ℝ)*δ < 1+δ := by
    have hc := Nat.ceil_lt_add_one (show 0 ≤ 1/δ by positivity)
    have := (mul_lt_mul_of_pos_right hc hδ)
    dsimp [T]
    field_simp at this
    nlinarith
  have hinside (j : ℕ) (hj : j < T) : (j : ℝ)*δ < 1 :=
    (lt_div_iff₀ hδ).mp (Nat.lt_ceil.mp hj)
  have hmesh : 1/(T : ℝ) ≤ δ := (div_le_iff₀ hTp).mpr (by nlinarith [hcover])
  let N : ℕ := ⌈4*((r*T : ℕ) : ℝ)/eps⌉₊ + 1
  refine ⟨N, by omega, ?_⟩
  intro n hn x a b hx ha hab hb
  have hn0 : 0 < n := by dsimp [N] at hn; omega
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn0
  have hlong : 4*((r*T : ℕ) : ℝ)/eps < (n : ℝ) := by
    have hc := Nat.le_ceil (4*((r*T : ℕ) : ℝ)/eps)
    have hcn : (⌈4*((r*T : ℕ) : ℝ)/eps⌉₊ : ℝ)+1 ≤ n := by
      simpa only [N, Nat.cast_add, Nat.cast_one] using (Nat.cast_le.mpr hn : (N : ℝ) ≤ (n : ℝ))
    linarith
  have hboundary : ((r*T : ℕ) : ℝ)/(n : ℝ) < eps/4 := by
    have hm := (div_lt_iff₀ heps).mp hlong
    apply (div_lt_iff₀ hnp).mpr
    nlinarith
  let f : ℕ → ℝ := fun t => chi a b (phaseShift x t)
  have hf (t : ℕ) : 0 ≤ f t ∧ f t ≤ 1 := by dsimp [f, chi]; split_ifs <;> norm_num
  let g : ℕ → ℝ := fun t => circleGridAverage (phaseShift x t) δ T a b
  have hg (t : ℕ) (_ht : t < n) : |g t-(b-a)| ≤ 6*δ := by
    have hphase : 0 ≤ phaseShift x t ∧ phaseShift x t < 1 :=
      ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
    have he := translated_grid_error δ hδ T hT hcover hover hinside (phaseShift x t) a b hphase ha hab hb
    have hid : 4/(T : ℝ) = 4*(1/(T : ℝ)) := by ring
    dsimp [g]
    rw [hid] at he
    linarith
  have havg := bounded_average_error g n hn0 (b-a) (6*δ) hg
  have hdouble : (∑ t ∈ Finset.range n, g t)/(n : ℝ) =
      ((∑ j ∈ Finset.range T, ∑ t ∈ Finset.range n, f (t+j*r))/(T : ℝ))/(n : ℝ) := by
    dsimp [g, circleGridAverage]
    rw [← Finset.sum_div, Finset.sum_comm]
    congr 2
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro t _
    dsimp [f]
    rw [phase_return_grid x t j r B δ hreturn]
  have hshift := averaged_shift_error f hf n r T hT
  have hdiff : |(∑ t ∈ Finset.range n, g t)/(n : ℝ) -
      (shiftedIntervalCount x a b n : ℝ)/(n : ℝ)| ≤ ((r*T : ℕ) : ℝ)/(n : ℝ) := by
    rw [hdouble, shifted_count_sum, ← sub_div, abs_div, abs_of_pos hnp]
    exact (div_le_div_iff_of_pos_right hnp).mpr hshift
  rw [← abs_sub_comm] at hdiff
  calc
    |(shiftedIntervalCount x a b n : ℝ)/(n : ℝ)-(b-a)| ≤
      |(shiftedIntervalCount x a b n : ℝ)/(n : ℝ)-(∑ t ∈ Finset.range n, g t)/(n : ℝ)| +
      |(∑ t ∈ Finset.range n, g t)/(n : ℝ)-(b-a)| := abs_sub_le _ _ _
    _ < eps := by linarith

/-- Frozen A01, obtained by choosing the actual starting phase zero in A02. -/
theorem uniform_interval_discrepancy : UniformIntervalDiscrepancy := by
  intro eps heps
  obtain ⟨N, hN, h⟩ := uniform_shifted_interval_discrepancy eps heps
  refine ⟨N,hN,?_⟩
  intro n hn a b ha hab hb
  have h0 := h n hn 0 a b ⟨le_rfl,zero_lt_one⟩ ha hab hb
  simpa [intervalCount,shiftedIntervalCount,phaseShift,phaseTick] using h0

end
end ExternalBridgePressureAnalyticDiscrepancy
