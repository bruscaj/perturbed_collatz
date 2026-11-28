import PressureAnalyticExpectedTypes
import BridgeArithmetic
import PositiveCeilReturns
import Mathlib.Topology.Order.DenselyOrdered

/-! Positive orbit density for the actual, fixed logarithmic slope. -/
namespace ExternalBridgePressureAnalyticRotation
open ExternalFiniteBridgeDraft ExternalBridgePressureDraft
open ExternalBridgePressureWordDraft ExternalBridgePressureAnalyticDraft

/-- A small positive real representative of a positive iterate of the actual rotation. -/
theorem small_positive_return (eps : ℝ) (heps : 0 < eps) :
    ∃ r : ℕ, 2 ≤ r ∧ ∃ B : ℤ, ∃ δ : ℝ,
      0 < δ ∧ δ < eps ∧ (r : ℝ) * slope = δ - B := by
  obtain ⟨r, hr, hpos, hsmall⟩ :=
    ExternalO3PositiveCeilReturns.exists_positive_ceil_gap (-slope)
      ExternalFiniteBridgeArithmetic.source_slope_facts.2.2.neg eps heps
  refine ⟨r, hr, ⌈(r : ℝ) * (-slope)⌉,
    (⌈(r : ℝ) * (-slope)⌉ : ℝ) - (r : ℝ) * (-slope), hpos, hsmall, ?_⟩
  ring

theorem positive_orbit_interior (x y : ℝ) (hx : ActualPhase x)
    (hy : 0 < y ∧ y < 1) (eps : ℝ) (heps : 0 < eps) :
    ∃ m : ℕ, 1 ≤ m ∧ |phaseShift x m - y| < eps := by
  obtain ⟨r, hr, B, δ, hδ, hδsmall, hreturn⟩ :=
    small_positive_return (min eps (min y 1)) (lt_min heps (lt_min hy.1 zero_lt_one))
  have hδε : δ < eps := lt_of_lt_of_le hδsmall (min_le_left _ _)
  have hδy : δ < y := lt_of_lt_of_le hδsmall (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδone : δ < 1 := lt_of_lt_of_le hδsmall (le_trans (min_le_right _ _) (min_le_right _ _))
  let A : ℝ := y - x + 2
  have hA : 1 < A := by dsimp [A]; linarith [hx.2]
  let j : ℕ := ⌊A / δ⌋₊
  have hjlo : (j : ℝ) * δ ≤ A := by
    have := Nat.floor_le (show 0 ≤ A / δ by positivity)
    exact (le_div_iff₀ hδ).mp this
  have hjhi : A < ((j : ℝ) + 1) * δ := by
    exact (div_lt_iff₀ hδ).mp (Nat.lt_floor_add_one (A / δ))
  have hj : 1 ≤ j := by
    by_contra h
    have : j = 0 := by omega
    rw [this] at hjhi
    norm_num at hjhi
    linarith
  have hphase : phaseShift x (j*r) = y - (A - (j : ℝ)*δ) := by
    have hmod : x + ((j*r : ℕ) : ℝ)*slope =
        (y - (A - (j : ℝ)*δ)) + 2 - ((j : ℤ)*B : ℤ) := by
      push_cast
      dsimp [A]
      nlinarith [hreturn]
    change Int.fract (x + ((j*r : ℕ) : ℝ)*slope) = _
    rw [hmod, Int.fract_sub_intCast]
    rw [show (y - (A - (j : ℝ)*δ)) + 2 =
      (y - (A - (j : ℝ)*δ)) + (2 : ℤ) by norm_num]
    rw [Int.fract_add_intCast, Int.fract_eq_self.mpr]
    constructor <;> linarith
  refine ⟨j*r, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩
  rw [hphase, abs_of_nonpos (by linarith : y - (A - (j : ℝ)*δ) - y ≤ 0)]
  linarith

/-- Frozen A14, including approximation to both closed-interval endpoints. -/
theorem positive_rotation_orbit_dense : PositiveRotationOrbitDense := by
  intro x y hx hy eps heps
  have hycl : y ∈ closure (Set.Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact hy
  obtain ⟨z, hz, hzy⟩ := Metric.mem_closure_iff.mp hycl (eps/2) (by positivity)
  obtain ⟨m, hm, hzm⟩ := positive_orbit_interior x z hx hz (eps/2) (by positivity)
  refine ⟨m, hm, ?_⟩
  have hzabs : |z-y| < eps/2 := by simpa [Real.dist_eq, abs_sub_comm] using hzy
  calc
    |phaseShift x m-y| ≤ |phaseShift x m-z| + |z-y| := abs_sub_le _ _ _
    _ < eps := by linarith

end ExternalBridgePressureAnalyticRotation
