import GapPacking
import Mathlib.Data.Nat.Find

/-! The last low time before L reduces the actual long-excursion event to a
finite union of translated consecutive gaps. No tail estimate is assumed. -/
namespace ExternalCriticalExcursionMoment
open ExternalCriticalSpaceDraft ExternalCriticalGapPacking ExternalCriticalStationaryEvents
open ExternalCriticalSpaceArithmetic MeasureTheory Filter
open scoped Topology ENNReal BigOperators
noncomputable section
local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem gap_zero_measure (mu : ProbabilityMeasure Config) (H : ℕ) :
    (mu : Measure Config) (successiveGap H 0) = 0 := by
  have he : successiveGap H 0 = ∅ := by
    ext w
    simp [successiveGap]
  rw [he,measure_empty]

theorem gap_unweighted_summable (mu : ProbabilityMeasure Config)
    (hmu : IsStationary (mu : Measure Config)) (H : ℕ) :
    Summable (fun m : ℕ => ((mu : Measure Config) (successiveGap H m)).toReal) := by
  apply Summable.of_nonneg_of_le (fun _ => ENNReal.toReal_nonneg) _ (gap_packing mu hmu H).1
  intro m
  cases m with
  | zero => simp [gap_zero_measure]
  | succ k =>
    have hn : (1 : ℝ) ≤ ((k+1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
    have hg : 0 ≤ ((mu : Measure Config) (successiveGap H (k+1))).toReal := ENNReal.toReal_nonneg
    nlinarith

theorem shifted_weighted_gap_summable (mu : ProbabilityMeasure Config)
    (hmu : IsStationary (mu : Measure Config)) (H k : ℕ) :
    Summable (fun n : ℕ => (n : ℝ)*((mu : Measure Config) (successiveGap H (n-k))).toReal) := by
  apply (summable_nat_add_iff k).mp
  have h1 := (gap_packing mu hmu H).1
  have h2 := (gap_unweighted_summable mu hmu H).mul_left (k : ℝ)
  simpa only [Nat.add_sub_cancel,Nat.cast_add,add_mul] using h1.add h2

theorem excursion_subset_gap_union (H L n : ℕ) (hL : 0 < L) (hn : L ≤ n) :
    longExcursion H L n ⊆ ⋃ k : Fin L,
      (timeShift (k.val : ℤ)) ⁻¹' successiveGap H (n-k.val) := by
  intro w hw
  rcases hw with ⟨hw0,hwn,havoid⟩
  let P : ℕ → Prop := fun k => w ∈ lowEvent H (k : ℤ)
  let k := Nat.findGreatest P (L-1)
  have hkb : k ≤ L-1 := Nat.findGreatest_le _
  have hkl : k < L := by omega
  have hkw : w ∈ lowEvent H (k : ℤ) :=
    Nat.findGreatest_spec (P := P) (m := 0) (n := L-1) (by omega) hw0
  apply Set.mem_iUnion.mpr
  refine ⟨⟨k,hkl⟩, ?_⟩
  change 0 < n-k ∧ timeShift (k : ℤ) w ∈ lowEvent H 0 ∧
    timeShift (k : ℤ) w ∈ lowEvent H ((n-k : ℕ) : ℤ) ∧
      ∀ u : ℕ, 0 < u → u < n-k → timeShift (k : ℤ) w ∉ lowEvent H (u : ℤ)
  refine ⟨by omega, ?_, ?_, ?_⟩
  · rw [low_event_shift,zero_add]
    exact hkw
  · rw [low_event_shift]
    have he : ((n-k : ℕ) : ℤ)+(k : ℤ) = (n : ℤ) := by omega
    rwa [he]
  · intro u hu hun hlow
    rw [low_event_shift] at hlow
    have he : (u : ℤ)+(k : ℤ) = ((u+k : ℕ) : ℤ) := by omega
    rw [he] at hlow
    by_cases hbig : L ≤ u+k
    · exact havoid (u+k) hbig (by omega) hlow
    · have hnot : ¬P (u+k) := Nat.findGreatest_is_greatest (P := P)
        (show Nat.findGreatest P (L-1) < u+k by change k < u+k; omega) (by omega)
      exact hnot hlow

theorem excursion_probability_bound (mu : ProbabilityMeasure Config)
    (hmu : IsStationary (mu : Measure Config)) (H L n : ℕ) (hL : 0 < L) (hn : L ≤ n) :
    ((mu : Measure Config) (longExcursion H L n)).toReal ≤
      ∑ k : Fin L, ((mu : Measure Config) (successiveGap H (n-k.val))).toReal := by
  have h1 := measureReal_mono (μ := (mu : Measure Config)) (excursion_subset_gap_union H L n hL hn)
  have h2 := measureReal_iUnion_fintype_le (μ := (mu : Measure Config))
    (fun k : Fin L => (timeShift (k.val : ℤ)) ⁻¹' successiveGap H (n-k.val))
  have he (k : Fin L) : (mu : Measure Config).real
      ((timeShift (k.val : ℤ)) ⁻¹' successiveGap H (n-k.val)) =
      ((mu : Measure Config) (successiveGap H (n-k.val))).toReal := by
    rw [measureReal_def,stationary_preimage (mu : Measure Config) hmu _ _
      (successive_gap_measurable H (n-k.val))]
  exact h1.trans (by simpa only [he] using h2)

theorem excursion_first_moment : ExcursionFirstMoment := by
  intro mu hmu H L hL
  apply (summable_nat_add_iff L).mp
  have hsum : Summable (fun n : ℕ => ∑ k : Fin L,
      (n : ℝ)*((mu : Measure Config) (successiveGap H (n-k.val))).toReal) :=
    summable_sum (fun k _ => shifted_weighted_gap_summable mu hmu H k.val)
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg) _
    ((summable_nat_add_iff L).mpr hsum)
  intro n
  have h := mul_le_mul_of_nonneg_left
    (excursion_probability_bound mu hmu H L (n+L) hL (by omega)) (Nat.cast_nonneg (n+L) : (0 : ℝ) ≤ (n+L : ℕ))
  simpa only [Finset.mul_sum] using h

end
end ExternalCriticalExcursionMoment
