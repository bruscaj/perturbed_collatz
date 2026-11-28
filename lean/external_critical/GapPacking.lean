import StationaryEvents

/-! A genuine disjoint tiling by consecutive low-return intervals around zero.
No recurrence, finite-height support or critical Gibbs property is assumed. -/
namespace ExternalCriticalGapPacking
open ExternalCriticalSpaceDraft ExternalCriticalSpaceArithmetic ExternalCriticalStationaryEvents
open MeasureTheory Filter
open scoped Topology ENNReal BigOperators
noncomputable section

abbrev GapIndex := Σ m : ℕ, Fin m
def gapTile (H : ℕ) (i : GapIndex) : Set Config := shiftedGap H i.1 i.2.val

theorem low_event_shift (H : ℕ) (t s : ℤ) (w : Config) :
    timeShift s w ∈ lowEvent H t ↔ w ∈ lowEvent H (t+s) := Iff.rfl

theorem tile_start (H m : ℕ) (k : Fin m) (w : Config) (hw : w ∈ gapTile H ⟨m,k⟩) :
    w ∈ lowEvent H (-(k.val : ℤ)) := by
  have h : timeShift (-(k.val : ℤ)) w ∈ successiveGap H m := hw
  simpa only [low_event_shift,zero_add] using h.2.1

theorem tile_end (H m : ℕ) (k : Fin m) (w : Config) (hw : w ∈ gapTile H ⟨m,k⟩) :
    w ∈ lowEvent H ((m : ℤ)-(k.val : ℤ)) := by
  have h : timeShift (-(k.val : ℤ)) w ∈ successiveGap H m := hw
  simpa only [low_event_shift,sub_eq_add_neg] using h.2.2.1

theorem tile_no_low (H m : ℕ) (k : Fin m) (w : Config) (hw : w ∈ gapTile H ⟨m,k⟩)
    (u : ℕ) (hu : 0 < u) (hum : u < m) :
    w ∉ lowEvent H ((u : ℤ)-(k.val : ℤ)) := by
  have h : timeShift (-(k.val : ℤ)) w ∈ successiveGap H m := hw
  simpa only [low_event_shift,sub_eq_add_neg] using h.2.2.2 u hu hum

theorem gap_tile_unique (H : ℕ) (i j : GapIndex) (w : Config)
    (hi : w ∈ gapTile H i) (hj : w ∈ gapTile H j) : i = j := by
  rcases i with ⟨m,k⟩
  rcases j with ⟨n,l⟩
  have hkl : k.val = l.val := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hno := tile_no_low H n l w hj (l.val-k.val) (by omega) (by omega)
      have he : (((l.val-k.val : ℕ) : ℤ)-(l.val : ℤ)) = -(k.val : ℤ) := by omega
      rw [he] at hno
      exact hno (tile_start H m k w hi)
    · have hno := tile_no_low H m k w hi (k.val-l.val) (by omega) (by omega)
      have he : (((k.val-l.val : ℕ) : ℤ)-(k.val : ℤ)) = -(l.val : ℤ) := by omega
      rw [he] at hno
      exact hno (tile_start H n l w hj)
  have hmn : m = n := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hno := tile_no_low H n l w hj m (by omega) hlt
      have he : (m : ℤ)-(l.val : ℤ) = (m : ℤ)-(k.val : ℤ) := by omega
      rw [he] at hno
      exact hno (tile_end H m k w hi)
    · have hno := tile_no_low H m k w hi n (by omega) hgt
      have he : (n : ℤ)-(k.val : ℤ) = (n : ℤ)-(l.val : ℤ) := by omega
      rw [he] at hno
      exact hno (tile_end H n l w hj)
  cases hmn
  have hk : k = l := Fin.ext hkl
  subst l
  rfl

theorem gap_tiles_disjoint (H : ℕ) : Pairwise (fun i j : GapIndex => Disjoint (gapTile H i) (gapTile H j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro w hi hj
  exact hij (gap_tile_unique H i j w hi hj)

theorem gap_tiles_measurable (H : ℕ) (i : GapIndex) : MeasurableSet (gapTile H i) :=
  shifted_gap_measurable H i.1 i.2.val

theorem gap_tile_measure (mu : ProbabilityMeasure Config) (hmu : IsStationary (mu : Measure Config))
    (H : ℕ) (i : GapIndex) :
    (mu : Measure Config) (gapTile H i) = (mu : Measure Config) (successiveGap H i.1) :=
  stationary_preimage (mu : Measure Config) hmu _ _ (successive_gap_measurable H i.1)

theorem gap_mass_ennreal_bound (mu : ProbabilityMeasure Config) (hmu : IsStationary (mu : Measure Config))
    (H : ℕ) : (∑' m : ℕ, (m : ℝ≥0∞)*(mu : Measure Config) (successiveGap H m)) ≤ 1 := by
  have ht : (∑' i : GapIndex, (mu : Measure Config) (gapTile H i)) ≤ 1 := by
    rw [← measure_iUnion (gap_tiles_disjoint H) (gap_tiles_measurable H)]
    exact (measure_mono (Set.subset_univ _)).trans_eq (measure_univ : (mu : Measure Config) Set.univ = 1)
  have he : (∑' i : GapIndex, (mu : Measure Config) (gapTile H i)) =
      ∑' m : ℕ, (m : ℝ≥0∞)*(mu : Measure Config) (successiveGap H m) := by
    rw [ENNReal.tsum_sigma']
    simp_rw [gap_tile_measure mu hmu H]
    simp only [tsum_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rwa [he] at ht

theorem gap_packing : GapPacking := by
  intro mu hmu H
  have hbound := gap_mass_ennreal_bound mu hmu H
  have hsum : (∑' m : ℕ, (m : ℝ≥0∞)*(mu : Measure Config) (successiveGap H m)) ≠ ∞ :=
    ne_of_lt (hbound.trans_lt (by simp))
  have hf (m : ℕ) : (m : ℝ≥0∞)*(mu : Measure Config) (successiveGap H m) ≠ ∞ := by finiteness
  constructor
  · simpa only [ENNReal.toReal_mul,ENNReal.toReal_natCast] using ENNReal.summable_toReal hsum
  · have ht := ENNReal.toReal_mono ENNReal.one_ne_top hbound
    simpa only [ENNReal.tsum_toReal_eq hf,ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_one] using ht

end
end ExternalCriticalGapPacking
