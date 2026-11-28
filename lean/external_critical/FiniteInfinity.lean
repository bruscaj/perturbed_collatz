import StationaryEvents

/-! The no-upward-cylinder premise and stationarity exclude a finite/infinite
interface. The limiting law may still be a mixture of the two pure sectors. -/
namespace ExternalCriticalFiniteInfinity
open ExternalCriticalSpaceDraft ExternalCriticalStationaryEvents ExternalCriticalSpaceArithmetic
open MeasureTheory Filter
open scoped Topology
noncomputable section

def finiteAt (t : ℤ) : Set Config := {w | ∃ a : ℕ, w.2 t = OnePoint.some a}

theorem finite_at_measurable (t : ℤ) : MeasurableSet (finiteAt t) := finite_coordinate_measurable t

theorem finite_forward_ae (mu : ProbabilityMeasure Config)
    (hz : ∀ a : ℕ, (mu : Measure Config) (forbiddenUpwardCylinder a) = 0) :
    finiteAt 0 ≤ᵐ[(mu : Measure Config)] finiteAt 1 := by
  have hbad (a : ℕ) : ∀ᵐ w ∂(mu : Measure Config), w ∉ forbiddenUpwardCylinder a := by
    rw [ae_iff]
    simpa only [not_not,Set.ofPred_mem_eq] using hz a
  filter_upwards [ae_all_iff.mpr hbad] with w hw
  rintro ⟨a, ha⟩
  have hnext : w.2 1 ∈ finiteHeightSet (a+1) := by
    by_contra h
    exact hw a ⟨ha,h⟩
  obtain ⟨b, _, hb⟩ := hnext
  exact ⟨b,hb⟩

theorem finite_adjacent_ae (mu : ProbabilityMeasure Config) (hmu : IsStationary (mu : Measure Config))
    (hz : ∀ a : ℕ, (mu : Measure Config) (forbiddenUpwardCylinder a) = 0) :
    ∀ᵐ w ∂(mu : Measure Config), (w ∈ finiteAt 0 ↔ w ∈ finiteAt 1) := by
  have he : (mu : Measure Config) (finiteAt 1) = (mu : Measure Config) (finiteAt 0) := by
    have h := stationary_preimage (mu : Measure Config) hmu 1 (finiteAt 0) (finite_at_measurable 0)
    simpa only [finiteAt,Set.preimage_ofPred_eq,timeShift,zero_add] using h
  have hh := ae_eq_of_ae_subset_of_measure_ge (finite_forward_ae mu hz) he.le
    (finite_at_measurable 0).nullMeasurableSet (measure_ne_top _ _)
  exact hh.mono fun _ h => Iff.of_eq h

theorem finite_all_adjacent_ae (mu : ProbabilityMeasure Config) (hmu : IsStationary (mu : Measure Config))
    (hz : ∀ a : ℕ, (mu : Measure Config) (forbiddenUpwardCylinder a) = 0) :
    ∀ᵐ w ∂(mu : Measure Config), ∀ t : ℤ, (w ∈ finiteAt t ↔ w ∈ finiteAt (t+1)) := by
  apply ae_all_iff.mpr
  intro t
  have hb : ∀ᵐ w ∂Measure.map (timeShift t) (mu : Measure Config),
      (w ∈ finiteAt 0 ↔ w ∈ finiteAt 1) := by
    rw [stationary_map_int (mu : Measure Config) hmu t]
    exact finite_adjacent_ae mu hmu hz
  have hc := ae_of_ae_map (time_shift_measurable t).aemeasurable hb
  filter_upwards [hc] with w hw
  change (∃ a : ℕ, w.2 (0+t) = OnePoint.some a) ↔
    (∃ a : ℕ, w.2 (1+t) = OnePoint.some a) at hw
  simpa only [zero_add,add_comm 1 t,finiteAt,Set.mem_ofPred_eq] using hw

theorem int_predicate_constant (P : ℤ → Prop) (hP : ∀ t, P t ↔ P (t+1)) (t : ℤ) :
    P t ↔ P 0 := by
  apply Int.induction_on (motive := fun t => P t ↔ P 0) t
  · rfl
  · intro k hk
    exact (hP (k : ℤ)).symm.trans hk
  · intro k hk
    have he : -(k : ℤ)-1+1 = -(k : ℤ) := by omega
    exact ((hP (-(k : ℤ)-1)).trans (by rw [he])).trans hk

theorem finite_infinity_exclusion : FiniteInfinityExclusion := by
  intro mu hmu hz
  apply (mem_ae_iff_prob_eq_one (all_finite_measurable.union all_infinite_measurable)).mp
  filter_upwards [finite_all_adjacent_ae mu hmu hz] with w hw
  by_cases hf : w ∈ finiteAt 0
  · left
    intro t
    exact (int_predicate_constant (fun t => w ∈ finiteAt t) hw t).mpr hf
  · right
    intro t
    by_contra hh
    obtain ⟨a,ha⟩ := OnePoint.ne_infty_iff_exists.mp hh
    exact hf ((int_predicate_constant (fun t => w ∈ finiteAt t) hw t).mp ⟨a,ha.symm⟩)

end
end ExternalCriticalFiniteInfinity
