import SpaceTopology
import SpaceArithmetic

/-! All-integer stationarity transport and Borel cylinder foundations, using the
unchanged circle/OnePoint configuration space. -/
namespace ExternalCriticalStationaryEvents
open ExternalCriticalSpaceDraft ExternalCriticalSpaceTopology ExternalCriticalSpaceArithmetic
open MeasureTheory Filter
open scoped Topology BigOperators ENNReal
noncomputable section

theorem stationary_map_nat (mu : Measure Config) (hmu : IsStationary mu) (k : ℕ) :
    Measure.map (timeShift (k : ℤ)) mu = mu := by
  induction k with
  | zero =>
    have he : timeShift (0 : ℤ) = id := funext time_shift_zero
    rw [Nat.cast_zero, he, Measure.map_id]
  | succ k ih =>
    have he : timeShift ((k+1 : ℕ) : ℤ) = timeShift 1 ∘ timeShift (k : ℤ) := by
      funext w
      rw [Function.comp_apply, time_shift_add]
      congr 1
      omega
    rw [he, ← Measure.map_map (time_shift_measurable 1) (time_shift_measurable (k : ℤ)), ih]
    exact hmu

theorem stationary_map_neg_nat (mu : Measure Config) (hmu : IsStationary mu) (k : ℕ) :
    Measure.map (timeShift (-(k : ℤ))) mu = mu := by
  have he : timeShift (-(k : ℤ)) ∘ timeShift (k : ℤ) = id := by
    funext w
    rw [Function.comp_apply,time_shift_add,neg_add_cancel,time_shift_zero]
    rfl
  have hh := congrArg (Measure.map (timeShift (-(k : ℤ)))) (stationary_map_nat mu hmu k)
  rw [Measure.map_map (time_shift_measurable _) (time_shift_measurable _),he,Measure.map_id] at hh
  exact hh.symm

theorem stationary_map_int (mu : Measure Config) (hmu : IsStationary mu) (s : ℤ) :
    Measure.map (timeShift s) mu = mu := by
  cases s with
  | ofNat k => exact stationary_map_nat mu hmu k
  | negSucc k => exact stationary_map_neg_nat mu hmu (k+1)

theorem stationary_preimage (mu : Measure Config) (hmu : IsStationary mu)
    (s : ℤ) (E : Set Config) (hE : MeasurableSet E) :
    mu ((timeShift s) ⁻¹' E) = mu E := by
  rw [← Measure.map_apply (time_shift_measurable s) hE,stationary_map_int mu hmu s]

theorem measurable_forall_pred {α ι : Type*} [MeasurableSpace α] [Countable ι]
    (P : ι → α → Prop) (hP : ∀ i, MeasurableSet {x | P i x}) :
    MeasurableSet {x | ∀ i, P i x} := by
  apply (MeasurableSet.iInter hP).congr
  ext x
  exact Set.mem_iInter

theorem measurable_exists_pred {α ι : Type*} [MeasurableSpace α] [Countable ι]
    (P : ι → α → Prop) (hP : ∀ i, MeasurableSet {x | P i x}) :
    MeasurableSet {x | ∃ i, P i x} := by
  apply (MeasurableSet.iUnion hP).congr
  ext x
  exact Set.mem_iUnion

theorem finite_height_set_measurable (H : ℕ) : MeasurableSet (finiteHeightSet H) := by
  apply measurable_exists_pred
  intro a
  exact (MeasurableSet.const (a ≤ H)).inter (MeasurableSet.singleton (OnePoint.some a))

theorem coordinate_measurable (t : ℤ) : Measurable (fun w : Config => w.2 t) :=
  ((continuous_apply t).comp continuous_snd).measurable

theorem low_event_measurable (H : ℕ) (t : ℤ) : MeasurableSet (lowEvent H t) :=
  (finite_height_set_measurable H).preimage (coordinate_measurable t)

theorem finite_coordinate_measurable (t : ℤ) :
    MeasurableSet {w : Config | ∃ a : ℕ, w.2 t = OnePoint.some a} := by
  apply measurable_exists_pred
  intro a
  exact (MeasurableSet.singleton (OnePoint.some a)).preimage (coordinate_measurable t)

theorem all_finite_measurable : MeasurableSet allFinite :=
  measurable_forall_pred _ finite_coordinate_measurable

theorem all_infinite_measurable : MeasurableSet allInfinite :=
  measurable_forall_pred _ (fun t => (MeasurableSet.singleton OnePoint.infty).preimage (coordinate_measurable t))

theorem forbidden_upward_measurable (a : ℕ) : MeasurableSet (forbiddenUpwardCylinder a) :=
  ((MeasurableSet.singleton (OnePoint.some a)).preimage (coordinate_measurable 0)).inter
    (low_event_measurable (a+1) 1).compl

theorem successive_gap_measurable (H m : ℕ) : MeasurableSet (successiveGap H m) := by
  apply (MeasurableSet.const (0 < m)).inter
  apply (low_event_measurable H 0).inter
  apply (low_event_measurable H (m : ℤ)).inter
  apply measurable_forall_pred
  intro t
  exact (MeasurableSet.const (0 < t)).imp
    ((MeasurableSet.const (t < m)).imp (low_event_measurable H (t : ℤ)).compl)

theorem shifted_gap_measurable (H m k : ℕ) : MeasurableSet (shiftedGap H m k) :=
  (successive_gap_measurable H m).preimage (time_shift_measurable _)

theorem long_excursion_measurable (H L n : ℕ) : MeasurableSet (longExcursion H L n) := by
  apply (low_event_measurable H 0).inter
  apply (low_event_measurable H (n : ℤ)).inter
  apply measurable_forall_pred
  intro t
  exact (MeasurableSet.const (L ≤ t)).imp
    ((MeasurableSet.const (t < n)).imp (low_event_measurable H (t : ℤ)).compl)

end
end ExternalCriticalStationaryEvents
