import AnalyticDiscrepancy
import WordPhaseUp

/-! Exact cap crossings, including the t=0 and auxiliary x=1 conventions. -/
namespace ExternalBridgePressureAnalyticCapDiscrepancy
open ExternalFiniteBridgeDraft ExternalBridgePressureDraft
open ExternalBridgePressureWordDraft ExternalBridgePressureAnalyticDraft
open ExternalBridgePressureWordPhaseUp ExternalBridgePressureAnalyticDiscrepancy
noncomputable section
local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem cap_difference_interval_count (x y : ℝ) (n : ℕ) (hxy : OrderedPhases x y) :
    Dcount x y n = intervalCount (1-y) (1-x) n := by
  let s := (Finset.range n).filter (fun t : ℕ =>
    1-y ≤ Int.fract ((t : ℝ)*slope) ∧ Int.fract ((t : ℝ)*slope) < 1-x)
  have hcross := (cap_difference_geometry x y n hxy).2.2
  let e : CapDifference x y n ≃ ↥s := {
    toFun := fun t => ⟨t.val.val, by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_range.mpr t.val.isLt, (hcross t.val.val).mp t.property⟩⟩
    invFun := fun t => ⟨⟨t.val, Finset.mem_range.mp (Finset.mem_filter.mp t.property).1⟩,
      (hcross t.val).mpr (Finset.mem_filter.mp t.property).2⟩
    left_inv := fun t => by rfl
    right_inv := fun t => by rfl }
  calc
    Dcount x y n = Nat.card ↥s := Nat.card_congr e
    _ = s.card := Nat.card_eq_finsetCard s
    _ = intervalCount (1-y) (1-x) n := rfl

/-- Frozen A03, with an exact cardinality identity rather than a tail estimate. -/
theorem cap_difference_discrepancy : CapDifferenceDiscrepancy := by
  intro eps heps
  obtain ⟨N,hN,h⟩ := uniform_interval_discrepancy eps heps
  refine ⟨N,hN,?_⟩
  intro n hn x y hxy
  rw [cap_difference_interval_count x y n hxy]
  have hinterval := h n hn (1-y) (1-x) (by linarith [hxy.2.1.2])
    (by linarith [hxy.2.2]) (by linarith [hxy.1.1])
  have hid : (1-x)-(1-y) = y-x := by ring
  rwa [hid] at hinterval

end
end ExternalBridgePressureAnalyticCapDiscrepancy
