import RateExpectedTypes
import GeneralWeights
import Mathlib.Analysis.SpecificLimits.Normed

/-! Exact geometric moments and the finite history normalization. -/
namespace ExternalO3RateMoments
open ExternalO3RateDraft ExternalO3GeneralDraft ExternalO3GeneralWeights
open scoped BigOperators

theorem history_weight_product (h : Depth) (r : History h) :
    historyWeight h r = productWeight (h.val + 1) r := by
  simp [historyWeight, productWeight, atom, Nat.cast_add, Nat.cast_one]

theorem history_weight_law : HistoryWeightLaw := by
  intro h
  have he : historyWeight h = productWeight (h.val + 1) := by
    funext r
    exact history_weight_product h r
  rw [he]
  exact ⟨productWeight_summable _, productWeight_tsum _⟩

theorem atom_hasSum : HasSum atom 1 := by
  simpa only [atom_tsum] using atom_summable.hasSum

theorem atom_length_hasSum :
    HasSum (fun a : ℕ => atom a * ((a : ℝ) + 1)) 2 := by
  have h1 := hasSum_coe_mul_geometric_of_norm_lt_one
    (r := (1 / 2 : ℝ)) (by norm_num)
  convert (h1.add hasSum_geometric_two).mul_left (1 / 2 : ℝ) using 1
  · funext a
    rw [atom_geometric]
    ring
  · norm_num

theorem atom_length_sq_hasSum :
    HasSum (fun a : ℕ => atom a * ((a : ℝ) + 1) ^ 2) 6 := by
  have h1 := hasSum_coe_mul_geometric_of_norm_lt_one
    (r := (1 / 2 : ℝ)) (by norm_num)
  have h2 := hasSum_sq_mul_geometric_of_norm_lt_one
    (r := (1 / 2 : ℝ)) (by norm_num)
  convert ((h2.add (h1.mul_left 2)).add hasSum_geometric_two).mul_left (1 / 2 : ℝ) using 1
  · funext a
    rw [atom_geometric]
    ring
  · norm_num

theorem atom_center_hasSum :
    HasSum (fun a : ℕ => atom a * ((a : ℝ) - 1)) 0 := by
  convert atom_length_hasSum.sub (atom_hasSum.mul_left 2) using 1
  · funext a
    ring
  · norm_num

theorem atom_center_sq_hasSum :
    HasSum (fun a : ℕ => atom a * ((a : ℝ) - 1) ^ 2) 2 := by
  convert (atom_length_sq_hasSum.sub (atom_length_hasSum.mul_left 4)).add
    (atom_hasSum.mul_left 4) using 1
  · funext a
    ring
  · norm_num

end ExternalO3RateMoments
