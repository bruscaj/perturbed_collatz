import ExpectedTypes
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
Unconditional summability and normalization of the frozen h=1 edge weights.
This module assumes no seed-density theorem and proves no literal density limit.
-/
namespace ExternalO3PopulationWeights
open ExternalO3Spec
open scoped BigOperators

abbrev Edge := Sum ℕ (ℕ × ℕ)

noncomputable def weight : Edge → ℝ
  | .inl a => (2 : ℝ) ^ (-(a + 2 : ℤ))
  | .inr (a, b) => (2 : ℝ) ^ (-(a + 2 : ℤ) - (b + 1 : ℤ))

def Bad (φ : Correction) : Edge → Prop
  | .inl a => 0 ≤ ascendingGain φ (a + 2)
  | .inr (a, b) => 0 ≤ exitGain φ (a + 2) (b + 1)

noncomputable def selectedWeight (φ : Correction) (e : Edge) : ℝ := by
  classical
  exact if Bad φ e then weight e else 0

noncomputable def landingWeight (b : ℕ) : ℝ := (2 : ℝ) ^ (-(b + 1 : ℤ))

theorem weight_nonneg (e : Edge) : 0 ≤ weight e := by
  cases e with
  | inl a => exact le_of_lt (zpow_pos (by norm_num) _)
  | inr p => exact le_of_lt (zpow_pos (by norm_num) _)

theorem neg_power_geometric (a c : ℕ) :
    (2 : ℝ) ^ (-(a + c : ℤ)) =
      (2 : ℝ) ^ (-(c : ℤ)) * ((1 : ℝ) / 2) ^ a := by
  rw [neg_add, zpow_add₀ (by norm_num)]
  simp [zpow_neg, one_div, inv_pow, mul_comm]

theorem weight_inl_geometric (a : ℕ) :
    weight (.inl a) = ((1 : ℝ) / 4) * ((1 : ℝ) / 2) ^ a := by
  change (2 : ℝ) ^ (-(a + 2 : ℤ)) = _
  have h := neg_power_geometric a 2
  norm_num at h
  convert h using 1
  congr 1
  omega

theorem landingWeight_geometric (b : ℕ) :
    landingWeight b = ((1 : ℝ) / 2) * ((1 : ℝ) / 2) ^ b := by
  change (2 : ℝ) ^ (-(b + 1 : ℤ)) = _
  have h := neg_power_geometric b 1
  norm_num at h
  convert h using 1
  congr 1
  omega

theorem weight_inr_mul (a b : ℕ) :
    weight (.inr (a, b)) = weight (.inl a) * landingWeight b := by
  change (2 : ℝ) ^ (-(a + 2 : ℤ) - (b + 1 : ℤ)) =
    (2 : ℝ) ^ (-(a + 2 : ℤ)) * (2 : ℝ) ^ (-(b + 1 : ℤ))
  rw [sub_eq_add_neg, zpow_add₀ (by norm_num)]

theorem ascending_weight_summable : Summable (fun a : ℕ => weight (.inl a)) := by
  simpa only [weight_inl_geometric] using summable_geometric_two.mul_left ((1 : ℝ) / 4)

theorem ascending_weight_tsum : (∑' a : ℕ, weight (.inl a)) = (1 : ℝ) / 2 := by
  simp_rw [weight_inl_geometric]
  rw [summable_geometric_two.tsum_mul_left, tsum_geometric_two]
  norm_num

theorem landingWeight_summable : Summable landingWeight := by
  change Summable (fun b : ℕ => landingWeight b)
  simpa only [landingWeight_geometric] using summable_geometric_two.mul_left ((1 : ℝ) / 2)

theorem landingWeight_tsum : (∑' b : ℕ, landingWeight b) = 1 := by
  simp_rw [landingWeight_geometric]
  rw [summable_geometric_two.tsum_mul_left, tsum_geometric_two]
  norm_num

theorem exit_row_summable (a : ℕ) :
    Summable (fun b : ℕ => weight (.inr (a, b))) := by
  simpa only [weight_inr_mul] using landingWeight_summable.mul_left (weight (.inl a))

theorem exit_row_tsum (a : ℕ) :
    (∑' b : ℕ, weight (.inr (a, b))) = weight (.inl a) := by
  simp_rw [weight_inr_mul]
  rw [landingWeight_summable.tsum_mul_left, landingWeight_tsum, mul_one]

theorem exit_weight_summable : Summable (fun p : ℕ × ℕ => weight (.inr p)) := by
  apply (summable_prod_of_nonneg (fun p => weight_nonneg (.inr p))).mpr
  exact ⟨exit_row_summable, by simpa only [exit_row_tsum] using ascending_weight_summable⟩

theorem weight_summable : Summable weight := by
  exact Summable.sum weight ascending_weight_summable exit_weight_summable

theorem weight_tsum_one : (∑' e : Edge, weight e) = 1 := by
  rw [Summable.tsum_sum (f := weight) ascending_weight_summable exit_weight_summable,
    exit_weight_summable.tsum_prod]
  simp only [exit_row_tsum, ascending_weight_tsum]
  norm_num

theorem selectedWeight_nonneg (φ : Correction) (e : Edge) : 0 ≤ selectedWeight φ e := by
  classical
  unfold selectedWeight
  split
  · exact weight_nonneg e
  · exact le_rfl

theorem selectedWeight_le (φ : Correction) (e : Edge) : selectedWeight φ e ≤ weight e := by
  classical
  unfold selectedWeight
  split
  · exact le_rfl
  · exact weight_nonneg e

theorem selectedWeight_summable (φ : Correction) : Summable (selectedWeight φ) := by
  exact Summable.of_nonneg_of_le (selectedWeight_nonneg φ) (selectedWeight_le φ) weight_summable

theorem selectedWeight_inl (φ : Correction) (a : ℕ) :
    selectedWeight φ (.inl a) = ascendingMass φ a := by
  rfl

theorem selectedWeight_inr (φ : Correction) (a b : ℕ) :
    selectedWeight φ (.inr (a, b)) = exitMass φ a b := by
  rfl

theorem selected_ascending_summable (φ : Correction) :
    Summable (fun a : ℕ => selectedWeight φ (.inl a)) :=
  (selectedWeight_summable φ).comp_injective Sum.inl_injective

theorem selected_exit_summable (φ : Correction) :
    Summable (fun p : ℕ × ℕ => selectedWeight φ (.inr p)) :=
  (selectedWeight_summable φ).comp_injective Sum.inr_injective

theorem selectedWeight_tsum_eq_symbolic (φ : Correction) :
    (∑' e : Edge, selectedWeight φ e) = symbolicFailureDensity φ := by
  rw [Summable.tsum_sum (f := selectedWeight φ)
      (selected_ascending_summable φ) (selected_exit_summable φ),
    (selected_exit_summable φ).tsum_prod]
  simp only [selectedWeight_inl, selectedWeight_inr, symbolicFailureDensity]

theorem symbolic_mass_summable : SymbolicMassSummable := by
  intro φ
  refine ⟨?_, ?_, ?_⟩
  · simpa only [selectedWeight_inl] using selected_ascending_summable φ
  · intro k
    simpa only [selectedWeight_inr] using (selected_exit_summable φ).prod_factor k
  · simpa only [selectedWeight_inr] using (selected_exit_summable φ).prod

theorem symbolic_density_bounds (φ : Correction) :
    0 ≤ symbolicFailureDensity φ ∧ symbolicFailureDensity φ ≤ 1 := by
  rw [← selectedWeight_tsum_eq_symbolic]
  refine ⟨tsum_nonneg (selectedWeight_nonneg φ), ?_⟩
  calc
    (∑' e : Edge, selectedWeight φ e) ≤ ∑' e : Edge, weight e :=
      Summable.tsum_le_tsum (selectedWeight_le φ) (selectedWeight_summable φ) weight_summable
    _ = 1 := weight_tsum_one

end ExternalO3PopulationWeights
