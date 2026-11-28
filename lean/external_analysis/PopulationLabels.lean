import PopulationWeights
import Gains
import ExitCylinders
import PartitionGeneral

/-!
Literal population labels for the frozen depth-one Syracuse model.
Every odd seed is either inside a nonfinal block (remaining length at least two)
or at an exit (valuation at least two), with a positive next-block length.
The labels are actual arithmetic functions of seed 2*n+1. Their densities come
from the proved exact residue cylinders, not an independence assumption.
Per-edge eventual decisions follow from the literal logarithmic error theorem;
no common stabilization threshold and no bound on the correction is imposed.
-/
namespace ExternalO3PopulationLabels

open ExternalO3Spec ExternalO3Arithmetic ExternalO3PopulationWeights
open ExternalO3Gains ExternalO3Cylinders ExternalO3ExitCylinders
open ExternalO3CountablePartition Filter
open scoped Topology

/-- Sum labels encode ascending offsets or (exit valuation,next-block) offsets. -/
def label (n : ℕ) : Edge :=
  if 2 ≤ blockLength (2 * n + 1) then
    .inl (blockLength (2 * n + 1) - 2)
  else
    .inr (strideValuation (2 * n + 1) - 2,
      blockLength (stride (2 * n + 1)) - 1)

theorem label_inl_iff (n a : ℕ) :
    label n = .inl a ↔ blockLength (2 * n + 1) = a + 2 := by
  by_cases hr : 2 ≤ blockLength (2 * n + 1)
  · simp only [label, ite_eq_left hr, Sum.inl.injEq]
    omega
  · simp only [label, ite_eq_right hr, Sum.inr_ne_inl, false_iff]
    omega

theorem label_inr_iff (n a b : ℕ) :
    label n = .inr (a, b) ↔
      strideValuation (2 * n + 1) = a + 2 ∧
      blockLength (stride (2 * n + 1)) = b + 1 := by
  have hx : IsOddSeed (2 * n + 1) := ⟨by omega, by omega⟩
  by_cases hr : 2 ≤ blockLength (2 * n + 1)
  · have hk := valuation_one_of_long_block (2 * n + 1) hx hr
    simp only [label, ite_eq_left hr, Sum.inl_ne_inr, false_iff]
    omega
  · have hp := block_length_positive (2 * n + 1) hx
    have hb : blockLength (2 * n + 1) = 1 := by omega
    have hk := exit_valuation_of_short_block (2 * n + 1) hx hb
    have hn := block_length_positive (stride (2 * n + 1)) (stride_output _)
    simp only [label, ite_eq_right hr, Sum.inr.injEq, Prod.mk.injEq]
    omega

/-- The arithmetic decoder never loses the positivity of an exit's fields. -/
theorem exit_fields_positive (n : ℕ) (hr : ¬2 ≤ blockLength (2 * n + 1)) :
    2 ≤ strideValuation (2 * n + 1) ∧
      1 ≤ blockLength (stride (2 * n + 1)) := by
  have hx : IsOddSeed (2 * n + 1) := ⟨by omega, by omega⟩
  have hp := block_length_positive (2 * n + 1) hx
  exact ⟨exit_valuation_of_short_block _ hx (by omega),
    block_length_positive _ (stride_output _)⟩

theorem weight_inl_reciprocal (a : ℕ) :
    weight (.inl a) = 1 / (2 : ℝ) ^ (a + 2) := by
  change (2 : ℝ) ^ (-(a + 2 : ℤ)) = _
  rw [show -(a + 2 : ℤ) = -((a + 2 : ℕ) : ℤ) by omega]
  simp only [zpow_neg, zpow_natCast, one_div]

theorem weight_inr_reciprocal (a b : ℕ) :
    weight (.inr (a, b)) = 1 / (2 : ℝ) ^ (a + b + 3) := by
  change (2 : ℝ) ^ (-(a + 2 : ℤ) - (b + 1 : ℤ)) = _
  rw [show -(a + 2 : ℤ) - (b + 1 : ℤ) = -((a + b + 3 : ℕ) : ℤ) by omega]
  simp only [zpow_neg, zpow_natCast, one_div]

/-- Exact unconditional density of each literal ascending label. -/
theorem ascending_label_density (a : ℕ) :
    Tendsto (frequency (fun n => label n = .inl a)) atTop (𝓝 (weight (.inl a))) := by
  have hp : (fun n => label n = .inl a) =
      (fun n => blockLength (2 * n + 1) = a + 2) := by
    funext n
    exact propext (label_inl_iff n a)
  rw [hp, weight_inl_reciprocal]
  change Tendsto (fun N => frequency (fun n => blockLength (2 * n + 1) = a + 2) N)
    atTop (𝓝 (1 / (2 : ℝ) ^ (a + 2)))
  apply (ascending_density a).congr'
  filter_upwards [] with N
  unfold frequency
  apply congrArg (fun s : Finset ℕ => (s.card : ℝ) / (N : ℝ))
  ext n
  simp

/-- Exact unconditional density of each literal exit/landing label. -/
theorem exit_label_density (a b : ℕ) :
    Tendsto (frequency (fun n => label n = .inr (a, b)))
      atTop (𝓝 (weight (.inr (a, b)))) := by
  have hp : (fun n => label n = .inr (a, b)) =
      (fun n => strideValuation (2 * n + 1) = a + 2 ∧
        blockLength (stride (2 * n + 1)) = b + 1) := by
    funext n
    exact propext (label_inr_iff n a b)
  rw [hp, weight_inr_reciprocal]
  change Tendsto (fun N => frequency (fun n =>
    strideValuation (2 * n + 1) = a + 2 ∧
      blockLength (stride (2 * n + 1)) = b + 1) N)
    atTop (𝓝 (1 / (2 : ℝ) ^ (a + b + 3)))
  apply (exit_cylinder_density a b).congr'
  filter_upwards [] with N
  unfold frequency
  apply congrArg (fun s : Finset ℕ => (s.card : ℝ) / (N : ℝ))
  ext n
  simp

/-- All coordinate density hypotheses for the general partition theorem. -/
theorem label_density (e : Edge) :
    Tendsto (frequency (fun n => label n = e)) atTop (𝓝 (weight e)) := by
  cases e with
  | inl a => exact ascending_label_density a
  | inr p =>
    rcases p with ⟨a, b⟩
    exact exit_label_density a b

/-- Each edge eventually has precisely its frozen symbolic failure decision. -/
theorem label_stabilizes (φ : Correction) (e : Edge) :
    ∃ M : ℕ, ∀ n : ℕ, M ≤ n → label n = e →
      (FailsAt φ (2 * n + 1) ↔ Bad φ e) := by
  cases e with
  | inl a =>
    obtain ⟨M, hM⟩ := ascending_stabilizes φ a
    refine ⟨M, fun n hn he => ?_⟩
    exact hM n hn ((label_inl_iff n a).mp he)
  | inr p =>
    rcases p with ⟨a, b⟩
    obtain ⟨M, hM⟩ := exit_stabilizes φ a b
    refine ⟨M, fun n hn he => ?_⟩
    obtain ⟨hk, hr⟩ := (label_inr_iff n a b).mp he
    exact hM n hn hk hr

/-- The generic population frequency is definitionally the frozen source one. -/
theorem failure_frequency_eq (φ : Correction) (N : ℕ) :
    frequency (fun n => FailsAt φ (2 * n + 1)) N = failureFrequency φ N := by
  rfl

end ExternalO3PopulationLabels
