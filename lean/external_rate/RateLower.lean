import RateNormalization
import RateSymmetry
import GeneralSourceDensity
import GeneralDensity

/-! Finite-cycle forcing converted to literal odd-seed failure density. -/
namespace ExternalO3RateLower
open scoped BigOperators
open ExternalO3GeneralDraft ExternalO3RateDraft ExternalO3GeneralWeights
open ExternalO3GeneralMarginal ExternalO3RateMoments ExternalO3RateCycles
open ExternalO3RateNormalization ExternalO3RateSymmetry ExternalO3GeneralDensity

/-- Rotation of auxiliary finite history slots, not of an integer trajectory. -/
def rotation (h : Depth) (i : ℕ) : Equiv.Perm (Fin (h.val + 1)) :=
  Equiv.addRight (Fin.ofNat (h.val + 1) i)

def rotatedHistory (h : Depth) (i : ℕ) : History h ≃ History h :=
  reindex (h.val + 1) (rotation h i)

theorem cyclicLength_rotated (h : Depth) (r : History h) (i t : ℕ) :
    cyclicLength h (rotatedHistory h i r) t = cyclicLength h r (i + t) := by
  change r (Fin.ofNat (h.val + 1) t + Fin.ofNat (h.val + 1) i) + 1 =
    r (Fin.ofNat (h.val + 1) (i + t)) + 1
  congr 2
  apply Fin.ext
  simp [Fin.add_def, Nat.add_mod, Nat.add_comm]

theorem cyclicWindow_rotated (h : Depth) (r : History h) (i t s : ℕ) :
    cyclicWindow h (rotatedHistory h i r) t s = cyclicWindow h r (i + t) s := by
  funext j
  simp only [cyclicWindow]
  split_ifs
  · rfl
  · rw [cyclicLength_rotated, Nat.add_assoc]

theorem blockFailures_rotated (h : Depth) (φ : Correction h) (r : History h)
    (i k : ℕ) :
    blockFailures h φ (rotatedHistory h i r) 0 k = blockFailures h φ r i k := by
  unfold blockFailures ascentGain exitGain
  simp only [cyclicLength_rotated, cyclicWindow_rotated, Nat.add_zero, Nat.zero_add]

theorem historyWeight_rotated (h : Depth) (r : History h) (i : ℕ) :
    historyWeight h (rotatedHistory h i r) = historyWeight h r := by
  simp only [history_weight_product]
  exact productWeight_reindex (h.val + 1) (rotation h i) r

theorem weighted_block_summable (h : Depth) (φ : Correction h) (i : ℕ) :
    Summable (fun r : History h => historyWeight h r * (blockFailures h φ r i 2 : ℝ)) := by
  have hs := (cyclic_normalization h φ).1.comp_injective (rotatedHistory h i).injective
  simpa only [Function.comp_def, historyWeight_rotated, blockFailures_rotated] using hs

theorem weighted_block_tsum_eq_zero (h : Depth) (φ : Correction h) (i : ℕ) :
    (∑' r : History h, historyWeight h r * (blockFailures h φ r i 2 : ℝ)) =
      ∑' r : History h, historyWeight h r * (blockFailures h φ r 0 2 : ℝ) := by
  calc
    _ = ∑' r : History h, historyWeight h r *
        (blockFailures h φ (rotatedHistory h i r) 0 2 : ℝ) := by
      apply tsum_congr
      intro r
      rw [blockFailures_rotated]
    _ = _ := by
      simp only [history_weight_product]
      exact weighted_tsum_reindex (h.val + 1) (rotation h i)
        (fun r => (blockFailures h φ r 0 2 : ℝ))

theorem weighted_cycle_hasSum (h : Depth) (φ : Correction h) :
    HasSum (fun r : History h => historyWeight h r * (cycleFailures h φ r : ℝ))
      (((h.val : ℝ) + 1) * (2 * ascendingMass h φ + 4 * exitMass h φ 0)) := by
  have hs := hasSum_sum (s := Finset.univ)
    (fun (i : Fin (h.val + 1)) _ => (weighted_block_summable h φ i.val).hasSum)
  convert hs using 1
  · funext r
    simp only [cycleFailures, Nat.cast_sum, Finset.mul_sum]
  · simp_rw [weighted_block_tsum_eq_zero, (cyclic_normalization h φ).2]
    simp
    ring

theorem weighted_cycle_summable (h : Depth) (φ : Correction h) :
    Summable (fun r : History h => historyWeight h r * (cycleFailures h φ r : ℝ)) :=
  (weighted_cycle_hasSum h φ).summable

theorem positive_cycle_mask_summable (h : Depth) :
    Summable (fun r : History h => if 0 < cycleGain h r then historyWeight h r else 0) := by
  classical
  exact masked_summable (historyWeight h)
    (fun r => by rw [history_weight_product]; exact le_of_lt (productWeight_positive _ _))
    (history_weight_law h).1 (fun r => 0 < cycleGain h r)

theorem positive_cycle_le_expected_failures (h : Depth) (φ : Correction h) :
    positiveCycleMass h ≤
      ((h.val : ℝ) + 1) * (2 * ascendingMass h φ + 4 * exitMass h φ 0) := by
  classical
  have hp (r : History h) :
      (if 0 < cycleGain h r then historyWeight h r else 0) ≤
        historyWeight h r * (cycleFailures h φ r : ℝ) := by
    have hw : 0 ≤ historyWeight h r := by
      rw [history_weight_product]
      exact le_of_lt (productWeight_positive _ _)
    split_ifs with hg
    · have hh : (1 : ℝ) ≤ (cycleFailures h φ r : ℝ) := by
        exact_mod_cast (cyclic_forcing h φ r).2 hg
      nlinarith
    · positivity
  have ht := Summable.tsum_le_tsum hp (positive_cycle_mask_summable h)
    (weighted_cycle_summable h φ)
  change positiveCycleMass h ≤ _ at ht
  rwa [(weighted_cycle_hasSum h φ).tsum_eq] at ht

theorem ascending_exit_le_symbolic (h : Depth) (φ : Correction h) :
    ascendingMass h φ + exitMass h φ 0 ≤ symbolicFailureDensity h φ := by
  have hs := selected_mass_summable h φ
  have ha := hs.comp_injective Sum.inl_injective
  have he := hs.comp_injective Sum.inr_injective
  have hi : Function.Injective (fun b : Fin h.val → ℕ => (0, b)) := by
    intro a b hab
    exact congrArg Prod.snd hab
  have hx := he.comp_injective hi
  have hl := Summable.tsum_le_tsum_of_inj (fun b : Fin h.val → ℕ => (0, b)) hi
    (fun p _ => selectedWeight_nonneg h φ (.inr p)) (fun _ => le_rfl) hx he
  unfold symbolicFailureDensity
  rw [Summable.tsum_sum ha he]
  exact add_le_add (le_refl (ascendingMass h φ)) hl

theorem block_expectation_le_literal (h : Depth) (φ : Correction h) (d : ℝ)
    (hd : HasFailureDensity h φ d) :
    2 * ascendingMass h φ + 4 * exitMass h φ 0 ≤ 4 * d := by
  have he : d = symbolicFailureDensity h φ :=
    ExternalO3GeneralSourceDensity.density_unique h φ d (symbolicFailureDensity h φ)
      hd (density_equals_symbolic h φ).2.2.2
  have hl := ascending_exit_le_symbolic h φ
  have ha : 0 ≤ ascendingMass h φ := tsum_nonneg (fun a => selectedWeight_nonneg _ _ _)
  rw [← he] at hl
  linarith

theorem cyclic_density_lower_bound : CyclicDensityLowerBound := by
  intro h φ d hd
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * ((h.val : ℝ) + 1))).2
  calc
    positiveCycleMass h ≤ ((h.val : ℝ) + 1) *
        (2 * ascendingMass h φ + 4 * exitMass h φ 0) :=
      positive_cycle_le_expected_failures h φ
    _ ≤ ((h.val : ℝ) + 1) * (4 * d) :=
      mul_le_mul_of_nonneg_left (block_expectation_le_literal h φ d hd) (by positivity)
    _ = d * (4 * ((h.val : ℝ) + 1)) := by ring

end ExternalO3RateLower
