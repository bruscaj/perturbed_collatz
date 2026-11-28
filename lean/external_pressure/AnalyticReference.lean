import AnalyticDiscrepancy
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Uniform reference averages by monotone finite-bin envelopes. -/
namespace ExternalBridgePressureAnalyticReference
open ExternalBridgePressureDraft ExternalBridgePressureAnalyticDraft
open ExternalBridgePressureAnalyticDiscrepancy ExternalBridgePressureAnalyticCircleGrid
open scoped BigOperators
noncomputable section
local instance (P : Prop) : Decidable P := Classical.propDecidable P

def weight (u : ℝ) : ℝ := (2 : ℝ)^(-u)
def bin (M i : ℕ) : ℝ := (i : ℝ)/(M : ℝ)

theorem weight_continuous : Continuous weight :=
  (Real.continuous_const_rpow (a := 2) (by norm_num)).comp continuous_neg

theorem weight_antitone : Antitone weight := by
  intro u v huv
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (neg_le_neg huv)

theorem weight_bounds (u : ℝ) (hu : 0 ≤ u) : 0 ≤ weight u ∧ weight u ≤ 1 := by
  refine ⟨(Real.rpow_pos_of_pos (by norm_num) _).le, ?_⟩
  have := weight_antitone hu
  simpa [weight] using this

theorem weight_integral : (∫ u in (0 : ℝ)..1, weight u) = meanReference := by
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hd (u : ℝ) : HasDerivAt (fun v : ℝ => -weight v/Real.log 2) (weight u) u := by
    have hneg : HasDerivAt (fun v : ℝ => -v) (-1) u := (hasDerivAt_id u).neg
    have hp : HasDerivAt weight (Real.log 2 * (-1) * weight u) u := by
      exact HasDerivAt.const_rpow (by norm_num : (0 : ℝ)<2) hneg
    convert hp.neg.div_const (Real.log 2) using 1
    field_simp
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    (weight_continuous.intervalIntegrable 0 1)
  rw [h]
  norm_num [weight,meanReference,Real.rpow_neg_one]
  field_simp
  ring

theorem bin_membership (M : ℕ) (hM : 0 < M) (u : ℝ) (hu : 0 ≤ u ∧ u < 1) :
    ∃ k : ℕ, k < M ∧ ∀ i : ℕ,
      (bin M i ≤ u ∧ u < bin M (i+1)) ↔ i=k := by
  have hMp : (0 : ℝ)<M := by exact_mod_cast hM
  have hnonneg : 0 ≤ u*(M : ℝ) := mul_nonneg hu.1 hMp.le
  refine ⟨⌊u*(M : ℝ)⌋₊, (Nat.floor_lt hnonneg).mpr (by nlinarith [hu.2]), ?_⟩
  intro i
  rw [bin,bin,div_le_iff₀ hMp,lt_div_iff₀ hMp]
  simp only [Nat.cast_add,Nat.cast_one]
  exact (Nat.floor_eq_iff hnonneg).symm.trans eq_comm

/-- Exactly one half-open bin contributes; both weighted step envelopes are literal sums. -/
theorem step_envelope (M : ℕ) (hM : 0 < M) (u : ℝ) (hu : 0 ≤ u ∧ u < 1) :
    (∑ i ∈ Finset.range M, weight (bin M (i+1))*chi (bin M i) (bin M (i+1)) u) ≤ weight u ∧
    weight u ≤ ∑ i ∈ Finset.range M, weight (bin M i)*chi (bin M i) (bin M (i+1)) u := by
  obtain ⟨k,hk,hmem⟩ := bin_membership M hM u hu
  have heq (c : ℕ → ℝ) :
      (∑ i ∈ Finset.range M, c i * chi (bin M i) (bin M (i+1)) u) = c k := by
    rw [Finset.sum_eq_single k]
    · simp [chi,(hmem k).mpr rfl]
    · intro i _ hik
      rw [chi,ite_eq_right (by intro hi; exact hik ((hmem i).mp hi)),mul_zero]
    · exact fun h => (h (Finset.mem_range.mpr hk)).elim
  rw [heq,heq]
  have hkbin := (hmem k).mpr rfl
  exact ⟨weight_antitone hkbin.2.le,weight_antitone hkbin.1⟩


def lowerRiemann (M : ℕ) : ℝ := (∑ i ∈ Finset.range M, weight (bin M (i+1)))/(M : ℝ)
def upperRiemann (M : ℕ) : ℝ := (∑ i ∈ Finset.range M, weight (bin M i))/(M : ℝ)

theorem bin_width (M i : ℕ) : bin M (i+1)-bin M i = 1/(M : ℝ) := by
  simp only [bin,Nat.cast_add,Nat.cast_one]
  ring

theorem riemann_gap (M : ℕ) (hM : 0 < M) :
    upperRiemann M-lowerRiemann M = 1/(2*(M : ℝ)) := by
  have hMp : (M : ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hM
  have htel := Finset.sum_range_sub (fun i => weight (bin M i)) M
  have hend : weight (bin M M)-weight (bin M 0) = -(1/2 : ℝ) := by
    norm_num [bin,weight,hMp,Real.rpow_neg_one]
  rw [hend] at htel
  unfold upperRiemann lowerRiemann
  rw [← sub_div]
  have hsum : (∑ i ∈ Finset.range M, weight (bin M i)) -
      (∑ i ∈ Finset.range M, weight (bin M (i+1))) = (1/2 : ℝ) := by
    rw [Finset.sum_sub_distrib] at htel
    linarith
  rw [hsum]
  ring

theorem riemann_brackets (M : ℕ) (hM : 0 < M) :
    lowerRiemann M ≤ meanReference ∧ meanReference ≤ upperRiemann M := by
  have hMp : (0 : ℝ)<M := by exact_mod_cast hM
  have hint (i : ℕ) : IntervalIntegrable weight MeasureTheory.volume (bin M i) (bin M (i+1)) :=
    weight_continuous.intervalIntegrable _ _
  have hcell (i : ℕ) : weight (bin M (i+1))/(M : ℝ) ≤
      (∫ u in bin M i..bin M (i+1), weight u) ∧
      (∫ u in bin M i..bin M (i+1), weight u) ≤ weight (bin M i)/(M : ℝ) := by
    have hab : bin M i ≤ bin M (i+1) := by rw [bin,bin]; gcongr; norm_num
    have hlo := intervalIntegral.integral_mono_on hab (intervalIntegrable_const) (hint i)
      (fun u hu => weight_antitone hu.2)
    have hhi := intervalIntegral.integral_mono_on hab (hint i) (intervalIntegrable_const)
      (fun u hu => weight_antitone hu.1)
    simp only [intervalIntegral.integral_const,smul_eq_mul,bin_width] at hlo hhi
    exact ⟨by simpa [div_eq_mul_inv,mul_comm] using hlo, by simpa [div_eq_mul_inv,mul_comm] using hhi⟩
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (n:=M)
    (fun i _ => hint i)
  have hzero : bin M 0 = 0 := by simp [bin]
  have hone : bin M M = 1 := by simp [bin,ne_of_gt hMp]
  rw [hzero,hone,weight_integral] at hsum
  constructor
  · unfold lowerRiemann
    rw [Finset.sum_div]
    rw [← hsum]
    exact Finset.sum_le_sum (fun i _ => (hcell i).1)
  · unfold upperRiemann
    rw [Finset.sum_div]
    rw [← hsum]
    exact Finset.sum_le_sum (fun i _ => (hcell i).2)


theorem weighted_count_error (M n : ℕ) (x η : ℝ) (hη : 0 ≤ η) (c : ℕ → ℝ)
    (hc : ∀ i < M, 0 ≤ c i ∧ c i ≤ 1)
    (hd : ∀ i < M, |(shiftedIntervalCount x (bin M i) (bin M (i+1)) n : ℝ)/(n : ℝ)-1/(M : ℝ)| ≤ η) :
    |(∑ i ∈ Finset.range M, c i*((shiftedIntervalCount x (bin M i) (bin M (i+1)) n : ℝ)/(n : ℝ))) -
      (∑ i ∈ Finset.range M, c i)/(M : ℝ)| ≤ (M : ℝ)*η := by
  rw [Finset.sum_div, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ Finset.range M, |c i*((shiftedIntervalCount x (bin M i) (bin M (i+1)) n : ℝ)/(n : ℝ))-c i/(M : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ ∈ Finset.range M, η := by
      apply Finset.sum_le_sum
      intro i hi
      have hiM := Finset.mem_range.mp hi
      have hid : c i*((shiftedIntervalCount x (bin M i) (bin M (i+1)) n : ℝ)/(n : ℝ))-c i/(M : ℝ) =
        c i*((shiftedIntervalCount x (bin M i) (bin M (i+1)) n : ℝ)/(n : ℝ)-1/(M : ℝ)) := by ring
      rw [hid,abs_mul,abs_of_nonneg (hc i hiM).1]
      calc
        _ ≤ c i*η := mul_le_mul_of_nonneg_left (hd i hiM) (hc i hiM).1
        _ ≤ η := by nlinarith [(hc i hiM).2]
    _ = _ := by simp

theorem reference_as_range (x : ℝ) (n : ℕ) :
    reference x n = ∑ t ∈ Finset.range n, weight (phaseShift x t) := by
  exact Fin.sum_univ_eq_sum_range (fun t : ℕ => weight (phaseShift x t)) n

theorem empirical_brackets (M n : ℕ) (hM : 0 < M) (hn : 0 < n) (x : ℝ) :
    (∑ i ∈ Finset.range M, weight (bin M (i+1))*((shiftedIntervalCount x (bin M i) (bin M (i+1)) n : ℝ)/(n : ℝ))) ≤
      reference x n/(n : ℝ) ∧
    reference x n/(n : ℝ) ≤ ∑ i ∈ Finset.range M,
      weight (bin M i)*((shiftedIntervalCount x (bin M i) (bin M (i+1)) n : ℝ)/(n : ℝ)) := by
  have hnp : (0 : ℝ)<n := by exact_mod_cast hn
  have hp (t : ℕ) := step_envelope M hM (phaseShift x t) ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩
  have heq (c : ℕ → ℝ) :
      (∑ t ∈ Finset.range n, ∑ i ∈ Finset.range M, c i*chi (bin M i) (bin M (i+1)) (phaseShift x t))/(n : ℝ) =
      ∑ i ∈ Finset.range M, c i*((shiftedIntervalCount x (bin M i) (bin M (i+1)) n : ℝ)/(n : ℝ)) := by
    rw [Finset.sum_comm,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.mul_sum,← shifted_count_sum,mul_div_assoc]
  constructor
  · rw [← heq,reference_as_range]
    exact (div_le_div_iff_of_pos_right hnp).mpr (Finset.sum_le_sum (fun t _ => (hp t).1))
  · rw [← heq,reference_as_range]
    exact (div_le_div_iff_of_pos_right hnp).mpr (Finset.sum_le_sum (fun t _ => (hp t).2))


/-- Frozen A26: the actual mean, uniformly over physical starting phases. -/
theorem uniform_reference_composition : UniformReferenceComposition := by
  intro eps heps
  let M : ℕ := ⌈4/eps⌉₊+1
  have hM : 0 < M := by dsimp [M]; omega
  have hMp : (0 : ℝ)<M := by exact_mod_cast hM
  have hMlarge : 4/eps < (M : ℝ) := by
    have h := Nat.le_ceil (4/eps)
    dsimp [M]
    push_cast
    linarith
  have hgap : 1/(2*(M : ℝ)) < eps/8 := by
    have h := (div_lt_iff₀ heps).mp hMlarge
    apply (div_lt_iff₀ (by positivity : (0 : ℝ)<2*(M : ℝ))).mpr
    nlinarith
  let η : ℝ := eps/(4*(M : ℝ))
  have hη : 0 < η := by dsimp [η]; positivity
  have hMη : (M : ℝ)*η = eps/4 := by dsimp [η]; field_simp
  obtain ⟨N,hN,h⟩ := uniform_shifted_interval_discrepancy η hη
  refine ⟨N,hN,?_⟩
  intro n hn x hx0 hx1
  have hn0 : 0 < n := by omega
  have hd (i : ℕ) (hi : i < M) :
      |(shiftedIntervalCount x (bin M i) (bin M (i+1)) n : ℝ)/(n : ℝ)-1/(M : ℝ)| ≤ η := by
    have hbin0 : 0 ≤ bin M i := by unfold bin; positivity
    have hbinmono : bin M i ≤ bin M (i+1) := by unfold bin; gcongr; norm_num
    have hbin1 : bin M (i+1) ≤ 1 := by
      rw [bin,div_le_iff₀ hMp]
      push_cast
      simpa only [one_mul,Nat.cast_add,Nat.cast_one] using (Nat.cast_le.mpr (Nat.succ_le_of_lt hi) : ((i+1 : ℕ) : ℝ) ≤ (M : ℝ))
    have hierr := h n hn x (bin M i) (bin M (i+1)) ⟨hx0,hx1⟩ hbin0 hbinmono hbin1
    rw [bin_width] at hierr
    exact hierr.le
  have hlow := weighted_count_error M n x η hη.le (fun i => weight (bin M (i+1)))
    (fun i _ => weight_bounds _ (by unfold bin; positivity)) hd
  have hhigh := weighted_count_error M n x η hη.le (fun i => weight (bin M i))
    (fun i _ => weight_bounds _ (by unfold bin; positivity)) hd
  rw [hMη] at hlow hhigh
  have hlo := (abs_le.mp hlow).1
  have hhi := (abs_le.mp hhigh).2
  change -(eps/4) ≤ _-lowerRiemann M at hlo
  change _-upperRiemann M ≤ eps/4 at hhi
  have he := empirical_brackets M n hM hn0 x
  have hb := riemann_brackets M hM
  have hg := riemann_gap M hM
  rw [abs_lt]
  constructor <;> linarith

end
end ExternalBridgePressureAnalyticReference
