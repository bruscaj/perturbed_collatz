import WordPartitions

/-! Direct finite exponential partition estimates; no pressure-limit premise. -/
namespace ExternalBridgePressureWordFiniteComparison
open ExternalFiniteBridgeDraft ExternalBridgePressureDraft ExternalBridgePressureWordDraft
open ExternalBridgePressureWordArithmetic ExternalBridgePressureWordPopulation
open ExternalBridgePressureWordReward
open scoped BigOperators

 theorem aux_partition_eq_sum (x : ℝ) (n : ℕ) (lam : ℝ) (hn : 0<n)
    [Fintype (AuxWords x n)] :
    auxPartition x n lam = ∑ w : AuxWords x n, Real.exp (lam*auxReward x n w.val) := by
  simp only [auxPartition,Nat.ne_of_gt hn,ite_false,tsum_fintype]

theorem partition_term_le (x : ℝ) (n : ℕ) (hx : ClosedPhase x) (lam : ℝ)
    (w : AuxWords x n) : Real.exp (lam*auxReward x n w.val) ≤ auxPartition x n lam := by
  have := aux_words_finite x n hx
  let := Fintype.ofFinite (AuxWords x n)
  rw [aux_partition_eq_sum x n lam w.property.1]
  exact Finset.single_le_sum (f := fun w : AuxWords x n => Real.exp (lam*auxReward x n w.val))
    (fun _ _ => le_of_lt (Real.exp_pos _)) (Finset.mem_univ w)

theorem aux_partition_positive (x : ℝ) (n : ℕ) (hx : ClosedPhase x) (lam : ℝ) :
    0<auxPartition x n lam := by
  by_cases hn : n=0
  · simp [auxPartition,hn]
  · let w : AuxWords x n := ⟨canonicalWord x n,(canonical_word_law x n hx).2.2 (by omega)⟩
    exact lt_of_lt_of_le (Real.exp_pos _) (partition_term_le x n hx lam w)

theorem partition_lower_one (x : ℝ) (n : ℕ) (hx : ClosedPhase x) (lam : ℝ) (hl : 0≤lam) :
    1≤auxPartition x n lam := by
  by_cases hn : n=0
  · simp [auxPartition,hn]
  · let w : AuxWords x n := ⟨canonicalWord x n,(canonical_word_law x n hx).2.2 (by omega)⟩
    have hr := (normalized_reward_law x n w.val hx w.property).2.2.1
    have he : 1≤Real.exp (lam*auxReward x n w.val) := Real.one_le_exp_iff.mpr (mul_nonneg hl hr)
    exact he.trans (partition_term_le x n hx lam w)

theorem partition_exp_upper (x : ℝ) (n : ℕ) (hx : ClosedPhase x) (lam : ℝ) (hl : 0≤lam) :
    auxPartition x n lam ≤ Real.exp ((n : ℝ)*(Real.log 4+lam)) := by
  by_cases hn : n=0
  · simp [auxPartition,hn]
  · have := aux_words_finite x n hx
    let := Fintype.ofFinite (AuxWords x n)
    rw [aux_partition_eq_sum x n lam (by omega)]
    calc
      (∑ w : AuxWords x n, Real.exp (lam*auxReward x n w.val)) ≤
          ∑ _w : AuxWords x n, Real.exp (lam*(n : ℝ)) := by
        apply Finset.sum_le_sum
        intro w _
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
          (normalized_reward_law x n w.val hx w.property).2.2.2 hl)
      _ = (Nat.card (AuxWords x n) : ℝ)*Real.exp (lam*(n : ℝ)) := by
        simp [Nat.card_eq_fintype_card]
      _ ≤ (4 : ℝ)^n*Real.exp (lam*(n : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt (Real.exp_pos _))
        exact_mod_cast aux_words_card_le x n hx
      _ = Real.exp ((n : ℝ)*(Real.log 4+lam)) := by
        rw [mul_add,Real.exp_add,Real.exp_nat_mul,Real.exp_log (by norm_num : (0 : ℝ)<4)]
        congr 2
        ring

theorem finite_partition_bounds : FinitePartitionBounds := by
  intro x n lam hx
  refine ⟨aux_partition_positive x n hx lam,fun hl => ?_⟩
  refine ⟨Real.log_nonneg (partition_lower_one x n hx lam hl),?_⟩
  exact (Real.log_le_iff_le_exp (aux_partition_positive x n hx lam)).mpr (partition_exp_upper x n hx lam hl)

theorem partition_tilt_compare (x : ℝ) (n : ℕ) (hx : ClosedPhase x) (lam mu : ℝ) :
    auxPartition x n lam ≤ Real.exp ((n : ℝ)*|lam-mu|)*auxPartition x n mu := by
  by_cases hn : n=0
  · simp [auxPartition,hn]
  · have := aux_words_finite x n hx
    let := Fintype.ofFinite (AuxWords x n)
    rw [aux_partition_eq_sum x n lam (by omega),aux_partition_eq_sum x n mu (by omega),Finset.mul_sum]
    apply Finset.sum_le_sum
    intro w _
    have hr := normalized_reward_law x n w.val hx w.property |>.2.2
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have ha := mul_le_mul_of_nonneg_right (le_abs_self (lam-mu)) hr.1
    have hb := mul_le_mul_of_nonneg_left hr.2 (abs_nonneg (lam-mu))
    nlinarith

theorem log_tilt_compare (x : ℝ) (n : ℕ) (hx : ClosedPhase x) (lam mu : ℝ) :
    auxLogPartition x n lam - auxLogPartition x n mu ≤ (n : ℝ)*|lam-mu| := by
  have hz := aux_partition_positive x n hx mu
  have h := Real.log_le_log (aux_partition_positive x n hx lam) (partition_tilt_compare x n hx lam mu)
  rw [Real.log_mul (ne_of_gt (Real.exp_pos _)) (ne_of_gt hz),Real.log_exp] at h
  unfold auxLogPartition
  linarith

theorem finite_tilt_lipschitz : FiniteTiltLipschitz := by
  intro x n lam mu hx _ _
  apply abs_le.mpr
  have h1 := log_tilt_compare x n hx lam mu
  have h2 := log_tilt_compare x n hx mu lam
  rw [abs_sub_comm mu lam] at h2
  constructor <;> linarith

end ExternalBridgePressureWordFiniteComparison
