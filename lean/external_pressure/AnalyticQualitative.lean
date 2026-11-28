import AnalyticCost
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! Finite exponential convexity and actual candidate qualitative properties. -/
namespace ExternalBridgePressureAnalyticQualitative
open ExternalFiniteBridgeDraft ExternalBridgePressureDraft ExternalBridgePressureWordDraft
open ExternalBridgePressureCompleteDraft ExternalBridgePressureAnalyticDraft
open ExternalBridgePressureWordArithmetic ExternalBridgePressureWordPopulation ExternalBridgePressureWordReward
open ExternalBridgePressureWordFiniteComparison ExternalBridgePressureAnalyticSubsequence
open ExternalBridgePressureAnalyticUniformPressure ExternalBridgePressureAnalyticCost
open ExternalBridgePressurePhase
open Filter Set
open scoped Topology BigOperators

theorem finite_exp_sum_positive {α : Type*} [Fintype α] [Nonempty α] (E : α → ℝ) (a : ℝ) :
    0<∑ i,Real.exp (a*E i) :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

theorem normalized_exp_sum {α : Type*} [Fintype α] [Nonempty α] (E : α → ℝ) (a : ℝ) :
    (∑ i,Real.exp (a*E i-Real.log (∑ j,Real.exp (a*E j))))=1 := by
  have hp := finite_exp_sum_positive E a
  simp_rw [Real.exp_sub,Real.exp_log hp]
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt hp)

theorem finite_log_exp_convex {α : Type*} [Fintype α] [Nonempty α]
    (E : α → ℝ) (a b t : ℝ) (ht0 : 0≤t) (ht1 : t≤1) :
    Real.log (∑ i,Real.exp (((1-t)*a+t*b)*E i)) ≤
      (1-t)*Real.log (∑ i,Real.exp (a*E i))+t*Real.log (∑ i,Real.exp (b*E i)) := by
  let C := (1-t)*Real.log (∑ i,Real.exp (a*E i))+t*Real.log (∑ i,Real.exp (b*E i))
  have hpoint (i : α) :
      Real.exp ((1-t)*(a*E i-Real.log (∑ j,Real.exp (a*E j)))+
        t*(b*E i-Real.log (∑ j,Real.exp (b*E j)))) ≤
      (1-t)*Real.exp (a*E i-Real.log (∑ j,Real.exp (a*E j)))+
        t*Real.exp (b*E i-Real.log (∑ j,Real.exp (b*E j))) := by
    simpa only [smul_eq_mul] using convexOn_exp.2 (Set.mem_univ _) (Set.mem_univ _)
      (sub_nonneg.mpr ht1) ht0 (by ring : (1-t)+t=1)
  have hs := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hpoint i)
  rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,
    normalized_exp_sum E a,normalized_exp_sum E b] at hs
  have he : Real.exp (-C)*(∑ i,Real.exp (((1-t)*a+t*b)*E i)) =
      ∑ i,Real.exp ((1-t)*(a*E i-Real.log (∑ j,Real.exp (a*E j)))+
        t*(b*E i-Real.log (∑ j,Real.exp (b*E j)))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Real.exp_add]
    congr 1
    dsimp [C]
    ring
  have hh : Real.exp (-C)*(∑ i,Real.exp (((1-t)*a+t*b)*E i))≤1 := by rw [he]; linarith
  have hc : Real.exp (-C)*Real.exp C=1 := by rw [← Real.exp_add]; simp
  have hb : (∑ i,Real.exp (((1-t)*a+t*b)*E i))≤Real.exp C := by
    apply (mul_le_mul_iff_right₀ (Real.exp_pos (-C))).mp
    rw [hc]
    exact hh
  exact (Real.log_le_iff_le_exp (finite_exp_sum_positive E _)).mpr hb

theorem finite_pressure_convex (n : ℕ) (hn : 1≤n) (a b t : ℝ) (ht0 : 0≤t) (ht1 : t≤1) :
    auxLogPressure 0 n ((1-t)*a+t*b)≤(1-t)*auxLogPressure 0 n a+t*auxLogPressure 0 n b := by
  have hx : ClosedPhase (0 : ℝ) := by constructor <;> norm_num
  have := aux_words_finite 0 n hx
  let := Fintype.ofFinite (AuxWords 0 n)
  have : Nonempty (AuxWords 0 n) :=
    ⟨⟨canonicalWord 0 n,(canonical_word_law 0 n hx).2.2 (by omega)⟩⟩
  have h := finite_log_exp_convex (fun w : AuxWords 0 n => auxReward 0 n w.val) a b t ht0 ht1
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn
  unfold auxLogPressure auxLogPartition
  rw [aux_partition_eq_sum 0 n _ (by omega),aux_partition_eq_sum 0 n a (by omega),aux_partition_eq_sum 0 n b (by omega)]
  calc
    _ ≤ ((1-t)*Real.log (∑ w : AuxWords 0 n,Real.exp (a*auxReward 0 n w.val))+
        t*Real.log (∑ w : AuxWords 0 n,Real.exp (b*auxReward 0 n w.val)))/(n : ℝ) :=
      div_le_div_of_nonneg_right h (le_of_lt hnR)
    _ = _ := by ring

theorem candidate_pressure_convex : ConvexNonnegative candidatePressure := by
  intro a b t ha hb ht0 ht1
  have hm : 0≤(1-t)*a+t*b := add_nonneg (mul_nonneg (sub_nonneg.mpr ht1) ha) (mul_nonneg ht0 hb)
  have hx : ClosedPhase (0 : ℝ) := by constructor <;> norm_num
  have hA := uniform_along_pointwise a id (fun _ => candidatePressure a) (full_auxiliary_uniform_pressure a ha) 0 hx
  have hB := uniform_along_pointwise b id (fun _ => candidatePressure b) (full_auxiliary_uniform_pressure b hb) 0 hx
  have hM := uniform_along_pointwise _ id (fun _ => candidatePressure ((1-t)*a+t*b))
    (full_auxiliary_uniform_pressure _ hm) 0 hx
  have hlin : Tendsto (fun n => (1-t)*auxLogPressure 0 n a+t*auxLogPressure 0 n b) atTop
      (nhds ((1-t)*candidatePressure a+t*candidatePressure b)) :=
    (tendsto_const_nhds.mul hA).add (tendsto_const_nhds.mul hB)
  apply le_of_tendsto_of_tendsto hM hlin
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact finite_pressure_convex n hn a b t ht0 ht1

theorem candidate_cost_pressure_convex : ConvexNonnegative candidateCostPressure := by
  intro a b t ha hb ht0 ht1
  have h := candidate_pressure_convex a b t ha hb ht0 ht1
  unfold candidateCostPressure
  nlinarith

theorem mean_reference_le_one : meanReference≤1 := by
  have hl := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<(2 : ℝ)⁻¹)
  rw [Real.log_inv] at hl
  norm_num at hl
  have hp : (0 : ℝ)<2*Real.log 2 := mul_pos (by norm_num) (Real.log_pos (by norm_num))
  unfold meanReference
  apply (div_le_one hp).mpr
  linarith

theorem finite_pressure_mono (n : ℕ) (hn : 1≤n) (a b : ℝ) (hab : a≤b) :
    auxLogPressure 0 n a≤auxLogPressure 0 n b := by
  have hx : ClosedPhase (0 : ℝ) := by constructor <;> norm_num
  have := aux_words_finite 0 n hx
  let := Fintype.ofFinite (AuxWords 0 n)
  have hp : auxPartition 0 n a≤auxPartition 0 n b := by
    rw [aux_partition_eq_sum 0 n a (by omega),aux_partition_eq_sum 0 n b (by omega)]
    apply Finset.sum_le_sum
    intro w _
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hab
      (normalized_reward_law 0 n w.val hx w.property).2.2.1)
  have hlog := Real.log_le_log (aux_partition_positive 0 n hx a) hp
  exact div_le_div_of_nonneg_right hlog (Nat.cast_nonneg n)

theorem candidate_pressure_mono (a b : ℝ) (ha : 0≤a) (hab : a≤b) :
    candidatePressure a≤candidatePressure b := by
  have hx : ClosedPhase (0 : ℝ) := by constructor <;> norm_num
  have hA := uniform_along_pointwise a id (fun _ => candidatePressure a) (full_auxiliary_uniform_pressure a ha) 0 hx
  have hB := uniform_along_pointwise b id (fun _ => candidatePressure b) (full_auxiliary_uniform_pressure b (ha.trans hab)) 0 hx
  apply le_of_tendsto_of_tendsto hA hB
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact finite_pressure_mono n hn a b hab

def zeroDepth (n : ℕ) : Path n := fun _ => 0

theorem zero_depth_legal (x : ℝ) (n : ℕ) : PathLegal x n (zeroDepth n) := by
  refine ⟨rfl,rfl,fun i => ?_⟩
  have hi := phase_increment_alphabet x i.val
  simp only [zeroDepth,Fin.val_zero]
  omega

theorem zero_depth_cost (x : ℝ) (n : ℕ) : pathCost x n (zeroDepth n)=0 := by
  simp [pathCost,zeroDepth]

theorem path_cost_nonneg (x : ℝ) (n : ℕ) (j : Path n) : 0≤pathCost x n j := by
  apply Finset.sum_nonneg
  intro t _
  have hw : 0≤phaseWeight x t.val := by
    unfold phaseWeight
    exact le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  have hp : (2 : ℝ)^(-((j t.castSucc).val : ℤ))≤1 :=
    zpow_le_one_of_nonpos₀ (by norm_num) (neg_nonpos.mpr (Nat.cast_nonneg _))
  exact mul_nonneg hw (sub_nonneg.mpr hp)

theorem cost_partition_lower_one (x : ℝ) (n : ℕ) (lam : ℝ) : 1≤costPartition x n lam := by
  classical
  unfold costPartition
  calc
    1 = (if PathLegal x n (zeroDepth n) then Real.exp (-lam*pathCost x n (zeroDepth n)) else 0) := by
      rw [ite_eq_left (zero_depth_legal x n),zero_depth_cost]
      simp
    _ ≤ ∑ j : Path n,if PathLegal x n j then Real.exp (-lam*pathCost x n j) else 0 := by
      apply Finset.single_le_sum (f := fun j : Path n => if PathLegal x n j then Real.exp (-lam*pathCost x n j) else 0)
        (s := Finset.univ) (a := zeroDepth n)
      · intro j _
        split_ifs <;> positivity
      · exact Finset.mem_univ _

theorem cost_partition_mono (x : ℝ) (n : ℕ) (a b : ℝ) (hab : a≤b) :
    costPartition x n b≤costPartition x n a := by
  classical
  unfold costPartition
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : PathLegal x n j
  · simp only [hj,ite_true]
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right hab (path_cost_nonneg x n j)
    linarith
  · simp only [hj,ite_false,le_refl]

theorem finite_cost_pressure_nonneg (x : ℝ) (n : ℕ) (lam : ℝ) : 0≤costLogPressure x lam n :=
  div_nonneg (Real.log_nonneg (cost_partition_lower_one x n lam)) (Nat.cast_nonneg _)

theorem finite_cost_pressure_mono (x : ℝ) (n : ℕ) (a b : ℝ) (hab : a≤b) :
    costLogPressure x b n≤costLogPressure x a n := by
  have hp : 0<costPartition x n b := lt_of_lt_of_le (by norm_num) (cost_partition_lower_one x n b)
  exact div_le_div_of_nonneg_right (Real.log_le_log hp (cost_partition_mono x n a b hab)) (Nat.cast_nonneg _)

theorem cost_pressure_tendsto (lam : ℝ) (hl : 0≤lam) :
    Tendsto (fun n : ℕ => costLogPressure 0 lam n) atTop (nhds (candidateCostPressure lam)) := by
  apply Metric.tendsto_atTop.mpr
  intro eps heps
  obtain ⟨N,_,hN⟩ := cost_pressure_composition.1 lam hl eps heps
  refine ⟨N,fun n hn => ?_⟩
  simpa only [Real.dist_eq] using hN n hn 0 (le_refl _) (by norm_num)

theorem candidate_cost_nonneg (lam : ℝ) (hl : 0≤lam) : 0≤candidateCostPressure lam := by
  apply le_of_tendsto_of_tendsto tendsto_const_nhds (cost_pressure_tendsto lam hl)
  exact Eventually.of_forall (fun n => finite_cost_pressure_nonneg 0 n lam)

theorem candidate_cost_mono (a b : ℝ) (ha : 0≤a) (hab : a≤b) :
    candidateCostPressure b≤candidateCostPressure a := by
  apply le_of_tendsto_of_tendsto (cost_pressure_tendsto b (ha.trans hab)) (cost_pressure_tendsto a ha)
  exact Eventually.of_forall (fun n => finite_cost_pressure_mono 0 n a b hab)

theorem candidate_cost_upper (lam : ℝ) (hl : 0≤lam) : candidateCostPressure lam≤candidatePressure 0 := by
  simpa only [candidateCostPressure,zero_mul,sub_zero] using candidate_cost_mono 0 lam (le_refl _) hl

theorem candidate_cost_lipschitz_ordered (a b : ℝ) (ha : 0≤a) (hab : a≤b) :
    |candidateCostPressure a-candidateCostPressure b|≤|a-b| := by
  have hP := candidate_pressure_mono a b ha hab
  have hC := candidate_cost_mono a b ha hab
  rw [abs_of_nonneg (sub_nonneg.mpr hC),abs_of_nonpos (sub_nonpos.mpr hab)]
  unfold candidateCostPressure
  have hM := mean_reference_le_one
  nlinarith [mul_le_mul_of_nonneg_right hM (sub_nonneg.mpr hab)]

theorem candidate_cost_lipschitz (a b : ℝ) (ha : 0≤a) (hb : 0≤b) :
    |candidateCostPressure a-candidateCostPressure b|≤|a-b| := by
  by_cases hab : a≤b
  · exact candidate_cost_lipschitz_ordered a b ha hab
  · have h := candidate_cost_lipschitz_ordered b a hb (le_of_not_ge hab)
    simpa only [abs_sub_comm (candidateCostPressure b) (candidateCostPressure a),abs_sub_comm b a] using h

theorem candidate_qualitative_pressure : CandidateQualitativePressure := by
  refine ⟨candidate_pressure_convex,candidate_cost_pressure_convex,?_,?_,candidate_cost_lipschitz⟩
  · intro lam hl
    exact ⟨candidate_cost_nonneg lam hl,candidate_cost_upper lam hl⟩
  · intro a b ha hab
    exact ⟨candidate_pressure_mono a b ha hab,candidate_cost_mono a b ha hab⟩

end ExternalBridgePressureAnalyticQualitative
