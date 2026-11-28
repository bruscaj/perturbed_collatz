import WordFiniteComparison
import WordClampCount
import WordCompletion
import WordTruncationFiber

/-! Finite injection/fiber partition comparisons, with literal maps and bounds. -/
namespace ExternalBridgePressureWordPartitionTransport
open ExternalFiniteBridgeDraft ExternalBridgePressureDraft ExternalBridgePressureWordDraft
open ExternalBridgePressureWordArithmetic ExternalBridgePressureWordReward ExternalBridgePressureWordPopulation
open ExternalBridgePressureWordFiniteComparison ExternalBridgePressureWordPhaseUp
open ExternalBridgePressureWordClamp ExternalBridgePressureWordClampCount
open ExternalBridgePressureWordCompletion ExternalBridgePressureWordTruncation ExternalBridgePressureWordTruncationFiber
open scoped BigOperators

 theorem finite_sum_injection {α β : Type*} [Fintype α] [Fintype β]
    (e : α → β) (he : Function.Injective e) (f : α → ℝ) (g : β → ℝ)
    (hg : ∀ b,0≤g b) (hf : ∀ a,f a≤g (e a)) : ∑ a,f a ≤ ∑ b,g b := by
  classical
  apply Finset.sum_le_sum_of_injOn e
  · exact he.injOn
  · intro _ _
    exact Finset.mem_univ _
  · intro a _
    exact hf a
  · intro b _ _
    exact hg b

theorem sum_product_constant {α β : Type*} [Fintype α] [Fintype β]
    (A : ℝ) (f : α → ℝ) :
    (∑ p : α×β,A*f p.1) = (Fintype.card β : ℝ)*A*∑ a,f a := by
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem partition_upper_via_code {γ : Type*} [Fintype γ]
    (x y : ℝ) (n k : ℕ) (hx : ClosedPhase x) (hy : ClosedPhase y)
    (hn : 0<n) (hk : 0<k) (lam L : ℝ) (hl : 0≤lam)
    (code : AuxWords y k → AuxWords x n × γ) (hi : Function.Injective code)
    (hR : ∀ w,auxReward y k w.val ≤ auxReward x n (code w).1.val+L) :
    auxPartition y k lam ≤ (Fintype.card γ : ℝ)*Real.exp (lam*L)*auxPartition x n lam := by
  have := aux_words_finite x n hx
  have := aux_words_finite y k hy
  let := Fintype.ofFinite (AuxWords x n)
  let := Fintype.ofFinite (AuxWords y k)
  rw [aux_partition_eq_sum y k lam hk,aux_partition_eq_sum x n lam hn]
  calc
    (∑ w : AuxWords y k,Real.exp (lam*auxReward y k w.val)) ≤
        ∑ p : AuxWords x n × γ,Real.exp (lam*L)*Real.exp (lam*auxReward x n p.1.val) := by
      apply finite_sum_injection code hi
      · intro p
        positivity
      · intro w
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have h := mul_le_mul_of_nonneg_left (hR w) hl
        nlinarith
    _ = _ := sum_product_constant (α := AuxWords x n) (β := γ)
      (Real.exp (lam*L)) (fun w => Real.exp (lam*auxReward x n w.val))

theorem partition_lower_via_injection
    (x y : ℝ) (n k : ℕ) (hx : ClosedPhase x) (hy : ClosedPhase y)
    (hn : 0<n) (hk : 0<k) (lam L : ℝ) (hl : 0≤lam)
    (e : AuxWords x n → AuxWords y k) (hi : Function.Injective e)
    (hR : ∀ w,auxReward x n w.val-L ≤ auxReward y k (e w).val) :
    Real.exp (-lam*L)*auxPartition x n lam ≤ auxPartition y k lam := by
  have := aux_words_finite x n hx
  have := aux_words_finite y k hy
  let := Fintype.ofFinite (AuxWords x n)
  let := Fintype.ofFinite (AuxWords y k)
  rw [aux_partition_eq_sum x n lam hn,aux_partition_eq_sum y k lam hk,Finset.mul_sum]
  apply finite_sum_injection e hi
  · intro w
    exact le_of_lt (Real.exp_pos _)
  · intro w
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left (hR w) hl
    nlinarith

noncomputable def completionMap (x : ℝ) (n m : ℕ) (hx : ClosedPhase x) (hn : 1≤n) :
    AuxWords x n → AuxWords x (n+m) := fun w =>
  ⟨completeWord x n m w.val,complete_word_legal x n m hx hn w.val w.property⟩

theorem completion_map_injective (x : ℝ) (n m : ℕ) (hx : ClosedPhase x) (hn : 1≤n) :
    Function.Injective (completionMap x n m hx hn) := by
  intro a b h
  exact complete_word_injective x n m hx hn (congrArg Subtype.val h)

noncomputable def truncationMap (x : ℝ) (n m : ℕ) (hn : 1≤n) :
    AuxWords x (n+m) → AuxWords x n × (Fin (m+1) → Fin (2*(n+m)+1)) := fun w =>
  (⟨truncateWord x n m w.val,truncate_word_legal x n m w.val w.property hn⟩,boundedTailRecord n m w.val)

theorem truncation_map_injective (x : ℝ) (n m : ℕ) (hx : ClosedPhase x) (hn : 1≤n) :
    Function.Injective (truncationMap x n m hn) := by
  intro a b h
  apply truncation_code_injective x n m hx hn
  exact congrArg (fun p => (p.1.val,p.2)) h

theorem fixed_shift_partition_lower (x : ℝ) (n m : ℕ) (hx : ClosedPhase x) (hn : 1≤n)
    (lam : ℝ) (hl : 0≤lam) : auxPartition x n lam ≤ auxPartition x (n+m) lam := by
  have h := partition_lower_via_injection x x n (n+m) hx hx (by omega) (by omega) lam 0 hl
    (completionMap x n m hx hn) (completion_map_injective x n m hx hn)
    (fun w => by simpa only [sub_zero,completionMap] using (completion_transport x n m hx hn).2 w.val w.property |>.2.2.2.2)
  simpa only [mul_zero,Real.exp_zero,one_mul] using h

theorem fixed_shift_partition_upper (x : ℝ) (n m : ℕ) (hx : ClosedPhase x) (hn : 1≤n)
    (lam : ℝ) (hl : 0≤lam) : auxPartition x (n+m) lam ≤
      ((2*(n+m)+1 : ℕ) : ℝ)^(m+1)*Real.exp (lam*(m : ℝ))*auxPartition x n lam := by
  have h := partition_upper_via_code x x n (n+m) hx hx (by omega) (by omega) lam (m : ℝ) hl
    (truncationMap x n m hn) (truncation_map_injective x n m hx hn)
    (fun w => (truncation_transport x n m hx hn w.val w.property).2.2.2.2.2)
  simpa only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow] using h

theorem fixed_shift_comparison : FixedShiftComparison := by
  intro x n m lam hx hn hl
  have hlo := fixed_shift_partition_lower x n m hx hn lam hl
  have hhi := fixed_shift_partition_upper x n m hx hn lam hl
  refine ⟨hlo,hhi,?_,?_⟩
  · have h := Real.log_le_log (aux_partition_positive x n hx lam) hlo
    unfold auxLogPartition
    linarith
  · have h := Real.log_le_log (aux_partition_positive x (n+m) hx lam) hhi
    have hp : (0 : ℝ)<((2*(n+m)+1 : ℕ) : ℝ) := by positivity
    rw [Real.log_mul (mul_ne_zero (ne_of_gt (pow_pos hp _)) (ne_of_gt (Real.exp_pos _)))
      (ne_of_gt (aux_partition_positive x n hx lam)),
      Real.log_mul (ne_of_gt (pow_pos hp _)) (ne_of_gt (Real.exp_pos _)),Real.log_pow,Real.log_exp] at h
    unfold auxLogPartition
    linarith

noncomputable def phaseUpMap (x y : ℝ) (n : ℕ) (hxy : OrderedPhases x y) (hn : 1≤n) :
    AuxWords x n → AuxWords y n := fun w =>
  ⟨phaseUp x y n w.val,((phase_up_transport x y n hxy hn).2 w.val w.property).1⟩

theorem phase_up_map_injective (x y : ℝ) (n : ℕ) (hxy : OrderedPhases x y) (hn : 1≤n) :
    Function.Injective (phaseUpMap x y n hxy hn) := by
  intro a b h
  apply Subtype.ext
  exact phase_up_injective x y n (congrArg Subtype.val h)

noncomputable def clampMap (x y : ℝ) (n : ℕ) (hxy : OrderedPhases x y) (hn : 1≤n) :
    AuxWords y n → AuxWords x n × (CapDifference x y n → Bool) := fun w =>
  (⟨clampWord x n w.val,(clamp_word_transport x y n hxy hn w.val w.property).2.2⟩,
    clampBits x y n w.val)

theorem clamp_map_injective (x y : ℝ) (n : ℕ) (hxy : OrderedPhases x y) (hn : 1≤n) :
    Function.Injective (clampMap x y n hxy hn) := by
  intro a b h
  apply clamp_code_injective x y n hxy
  exact congrArg (fun p => (p.1.val,p.2)) h

theorem phase_up_reward_lower (x y : ℝ) (n : ℕ) (hxy : OrderedPhases x y) (hn : 1≤n)
    (w : AuxWords x n) :
    auxReward x n w.val-Real.log 2*(y-x)*(n : ℝ) ≤ auxReward y n (phaseUpMap x y n hxy hn w).val := by
  have hr := (normalized_reward_law x n w.val hxy.1 w.property).2.2
  have ha : 0≤Real.log 2*(y-x) := mul_nonneg
    (le_of_lt (Real.log_pos (by norm_num))) (sub_nonneg.mpr hxy.2.2)
  have hq : 1-Real.log 2*(y-x) ≤ Real.rpow 2 (-(y-x)) := by
    have h := Real.add_one_le_exp (-Real.log 2*(y-x))
    have he : Real.rpow 2 (-(y-x)) = Real.exp (-Real.log 2*(y-x)) := by
      simp only [Real.rpow_eq_pow]
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ)<2)]
      congr 1
      ring
    rw [he]
    linarith
  have h1 := mul_le_mul_of_nonneg_right hq hr.1
  have h2 := mul_le_mul_of_nonneg_left hr.2 ha
  change auxReward x n w.val-Real.log 2*(y-x)*(n : ℝ) ≤ auxReward y n (phaseUp x y n w.val)
  rw [((phase_up_injection_reward x y n hxy hn).2 w.val w.property).2]
  nlinarith

theorem phase_partition_lower (x y : ℝ) (n : ℕ) (hxy : OrderedPhases x y) (hn : 1≤n)
    (lam : ℝ) (hl : 0≤lam) :
    Real.exp (-lam*Real.log 2*(y-x)*(n : ℝ))*auxPartition x n lam ≤ auxPartition y n lam := by
  have h := partition_lower_via_injection x y n n hxy.1 hxy.2.1 (by omega) (by omega) lam
    (Real.log 2*(y-x)*(n : ℝ)) hl (phaseUpMap x y n hxy hn)
    (phase_up_map_injective x y n hxy hn) (phase_up_reward_lower x y n hxy hn)
  have he : -lam*(Real.log 2*(y-x)*(n : ℝ)) = -lam*Real.log 2*(y-x)*(n : ℝ) := by ring
  simpa only [he] using h

theorem phase_partition_upper (x y : ℝ) (n : ℕ) (hxy : OrderedPhases x y) (hn : 1≤n)
    (lam : ℝ) (hl : 0≤lam) :
    auxPartition y n lam ≤ (2 : ℝ)^Dcount x y n * Real.exp (lam*(Dcount x y n : ℝ))*auxPartition x n lam := by
  classical
  have h := partition_upper_via_code x y n n hxy.1 hxy.2.1 (by omega) (by omega) lam
    (Dcount x y n : ℝ) hl (clampMap x y n hxy hn) (clamp_map_injective x y n hxy hn)
    (fun w => clamp_reward_bound x y n hxy hn w.val w.property)
  have hc : (Fintype.card (CapDifference x y n → Bool) : ℝ) = (2 : ℝ)^Dcount x y n := by
    exact_mod_cast (show Fintype.card (CapDifference x y n → Bool) = 2^Dcount x y n by
      rw [← Nat.card_eq_fintype_card]
      exact clamp_bits_card x y n)
  rw [hc] at h
  exact h

theorem phase_log_comparison : PhaseLogComparison := by
  intro x y n lam hxy hn hl
  have hlo := phase_partition_lower x y n hxy hn lam hl
  have hhi := phase_partition_upper x y n hxy hn lam hl
  refine ⟨hlo,hhi,?_,?_⟩
  · have hp : 0<Real.exp (-lam*Real.log 2*(y-x)*(n : ℝ))*auxPartition x n lam :=
      mul_pos (Real.exp_pos _) (aux_partition_positive x n hxy.1 lam)
    have h := Real.log_le_log hp hlo
    rw [Real.log_mul (ne_of_gt (Real.exp_pos _))
      (ne_of_gt (aux_partition_positive x n hxy.1 lam)),Real.log_exp] at h
    unfold auxLogPartition
    linarith
  · have h := Real.log_le_log (aux_partition_positive y n hxy.2.1 lam) hhi
    have hp : (0 : ℝ)<2 := by norm_num
    rw [Real.log_mul (mul_ne_zero (ne_of_gt (pow_pos hp _)) (ne_of_gt (Real.exp_pos _)))
      (ne_of_gt (aux_partition_positive x n hxy.1 lam)),
      Real.log_mul (ne_of_gt (pow_pos hp _)) (ne_of_gt (Real.exp_pos _)),Real.log_pow,Real.log_exp] at h
    unfold auxLogPartition
    nlinarith

end ExternalBridgePressureWordPartitionTransport
