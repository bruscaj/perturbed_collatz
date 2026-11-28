import UnrestrictedRotation
import BridgeEncoding
import BridgeArithmetic
import BridgeRewards

namespace ExternalM4UnrestrictedCanonical
open ExternalM4UnrestrictedDraft ExternalFiniteBridgeDraft
open ExternalFiniteBridgeEncoding ExternalFiniteBridgeArithmetic ExternalFiniteBridgeRewards
open ExternalM4UnrestrictedRotation
open scoped BigOperators
noncomputable section

 theorem canonical_zero (r : ℕ) : canonicalPrefix r 0 = 0 := by
  simp only [canonicalPrefix, literalCap, Fin.val_zero, Nat.cast_zero, zero_mul, zero_add]
  have hd := defect_bounds slope r
  exact Int.floor_eq_zero_iff.mpr (by simpa using hd)

theorem canonical_last (r : ℕ) :
    canonicalPrefix r (Fin.last r) = Int.ceil ((r : ℝ) * slope) := by
  change Int.floor ((r : ℝ) * slope + defect slope r) = _
  simp only [defect, add_sub_cancel]
  exact Int.floor_intCast _

theorem cap_step_bounds (r t : ℕ) :
    literalCap slope r t + 1 ≤ literalCap slope r (t+1) ∧
    literalCap slope r (t+1) ≤ literalCap slope r t + 2 := by
  have hl : (t : ℝ)*slope+defect slope r+1 ≤ ((t+1 : ℕ) : ℝ)*slope+defect slope r := by
    push_cast
    linarith [source_slope_facts.1]
  have hu : ((t+1 : ℕ) : ℝ)*slope+defect slope r ≤ (t : ℝ)*slope+defect slope r+2 := by
    push_cast
    linarith [source_slope_facts.2.1]
  constructor
  · simpa [literalCap, Int.floor_add_one] using Int.floor_mono hl
  · simpa [literalCap, Int.floor_add_ofNat] using Int.floor_mono hu

theorem canonical_positive_prefix (r : ℕ) : PositivePrefix r (canonicalPrefix r) :=
  ⟨canonical_zero r, fun i => (cap_step_bounds r i.val).1⟩

theorem canonical_prefix_law : CanonicalPrefixLaw := by
  intro r
  exact ⟨wordPrefix_prefixLetters r _ (canonical_positive_prefix r), canonical_zero r, canonical_last r⟩

theorem canonical_source (r : ℕ) (hr : 0 < r) : SourceWord slope r (canonicalWord r) := by
  refine ⟨hr, prefixLetters_positive r _ (canonical_positive_prefix r), ?_, ?_⟩
  · rw [(canonical_prefix_law r).1]
    exact canonical_last r
  · intro t
    rw [(canonical_prefix_law r).1]
    exact le_rfl

theorem floor_le_cap (r t : ℕ) : floorAt slope t ≤ literalCap slope r t := by
  apply Int.floor_mono
  linarith [(defect_bounds slope r).1]

theorem canonical_reward_ge_reference (r : ℕ) :
    phaseZeroReference slope r ≤ reward r (canonicalWord r) := by
  rw [← reward_real_power]
  unfold phaseZeroReference powerReward
  apply Finset.sum_le_sum
  intro t _
  rw [(canonical_prefix_law r).1]
  simp only [canonicalPrefix, Real.rpow_eq_pow]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  exact sub_le_sub_right (Int.cast_le.mpr (floor_le_cap r t.val)) _

theorem canonical_all_length_word : CanonicalAllLengthWord := by
  intro r hr
  exact ⟨canonical_source r hr, canonical_reward_ge_reference r⟩

theorem canonical_letter_cast (r : ℕ) (i : Fin r) :
    (canonicalWord r i : ℤ) = literalCap slope r (i.val+1)-literalCap slope r i.val :=
  prefixLetters_cast r _ (canonical_positive_prefix r) i

theorem canonical_alphabet (r : ℕ) (i : Fin r) : canonicalWord r i = 1 ∨ canonicalWord r i = 2 := by
  have h := cap_step_bounds r i.val
  have hi := canonical_letter_cast r i
  omega

theorem canonical_no_eleven (r : ℕ) (i : Fin r) (hi : i.val+1 < r) :
    ¬ (canonicalWord r i = 1 ∧ canonicalWord r ⟨i.val+1,hi⟩ = 1) := by
  rintro ⟨ha,hb⟩
  have h1 := canonical_letter_cast r i
  have h2 := canonical_letter_cast r ⟨i.val+1,hi⟩
  rw [ha] at h1
  rw [hb] at h2
  change (1 : ℤ) = literalCap slope r (i.val+1+1)-literalCap slope r (i.val+1) at h2
  have hx : (i.val : ℝ)*slope+defect slope r+3 ≤
      ((i.val+2 : ℕ) : ℝ)*slope+defect slope r := by
    push_cast
    nlinarith [slope_bounds.1]
  have he : i.val+1+1 = i.val+2 := by omega
  rw [he] at h2
  have h3 : literalCap slope r i.val+3 ≤ literalCap slope r (i.val+2) := by
    simpa [literalCap, Int.floor_add_ofNat] using Int.floor_mono hx
  omega

theorem canonical_sum (r : ℕ) :
    (∑ i : Fin r, canonicalWord r i) = (Int.ceil ((r : ℝ)*slope)).toNat := by
  have hi : ((∑ i : Fin r, canonicalWord r i : ℕ) : ℤ) = Int.ceil ((r : ℝ)*slope) := by
    have hh := congrFun (canonical_prefix_law r).1 (Fin.last r)
    rw [canonical_last] at hh
    simpa [wordPrefix] using hh
  exact_mod_cast congrArg Int.toNat hi

theorem canonical_ones_count (r : ℕ) :
    Nat.card {i : Fin r // canonicalWord r i = 1} =
      2*r-(Int.ceil ((r : ℝ)*slope)).toNat := by
  classical
  have hterm (i : Fin r) : canonicalWord r i + (if canonicalWord r i = 1 then 1 else 0) = 2 := by
    rcases canonical_alphabet r i with h | h <;> simp [h]
  have hs : (∑ i : Fin r, canonicalWord r i) +
      (∑ i : Fin r, if canonicalWord r i = 1 then 1 else 0) = 2*r := by
    rw [← Finset.sum_add_distrib]
    simp only [hterm]
    simp [Nat.mul_comm]
  have hc : (∑ i : Fin r, if canonicalWord r i = 1 then 1 else 0) =
      Nat.card {i : Fin r // canonicalWord r i = 1} := by
    simp [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [canonical_sum, hc] at hs
  omega

theorem canonical_many_ones (r : ℕ) : r/3 ≤ Nat.card {i : Fin r // canonicalWord r i = 1} := by
  have hq : 3*(r/3) ≤ r := by omega
  have hx : (r : ℝ)*slope ≤ ((2*r : ℕ) : ℝ)-(r/3 : ℕ) := by
    have hqr : (3 : ℝ)*(r/3 : ℕ) ≤ (r : ℝ) := by exact_mod_cast hq
    have hr : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
    have hm := mul_le_mul_of_nonneg_left (le_of_lt slope_bounds.2) hr
    push_cast
    nlinarith
  have hi : Int.ceil ((r : ℝ)*slope) ≤ (2*r : ℕ)-(r/3 : ℕ) := by
    apply Int.ceil_le.mpr
    exact_mod_cast hx
  have hn : 0 ≤ Int.ceil ((r : ℝ)*slope) := by
    apply Int.ceil_nonneg
    positivity [source_slope_facts.1]
  have hc := canonical_ones_count r
  omega

def previousIndex {r : ℕ} (i : Fin r) : Fin r :=
  ⟨i.val-1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩

theorem canonical_predecessor_site (r : ℕ) (i : Fin r) (hi : canonicalWord r i = 1)
    (hz : i.val ≠ 0) : TwentyOneSite r (canonicalWord r) (previousIndex i) := by
  have he : (previousIndex i).val+1 = i.val := by dsimp [previousIndex]; omega
  have hb : (previousIndex i).val+1 < r := by rw [he]; exact i.isLt
  have hnext : (⟨(previousIndex i).val+1,hb⟩ : Fin r) = i := Fin.ext he
  refine ⟨hb, ?_, by rw [hnext]; exact hi⟩
  rcases canonical_alphabet r (previousIndex i) with h | h
  · exact False.elim (canonical_no_eleven r _ hb ⟨h, by rw [hnext]; exact hi⟩)
  · exact h

theorem canonical_site_count (r : ℕ) :
    r/3-1 ≤ Nat.card {i : Fin r // TwentyOneSite r (canonicalWord r) i} := by
  classical
  let f : {i : Fin r // canonicalWord r i = 1} →
      Option {j : Fin r // TwentyOneSite r (canonicalWord r) j} := fun i =>
    if hz : i.val.val = 0 then none else
      some ⟨previousIndex i.val, canonical_predecessor_site r i.val i.property hz⟩
  have hf : Function.Injective f := by
    intro i j hij
    by_cases hi : i.val.val = 0
    · by_cases hj : j.val.val = 0
      · apply Subtype.ext
        apply Fin.ext
        omega
      · simp [f, hi, hj] at hij
    · by_cases hj : j.val.val = 0
      · simp [f, hi, hj] at hij
      · have he : previousIndex i.val = previousIndex j.val := by
          simpa [f, hi, hj] using hij
        have hv := congrArg Fin.val he
        dsimp [previousIndex] at hv
        apply Subtype.ext
        apply Fin.ext
        omega
  have hc : Nat.card {i : Fin r // canonicalWord r i = 1} ≤
      Nat.card {i : Fin r // TwentyOneSite r (canonicalWord r) i}+1 := by
    simpa [Nat.card_eq_fintype_card] using Fintype.card_le_of_injective f hf
  have hh := canonical_many_ones r
  omega

theorem canonical_alphabet_and_sites : CanonicalAlphabetAndSites := by
  intro r _hr
  exact ⟨canonical_alphabet r, canonical_no_eleven r, canonical_ones_count r, canonical_site_count r⟩

theorem distinct_sites_separated (r : ℕ) (w : Word r) (i j : Fin r)
    (hi : TwentyOneSite r w i) (hj : TwentyOneSite r w j) (hne : i ≠ j) :
    i.val+1 < j.val ∨ j.val+1 < i.val := by
  rcases hi with ⟨hi,hi2,hi1⟩
  rcases hj with ⟨hj,hj2,hj1⟩
  have hv : i.val ≠ j.val := fun h => hne (Fin.ext h)
  by_contra hn
  have he : i.val+1 = j.val ∨ j.val+1 = i.val := by omega
  rcases he with he | he
  · have hh : (⟨i.val+1,hi⟩ : Fin r) = j := Fin.ext he
    rw [hh, hj2] at hi1
    omega
  · have hh : (⟨j.val+1,hj⟩ : Fin r) = i := Fin.ext he
    rw [hh, hi2] at hj1
    omega

theorem many_disjoint_canonical_sites : ManyDisjointCanonicalSites := by
  classical
  intro r hr
  let T : Finset (Fin r) := Finset.univ.filter (TwentyOneSite r (canonicalWord r))
  have hc : T.card = Nat.card {i : Fin r // TwentyOneSite r (canonicalWord r) i} := by
    simp [T, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hsize : r/8 ≤ T.card := by
    have hh := canonical_site_count r
    rw [← hc] at hh
    omega
  obtain ⟨S,hST,hS⟩ := Finset.exists_subset_card_eq hsize
  refine ⟨S, ⟨?_, ?_⟩, hS⟩
  · intro i hi
    exact (Finset.mem_filter.mp (hST hi)).2
  · intro i hi j hj hne
    exact distinct_sites_separated r _ i j
      (Finset.mem_filter.mp (hST hi)).2 (Finset.mem_filter.mp (hST hj)).2 hne

theorem canonical_loss_term (r : ℕ) (i : Fin r) :
    0 ≤ (2 : ℝ)^wordPrefix r (canonicalWord r) i.succ/(3 : ℝ)^(i.val+1)/2 ∧
    (2 : ℝ)^wordPrefix r (canonicalWord r) i.succ/(3 : ℝ)^(i.val+1)/2 < 1 := by
  rw [congrFun (canonical_prefix_law r).1 i.succ]
  change 0 ≤ (2 : ℝ)^literalCap slope r (i.val+1)/(3 : ℝ)^(i.val+1)/2 ∧
    (2 : ℝ)^literalCap slope r (i.val+1)/(3 : ℝ)^(i.val+1)/2 < 1
  rw [← reward_term_real_power]
  have hf := Int.floor_le (((i.val+1 : ℕ) : ℝ)*slope+defect slope r)
  have he : ((literalCap slope r (i.val+1) : ℤ) : ℝ)-((i.val+1 : ℕ) : ℝ)*slope < 1 := by
    have hd := (defect_bounds slope r).2
    change ((literalCap slope r (i.val+1) : ℤ) : ℝ) ≤ _ at hf
    linarith
  have hp : Real.rpow 2 (((literalCap slope r (i.val+1) : ℤ) : ℝ)-((i.val+1 : ℕ) : ℝ)*slope) < 2 := by
    calc
      _ < Real.rpow 2 1 := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) he
      _ = 2 := by norm_num
  constructor
  · exact div_nonneg (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)) (by norm_num)
  · linarith

theorem canonical_swap_loss_bound : CanonicalSwapLossBound := by
  intro r S _hS
  have hlo : 0 ≤ swapLoss r (canonicalWord r) S :=
    Finset.sum_nonneg (fun i _ => (canonical_loss_term r i).1)
  have hhi : swapLoss r (canonicalWord r) S ≤ (S.card : ℝ) := by
    calc
      _ ≤ ∑ _i ∈ S, (1 : ℝ) := Finset.sum_le_sum (fun i _ => le_of_lt (canonical_loss_term r i).2)
      _ = _ := by simp
  refine ⟨hlo,hhi,?_⟩
  intro hpos
  calc
    _ < ∑ _i ∈ S, (1 : ℝ) :=
      Finset.sum_lt_sum_of_nonempty (Finset.card_pos.mp hpos) (fun i _ => (canonical_loss_term r i).2)
    _ = _ := by simp

theorem canonical_excess_term (r : ℕ) (hdelta : (1/2 : ℝ) ≤ defect slope r) (t : Fin r) :
    (if (1/2 : ℝ) ≤ Int.fract ((t.val : ℝ)*slope) then (1/2 : ℝ) else 0) ≤
      Real.rpow 2 (((literalCap slope r t.val : ℤ) : ℝ)-(t.val : ℝ)*slope)-
      Real.rpow 2 (((floorAt slope t.val : ℤ) : ℝ)-(t.val : ℝ)*slope) := by
  have hbase : Real.rpow 2 (((floorAt slope t.val : ℤ) : ℝ)-(t.val : ℝ)*slope) ≤
      Real.rpow 2 (((literalCap slope r t.val : ℤ) : ℝ)-(t.val : ℝ)*slope) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    exact sub_le_sub_right (Int.cast_le.mpr (floor_le_cap r t.val)) _
  split_ifs with hh
  · have hstep : floorAt slope t.val+1 ≤ literalCap slope r t.val := by
      apply Int.le_floor.mpr
      simp only [Int.cast_add, Int.cast_one]
      have hp : (1/2 : ℝ) ≤ (t.val : ℝ)*slope-(floorAt slope t.val : ℤ) := by
        simpa only [Int.fract, floorAt] using hh
      linarith
    have hfrac := Int.fract_lt_one ((t.val : ℝ)*slope)
    have hlower : -(1 : ℝ) ≤ ((floorAt slope t.val : ℤ) : ℝ)-(t.val : ℝ)*slope := by
      simp only [Int.fract] at hfrac
      dsimp only [floorAt]
      linarith
    have hb : (1/2 : ℝ) ≤ Real.rpow 2 (((floorAt slope t.val : ℤ) : ℝ)-(t.val : ℝ)*slope) := by
      calc
        _ = Real.rpow 2 (-1 : ℝ) := by norm_num
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hlower
    have hscale : Real.rpow 2 ((((floorAt slope t.val : ℤ) : ℝ)-(t.val : ℝ)*slope)+1) =
        2*Real.rpow 2 (((floorAt slope t.val : ℤ) : ℝ)-(t.val : ℝ)*slope) := by
      simp only [Real.rpow_eq_pow]
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      norm_num
      ring
    have hm : Real.rpow 2 ((((floorAt slope t.val : ℤ) : ℝ)-(t.val : ℝ)*slope)+1) ≤
        Real.rpow 2 (((literalCap slope r t.val : ℤ) : ℝ)-(t.val : ℝ)*slope) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hc : ((floorAt slope t.val+1 : ℤ) : ℝ) ≤ ((literalCap slope r t.val : ℤ) : ℝ) := Int.cast_le.mpr hstep
      push_cast at hc
      linarith
    rw [hscale] at hm
    linarith
  · linarith

theorem canonical_reward_budget : CanonicalRewardBudget := by
  classical
  intro r hdelta
  have hsum := Finset.sum_le_sum (fun (t : Fin r) (_ht : t ∈ Finset.univ) => canonical_excess_term r hdelta t)
  let H : Finset (Fin r) := Finset.univ.filter
    (fun t => (1/2 : ℝ) ≤ Int.fract ((t.val : ℝ)*slope))
  have hc : highPhaseCount r = H.card := by
    simp [highPhaseCount, H, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hleft : (∑ t : Fin r, if (1/2 : ℝ) ≤ Int.fract ((t.val : ℝ)*slope) then (1/2 : ℝ) else 0) =
      (highPhaseCount r : ℝ)/2 := by
    rw [hc]
    have hf : (∑ t : Fin r, if (1/2 : ℝ) ≤ Int.fract ((t.val : ℝ)*slope) then (1/2 : ℝ) else 0) =
        ∑ _t ∈ H, (1/2 : ℝ) := by simp only [H, Finset.sum_filter]
    rw [hf]
    simp [div_eq_mul_inv]
  rw [hleft, Finset.sum_sub_distrib] at hsum
  have hright : (∑ t : Fin r, Real.rpow 2 (((literalCap slope r t.val : ℤ) : ℝ)-(t.val : ℝ)*slope)) =
      reward r (canonicalWord r) := by
    rw [← reward_real_power]
    simp only [powerReward, (canonical_prefix_law r).1, canonicalPrefix, Fin.val_castSucc]
  rw [hright] at hsum
  change (highPhaseCount r : ℝ)/2 ≤ reward r (canonicalWord r)-phaseZeroReference slope r at hsum
  have hh : ((r/3 : ℕ) : ℝ) ≤ (highPhaseCount r : ℝ) := by exact_mod_cast high_phase_count_lower r
  linarith

end
end ExternalM4UnrestrictedCanonical
