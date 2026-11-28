import RateMarkerUpper
import RateSymmetry
import RateMaxMass

/-! Deterministic marker exit events; the stable selector and scalar bounds
remain in their original modules. -/
namespace ExternalO3RateMarkerEvents
open ExternalO3GeneralDraft ExternalO3RateDraft ExternalO3RateMarker
open ExternalO3RateMarkerUpper ExternalO3RateMaxMass
open ExternalO3GeneralWeights ExternalO3GeneralDensity
open scoped BigOperators

/-- Membership, maximality and first-tie minimality characterize the selector. -/
theorem selector_eq_of_properties (h : Depth) (hh : 2 ≤ h.val) (w : Window h)
    (j : Fin h.val) (hj : 0 < j.val)
    (hmax : ∀ i, 0 < i.val → w i ≤ w j)
    (hfirst : ∀ i, 0 < i.val → i.val < j.val → w i < w j) :
    firstFutureMax h w = j := by
  obtain ⟨hp, hm, hf⟩ := marker_selector_law h w hh
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hs := hfirst _ hp hlt
    have hw := hm j hj
    omega
  · have hs := hf j hj hgt
    have hw := hmax _ hp
    omega

/-- At a nonexceptional exit the retained first maximum shifts down one index. -/
theorem exit_selector_shift (n : ℕ) (v : Window ⟨n + 2, by omega⟩)
    (hj : 2 ≤ (firstFutureMax ⟨n + 2, by omega⟩ (prependOne ⟨n + 2, by omega⟩ v)).val)
    (hin : v (Fin.last (n + 1)) ≤
      prependOne ⟨n + 2, by omega⟩ v
        (firstFutureMax ⟨n + 2, by omega⟩ (prependOne ⟨n + 2, by omega⟩ v))) :
    (firstFutureMax ⟨n + 2, by omega⟩ v).val + 1 =
      (firstFutureMax ⟨n + 2, by omega⟩ (prependOne ⟨n + 2, by omega⟩ v)).val := by
  let h : Depth := ⟨n + 2, by omega⟩
  let j := firstFutureMax h (prependOne h v)
  let k : Fin (n + 2) := ⟨j.val - 1, by have ht : j.val < n + 2 := j.isLt; omega⟩
  have hj' : 2 ≤ j.val := hj
  have hkp : 0 < k.val := by dsimp [k]; omega
  have hkv : v k = prependOne h v j := by
    simp only [prependOne, show j.val ≠ 0 from by omega, dite_false]
    rfl
  have hsel := marker_selector_law h (prependOne h v) (by dsimp [h]; omega)
  have hmap (i : Fin (n + 2)) (hi : i.val < n + 1) :
      prependOne h v ⟨i.val + 1, by dsimp [h]; omega⟩ = v i := by
    simp only [prependOne, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
      dite_false, Nat.add_sub_cancel]
    congr 1
  have he : firstFutureMax h v = k := by
    apply selector_eq_of_properties h (by dsimp [h]; omega) v k hkp
    · intro i hi
      by_cases hil : i.val < n + 1
      · have hm := hsel.2.1 ⟨i.val + 1, by dsimp [h]; omega⟩ (by simp)
        rw [hmap i hil, ← hkv] at hm
        exact hm
      · have hie : i = Fin.last (n + 1) := by
          have ht : i.val < n + 2 := i.isLt
          apply Fin.ext
          simp only [Fin.val_last]
          omega
        simpa only [hie, hkv] using hin
    · intro i hi hik
      have hil : i.val < n + 1 := by have ht : j.val < n + 2 := j.isLt; dsimp [k] at hik; omega
      have hs := hsel.2.2 ⟨i.val + 1, by dsimp [h]; omega⟩ (by simp)
        (by change i.val + 1 < j.val; dsimp [k] at hik; omega)
      rw [hmap i hil, ← hkv] at hs
      exact hs
  change (firstFutureMax h v).val + 1 = j.val
  rw [he]
  dsimp [k]
  omega

/-- The selector shift implies an exact one-stride decrease of marker distance. -/
theorem exit_distance_of_shift (n : ℕ) (v : Window ⟨n + 2, by omega⟩)
    (he : (firstFutureMax ⟨n + 2, by omega⟩ v).val + 1 =
      (firstFutureMax ⟨n + 2, by omega⟩ (prependOne ⟨n + 2, by omega⟩ v)).val) :
    markerDistance ⟨n + 2, by omega⟩ v + 1 =
      markerDistance ⟨n + 2, by omega⟩ (prependOne ⟨n + 2, by omega⟩ v) := by
  let h : Depth := ⟨n + 2, by omega⟩
  have hpos := (marker_selector_law h (prependOne h v) (by dsimp [h]; omega)).1
  have hp (i : Fin (n + 1)) : prependOne h v i.succ = v i.castSucc := by
    simp only [prependOne, Fin.val_succ, Nat.add_eq_zero_iff,
      Nat.one_ne_zero, and_false, dite_false, Nat.add_sub_cancel]
    congr 1
  have hz : prependOne h v 0 = 1 := by simp [prependOne]
  have ho : markerDistance h (prependOne h v) = 1 +
      ∑ i : Fin (n + 1),
        if i.val + 1 < (firstFutureMax h (prependOne h v)).val then v i.castSucc else 0 := by
    unfold markerDistance
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, hpos, ite_true, hz, Fin.val_succ, hp]
  have hl : ¬ (n + 1 < (firstFutureMax h v).val) := by
    have ht : (firstFutureMax h (prependOne h v)).val < n + 2 :=
      (firstFutureMax h (prependOne h v)).isLt
    change (firstFutureMax h v).val + 1 = (firstFutureMax h (prependOne h v)).val at he
    omega
  have hn : markerDistance h v =
      ∑ i : Fin (n + 1), if i.val < (firstFutureMax h v).val then v i.castSucc else 0 := by
    unfold markerDistance
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, hl, ite_false, add_zero]
  have hsum : (∑ i : Fin (n + 1),
      if i.val + 1 < (firstFutureMax h (prependOne h v)).val then v i.castSucc else 0) =
      ∑ i : Fin (n + 1), if i.val < (firstFutureMax h v).val then v i.castSucc else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    have ht : i.val + 1 < (firstFutureMax h (prependOne h v)).val ↔
        i.val < (firstFutureMax h v).val := by
      change (firstFutureMax h v).val + 1 = (firstFutureMax h (prependOne h v)).val at he
      omega
    simp only [ht]
  change markerDistance h v + 1 = markerDistance h (prependOne h v)
  rw [ho, hn, hsum]
  omega

/-- Every nonexceptional exit has a strictly negative symbolic gain. -/
theorem exit_gain_neg_of_distance (n k : ℕ) (b : Fin (n + 2) → ℕ)
    (hd : markerDistance ⟨n + 2, by omega⟩ (positiveWindow ⟨n + 2, by omega⟩ b) + 1 =
      markerDistance ⟨n + 2, by omega⟩
        (prependOne ⟨n + 2, by omega⟩ (positiveWindow ⟨n + 2, by omega⟩ b))) :
    gain ⟨n + 2, by omega⟩ (markerCorrection ⟨n + 2, by omega⟩) (.inr (k,b)) < 0 := by
  have hc : (markerDistance ⟨n + 2, by omega⟩ (positiveWindow ⟨n + 2, by omega⟩ b) : ℝ) + 1 =
      (markerDistance ⟨n + 2, by omega⟩
        (prependOne ⟨n + 2, by omega⟩ (positiveWindow ⟨n + 2, by omega⟩ b)) : ℝ) := by
    exact_mod_cast hd
  have hl : Real.log 3 < 3 * Real.log 2 := by
    have hh := Real.log_lt_log (by norm_num : (0 : ℝ) < 3)
      (by norm_num : (3 : ℝ) < 2 ^ 3)
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  have hb : 0 ≤ Real.log 2 := le_of_lt (Real.log_pos (by norm_num))
  have hk := mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) hb
  simp only [gain, markerCorrection, Nat.cast_add, Nat.cast_ofNat]
  rw [← hc]
  nlinarith

/-- Failure is confined to departure of the old marker or an incoming strict record. -/
theorem marker_bad_exit_events (n k : ℕ) (b : Fin (n + 2) → ℕ)
    (hb : Bad ⟨n + 2, by omega⟩ (markerCorrection ⟨n + 2, by omega⟩) (.inr (k,b))) :
    (firstFutureMax ⟨n + 2, by omega⟩
      (prependOne ⟨n + 2, by omega⟩ (positiveWindow ⟨n + 2, by omega⟩ b))).val = 1 ∨
    prependOne ⟨n + 2, by omega⟩ (positiveWindow ⟨n + 2, by omega⟩ b)
      (firstFutureMax ⟨n + 2, by omega⟩
        (prependOne ⟨n + 2, by omega⟩ (positiveWindow ⟨n + 2, by omega⟩ b))) <
      positiveWindow ⟨n + 2, by omega⟩ b (Fin.last (n + 1)) := by
  by_contra hn
  push Not at hn
  have hp := (marker_selector_law ⟨n + 2, by omega⟩
    (prependOne ⟨n + 2, by omega⟩ (positiveWindow ⟨n + 2, by omega⟩ b)) (by change 2 ≤ n + 2; omega)).1
  have hj : 2 ≤ (firstFutureMax ⟨n + 2, by omega⟩
    (prependOne ⟨n + 2, by omega⟩ (positiveWindow ⟨n + 2, by omega⟩ b))).val := by omega
  have hs := exit_selector_shift n (positiveWindow ⟨n + 2, by omega⟩ b) hj hn.2
  have hd := exit_distance_of_shift n (positiveWindow ⟨n + 2, by omega⟩ b) hs
  exact (not_le_of_gt (exit_gain_neg_of_distance n k b hd)) hb

/-- The deterministic exceptions lie in explicit product-vector max events. -/
theorem marker_bad_exit_contains (n k : ℕ) (b : Fin (n + 2) → ℕ)
    (hb : Bad ⟨n + 2, by omega⟩ (markerCorrection ⟨n + 2, by omega⟩) (.inr (k,b))) :
    (∀ j : Fin n, b j.succ.castSucc ≤ b 0) ∨
    (∀ j : Fin (n + 2), j ≠ Fin.last (n + 1) → b j < b (Fin.last (n + 1))) := by
  let h : Depth := ⟨n + 2, by omega⟩
  let w := prependOne h (positiveWindow h b)
  have hs := marker_selector_law h w (by dsimp [h]; omega)
  have hmap (i : Fin (n + 2)) (hi : i.val < n + 1) :
      w ⟨i.val + 1, by dsimp [h]; omega⟩ = b i + 1 := by
    dsimp [w]
    simp only [prependOne, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
      dite_false, Nat.add_sub_cancel, positiveWindow]
    congr 1
  rcases marker_bad_exit_events n k b hb with hdepart | hrecord
  · left
    have hidx : firstFutureMax h w = ⟨1, by dsimp [h]; omega⟩ := by
      apply Fin.ext
      exact hdepart
    have hzero := hmap 0 (by simp)
    have hhead : w (firstFutureMax h w) = b 0 + 1 := by
      rw [hidx]
      exact hzero
    intro j
    have hm := hs.2.1 ⟨j.val + 2, by dsimp [h]; have := j.isLt; omega⟩ (by simp)
    have hv := hmap j.succ.castSucc (by simp)
    rw [hhead] at hm
    have hve : w ⟨j.val + 2, by dsimp [h]; have := j.isLt; omega⟩ =
        w ⟨j.succ.castSucc.val + 1, by dsimp [h]; have := j.isLt; simp⟩ := by
      congr 1
    rw [hve, hv] at hm
    omega
  · right
    intro j hj
    have hjlt : j.val < n + 1 := by
      have ht := j.isLt
      have hn : j.val ≠ n + 1 := by intro he; apply hj; apply Fin.ext; exact he
      omega
    have hm := hs.2.1 ⟨j.val + 1, by dsimp [h]; omega⟩ (by simp)
    rw [hmap j hjlt] at hm
    change w (firstFutureMax h w) < b (Fin.last (n + 1)) + 1 at hrecord
    omega

/-- The exact symbolic mass is bounded by half the two max-event masses. -/
theorem marker_symbolic_union_bound (n : ℕ) :
    symbolicFailureDensity ⟨n + 2, by omega⟩ (markerCorrection ⟨n + 2, by omega⟩) ≤
      (1 / 2 : ℝ) * (eventMass (n + 2) (WeakPrefix n) +
        eventMass (n + 2) (StrictMax (n + 2) (Fin.last (n + 1)))) := by
  classical
  let h : Depth := ⟨n + 2, by omega⟩
  let φ := markerCorrection h
  let P := WeakPrefix n
  let Q := StrictMax (n + 2) (Fin.last (n + 1))
  let f : ℕ → ℝ := fun k => (1 / 2 : ℝ) * atom k
  let g : (Fin (n + 2) → ℕ) → ℝ := fun b =>
    (if P b then productWeight (n + 2) b else 0) +
    (if Q b then productWeight (n + 2) b else 0)
  have hf := atom_summable.mul_left (1 / 2 : ℝ)
  have hP := event_mask_summable (n + 2) P
  have hQ := event_mask_summable (n + 2) Q
  have hg : Summable g := hP.add hQ
  have hf0 (k : ℕ) : 0 ≤ f k := by
    exact mul_nonneg (by norm_num) (le_of_lt (atom_positive k))
  have hg0 (b : Fin (n + 2) → ℕ) : 0 ≤ g b := by
    dsimp [g]
    split_ifs <;> nlinarith [productWeight_positive (n + 2) b]
  have hprod := independent_product_summable f g hf0 hg0 hf hg
  have hs := selected_mass_summable h φ
  have hzero : (fun a : AscendingIndex h => selectedWeight h φ (.inl a)) = fun _ => 0 := by
    funext a
    exact marker_ascending_weight_zero h (by dsimp [h]; omega) a
  have hmass : symbolicFailureDensity h φ =
      ∑' p : ExitIndex h, selectedWeight h φ (.inr p) := by
    unfold symbolicFailureDensity
    rw [Summable.tsum_sum (f := selectedWeight h φ)
      (hs.comp_injective Sum.inl_injective) (hs.comp_injective Sum.inr_injective),
      hzero, tsum_zero, zero_add]
  have hbound : ∀ p : ExitIndex h, selectedWeight h φ (.inr p) ≤ f p.1 * g p.2 := by
    rintro ⟨k,b⟩
    by_cases hb : Bad h φ (.inr (k,b))
    · have hc := marker_bad_exit_contains n k b hb
      have hm : productWeight (n + 2) b ≤ g b := by
        rcases hc with hp | hq
        · change P b at hp
          dsimp [g]
          simp only [hp, ite_true]
          split_ifs <;> nlinarith [productWeight_positive (n + 2) b]
        · change Q b at hq
          dsimp [g]
          simp only [hq, ite_true]
          split_ifs <;> nlinarith [productWeight_positive (n + 2) b]
      simp only [selectedWeight, hb, ite_true]
      rw [exit_weight_product]
      exact mul_le_mul_of_nonneg_left hm (hf0 k)
    · simp only [selectedWeight, hb, ite_false]
      exact mul_nonneg (hf0 k) (hg0 b)
  have hfsum : (∑' k, f k) = (1 / 2 : ℝ) := by
    change (∑' k, (1 / 2 : ℝ) * atom k) = _
    rw [atom_summable.tsum_mul_left, atom_tsum, mul_one]
  have hgsum : (∑' b, g b) = eventMass (n + 2) P + eventMass (n + 2) Q := by
    change (∑' b, ((if P b then productWeight (n + 2) b else 0) +
      (if Q b then productWeight (n + 2) b else 0))) = _
    rw [hP.tsum_add hQ]
    rfl
  change symbolicFailureDensity h φ ≤ _
  rw [hmass]
  calc
    _ ≤ ∑' p : ExitIndex h, f p.1 * g p.2 :=
      Summable.tsum_le_tsum hbound (hs.comp_injective Sum.inr_injective) hprod
    _ = (∑' k, f k) * (∑' b, g b) := by
      rw [hprod.tsum_prod]
      simp_rw [hg.tsum_mul_left]
      exact hf.tsum_mul_right _
    _ = _ := by rw [hfsum, hgsum]

/-- The frozen marker upper bound on literal odd-seed failure density. -/
theorem marker_upper_bound : MarkerUpperBound := by
  intro h hh
  obtain ⟨n, hn⟩ : ∃ n : ℕ, h.val = n + 2 := ⟨h.val - 2, by omega⟩
  have he : h = ⟨n + 2, Nat.zero_lt_succ (n + 1)⟩ := Subtype.ext hn
  subst h
  obtain ⟨d, hd, hhalf⟩ := marker_density_half ⟨n + 2, by omega⟩ hh
  refine ⟨d, hd, le_min hhalf ?_⟩
  have heq : d = symbolicFailureDensity ⟨n + 2, by omega⟩
      (markerCorrection ⟨n + 2, by omega⟩) :=
    tendsto_nhds_unique hd (density_equals_symbolic _ _).2.2.2
  rw [heq]
  have hw := weak_prefix_mass_le n
  have hs := strict_max_mass_le (n + 2) (by omega) (Fin.last (n + 1))
  have hu := marker_symbolic_union_bound n
  have hb := add_le_add hw hs
  have hm := mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hn0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hn1 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  calc
    _ ≤ (1 / 2 : ℝ) * (2 / ((n : ℝ) + 1) + 1 / (n + 2 : ℕ)) := hu.trans hm
    _ = _ := by
      simp only [Nat.cast_add, Nat.cast_ofNat]
      have he : ((n : ℝ) + 2) - 1 = (n : ℝ) + 1 := by ring
      rw [he]
      field_simp [ne_of_gt hn0, ne_of_gt hn1]

end ExternalO3RateMarkerEvents
