import RateCycles
import RateMoments
import GeneralMarginal

/-! Exact finite-history failure normalization; no averaging of corrections. -/
namespace ExternalO3RateNormalization
open scoped BigOperators
open ExternalO3GeneralDraft ExternalO3RateDraft ExternalO3GeneralWeights
open ExternalO3GeneralMarginal ExternalO3RateCycles ExternalO3RateMoments

theorem atom_succ (t : ℕ) : atom (t + 1) = (1 / 2 : ℝ) * atom t := by
  simp only [atom_geometric, pow_succ]
  ring

theorem prefix_nonneg_le (q : ℕ → ℝ) (hq0 : ∀ j, 0 ≤ q j)
    (hq1 : ∀ j, q j ≤ 1) (t : ℕ) :
    0 ≤ (∑ j ∈ Finset.range t, q j) ∧ (∑ j ∈ Finset.range t, q j) ≤ (t : ℝ) := by
  refine ⟨Finset.sum_nonneg (fun j _ => hq0 j), ?_⟩
  calc
    _ ≤ ∑ _j ∈ Finset.range t, (1 : ℝ) := Finset.sum_le_sum (fun j _ => hq1 j)
    _ = _ := by simp

theorem weighted_prefix_summable (q : ℕ → ℝ) (hq0 : ∀ j, 0 ≤ q j)
    (hq1 : ∀ j, q j ≤ 1) :
    Summable (fun t => atom t * ∑ j ∈ Finset.range t, q j) := by
  apply Summable.of_nonneg_of_le
    (fun t => mul_nonneg (le_of_lt (atom_positive t)) (prefix_nonneg_le q hq0 hq1 t).1)
    (fun t => mul_le_mul_of_nonneg_left
      (le_trans (prefix_nonneg_le q hq0 hq1 t).2 (by linarith))
      (le_of_lt (atom_positive t))) atom_length_hasSum.summable

theorem weighted_prefix_tsum (q : ℕ → ℝ) (hq0 : ∀ j, 0 ≤ q j)
    (hq1 : ∀ j, q j ≤ 1) :
    (∑' t, atom t * ∑ j ∈ Finset.range t, q j) = ∑' j, atom j * q j := by
  have hs := weighted_prefix_summable q hq0 hq1
  have hq : Summable (fun j => atom j * q j) :=
    Summable.of_nonneg_of_le (fun j => mul_nonneg (le_of_lt (atom_positive j)) (hq0 j))
      (fun j => by nlinarith [atom_positive j, hq1 j]) atom_summable
  have he (t : ℕ) : atom (t + 1) * (∑ j ∈ Finset.range (t + 1), q j) =
      (1 / 2 : ℝ) * (atom t * ∑ j ∈ Finset.range t, q j) +
      (1 / 2 : ℝ) * (atom t * q t) := by
    rw [atom_succ, Finset.sum_range_succ]
    ring
  have ht := hs.tsum_eq_zero_add
  simp only [Finset.range_zero, Finset.sum_empty, mul_zero, zero_add] at ht
  simp_rw [he] at ht
  rw [(hs.mul_left (1 / 2 : ℝ)).tsum_add (hq.mul_left (1 / 2 : ℝ)),
    hs.tsum_mul_left, hq.tsum_mul_left] at ht
  linarith

theorem cyclicLength_cons (h : Depth) (t : ℕ) (b : Fin h.val → ℕ)
    (j : Fin h.val) :
    cyclicLength h (Fin.cons t b) (j.val + 1) = b j + 1 := by
  have he : Fin.ofNat (h.val + 1) (j.val + 1) = j.succ := by
    apply Fin.ext
    simp only [Fin.val_ofNat, Fin.val_succ]
    exact Nat.mod_eq_of_lt (by omega)
  change (Fin.cons t b : Fin (h.val + 1) → ℕ) (Fin.ofNat (h.val + 1) (j.val + 1)) + 1 = _
  rw [he]
  rfl

theorem successor_window_cons (h : Depth) (t : ℕ) (b : Fin h.val → ℕ) :
    cyclicWindow h (Fin.cons t b) 1 (cyclicLength h (Fin.cons t b) 1) =
      positiveWindow h b := by
  funext j
  unfold cyclicWindow positiveWindow
  split_ifs with hj
  · simpa [hj] using cyclicLength_cons h t b j
  · rw [Nat.add_comm 1 j.val, cyclicLength_cons]

theorem exit_source_window_cons (h : Depth) (t : ℕ) (b : Fin h.val → ℕ) :
    cyclicWindow h (Fin.cons t b) 0 1 = prependOne h (positiveWindow h b) := by
  funext j
  unfold cyclicWindow prependOne
  split_ifs with hj
  · rfl
  · simp only [Nat.zero_add, positiveWindow]
    have he : j.val - 1 + 1 = j.val := by omega
    simpa only [he] using cyclicLength_cons h t b ⟨j.val - 1, by omega⟩

theorem exit_gain_cons (h : Depth) (φ : Correction h) (t : ℕ)
    (b : Fin h.val → ℕ) :
    exitGain h φ (Fin.cons t b) 0 2 = gain h φ (.inr (0, b)) := by
  simp only [exitGain, successor_window_cons, exit_source_window_cons, gain,
    Nat.zero_add, Nat.cast_ofNat]


theorem selected_eq_failed (h : Depth) (φ : Correction h) (e : Edge h) :
    selectedWeight h φ e = weight h e * (failed (gain h φ e) : ℝ) := by
  classical
  by_cases hp : 0 ≤ gain h φ e <;> simp [selectedWeight, Bad, failed, hp]

theorem failed_real_nonneg (g : ℝ) : 0 ≤ (failed g : ℝ) := by positivity

theorem failed_real_le_one (g : ℝ) : (failed g : ℝ) ≤ 1 := by
  exact_mod_cast failed_le_one g

theorem product_bounded_summable (n : ℕ) (q : (Fin n → ℕ) → ℝ)
    (hq0 : ∀ b, 0 ≤ q b) (hq1 : ∀ b, q b ≤ 1) :
    Summable (fun b => productWeight n b * q b) := by
  exact Summable.of_nonneg_of_le
    (fun b => mul_nonneg (le_of_lt (productWeight_positive n b)) (hq0 b))
    (fun b => by nlinarith [productWeight_positive n b, hq1 b])
    (productWeight_summable n)

theorem weighted_exit_summable (h : Depth) (φ : Correction h) :
    Summable (fun r : History h => historyWeight h r * (failed (exitGain h φ r 0 2) : ℝ)) := by
  simp_rw [history_weight_product]
  exact product_bounded_summable _ _
    (fun r => failed_real_nonneg _) (fun r => failed_real_le_one _)

theorem weighted_exit_tsum (h : Depth) (φ : Correction h) :
    (∑' r : History h, historyWeight h r * (failed (exitGain h φ r 0 2) : ℝ)) =
      4 * exitMass h φ 0 := by
  let q : (Fin h.val → ℕ) → ℝ := fun b => (failed (gain h φ (.inr (0, b))) : ℝ)
  have hq := product_bounded_summable h.val q
    (fun b => failed_real_nonneg _) (fun b => failed_real_le_one _)
  let e := Fin.consEquiv (fun _ : Fin (h.val + 1) => ℕ)
  have hs := (weighted_exit_summable h φ).comp_injective e.injective
  simp only [Function.comp_def] at hs
  have hv : (∑' r : History h, historyWeight h r * (failed (exitGain h φ r 0 2) : ℝ)) =
      ∑' b, productWeight h.val b * q b := by
    rw [← e.tsum_eq, hs.tsum_prod]
    simp only [e, Fin.consEquiv, Equiv.coe_fn_mk, history_weight_product,
      productWeight_cons, exit_gain_cons]
    have hi (t : ℕ) :
        (∑' b : Fin h.val → ℕ, atom t * productWeight h.val b * q b) =
        atom t * (∑' b, productWeight h.val b * q b) := by
      simpa only [mul_assoc] using hq.tsum_mul_left (atom t)
    change (∑' t, ∑' b, atom t * productWeight h.val b * q b) = _
    simp_rw [hi]
    rw [atom_summable.tsum_mul_right, atom_tsum, one_mul]
  have hp (b : Fin h.val → ℕ) : selectedWeight h φ (.inr (0, b)) =
      (1 / 4 : ℝ) * (productWeight h.val b * q b) := by
    rw [selected_eq_failed, exit_weight_product]
    norm_num [atom, q]
    ring
  have hm : exitMass h φ 0 = (1 / 4 : ℝ) * ∑' b, productWeight h.val b * q b := by
    unfold exitMass
    simp_rw [hp]
    exact hq.tsum_mul_left _
  rw [hv, hm]
  ring

theorem ascending_window_cons_snoc (n t j z : ℕ) (c : Fin n → ℕ) :
    cyclicWindow (succDepth n) (Fin.cons t (Fin.snoc c z)) 0 (j + 2) =
      ascendingWindow (succDepth n) (Fin.cons j c) := by
  funext i
  refine Fin.cases ?_ (fun u => ?_) i
  · change j + 2 = (Fin.cons j c : Fin (n + 1) → ℕ) 0 + 2
    rfl
  · simp only [cyclicWindow, ascendingWindow, Fin.val_succ, Nat.zero_add,
      Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false]
    change cyclicLength (succDepth n) (Fin.cons t (Fin.snoc c z)) (u.val + 1) = c u + 1
    have hv := cyclicLength_cons (succDepth n) t (Fin.snoc c z) u.castSucc
    change cyclicLength (succDepth n) (Fin.cons t (Fin.snoc c z)) (u.val + 1) =
      (Fin.snoc c z : Fin (n + 1) → ℕ) u.castSucc + 1 at hv
    simpa only [Fin.snoc_castSucc] using hv

theorem decremented_window_cons_snoc (n t j z : ℕ) (c : Fin n → ℕ) :
    cyclicWindow (succDepth n) (Fin.cons t (Fin.snoc c z)) 0 (j + 1) =
      decrementHead (succDepth n) (ascendingWindow (succDepth n) (Fin.cons j c)) := by
  funext i
  refine Fin.cases ?_ (fun u => ?_) i
  · change j + 1 = (Fin.cons j c : Fin (n + 1) → ℕ) 0 + 2 - 1
    simp
  · simp only [cyclicWindow, ascendingWindow, decrementHead, Fin.val_succ, Nat.zero_add,
      Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false]
    change cyclicLength (succDepth n) (Fin.cons t (Fin.snoc c z)) (u.val + 1) = c u + 1
    have hv := cyclicLength_cons (succDepth n) t (Fin.snoc c z) u.castSucc
    change cyclicLength (succDepth n) (Fin.cons t (Fin.snoc c z)) (u.val + 1) =
      (Fin.snoc c z : Fin (n + 1) → ℕ) u.castSucc + 1 at hv
    simpa only [Fin.snoc_castSucc] using hv

theorem ascent_gain_cons_snoc (n : ℕ) (φ : Correction (succDepth n))
    (t j z : ℕ) (c : Fin n → ℕ) :
    ascentGain (succDepth n) φ (Fin.cons t (Fin.snoc c z)) 0 (j + 2) =
      gain (succDepth n) φ (.inl (Fin.cons j c)) := by
  unfold ascentGain
  rw [show j + 2 - 1 = j + 1 by omega,
    ascending_window_cons_snoc, decremented_window_cons_snoc]
  rfl

theorem cons_prefix_summable (n : ℕ) (q : ℕ → (Fin n → ℕ) → ℝ)
    (hq0 : ∀ j c, 0 ≤ q j c) (hq1 : ∀ j c, q j c ≤ 1) :
    Summable (fun a : Fin (n + 1) → ℕ => productWeight (n + 1) a *
      ∑ j ∈ Finset.range (a 0), q j (Fin.tail a)) := by
  let e := Fin.consEquiv (fun _ : Fin (n + 1) => ℕ)
  have hb := independent_product_summable (fun t => atom t * ((t : ℝ) + 1))
    (productWeight n) (fun t => by positivity [le_of_lt (atom_positive t)])
    (fun c => le_of_lt (productWeight_positive n c))
    atom_length_hasSum.summable (productWeight_summable n)
  have hs : Summable (fun p : ℕ × (Fin n → ℕ) => atom p.1 * productWeight n p.2 *
      ∑ j ∈ Finset.range p.1, q j p.2) := by
    apply Summable.of_nonneg_of_le
      (fun p => mul_nonneg (mul_nonneg (le_of_lt (atom_positive _))
        (le_of_lt (productWeight_positive _ _)))
        (prefix_nonneg_le (fun j => q j p.2) (fun j => hq0 j p.2) (fun j => hq1 j p.2) p.1).1)
      (fun p => ?_) hb
    have hp := (prefix_nonneg_le (fun j => q j p.2)
      (fun j => hq0 j p.2) (fun j => hq1 j p.2) p.1).2
    have hx := mul_le_mul_of_nonneg_left (le_trans hp (by linarith :
      (p.1 : ℝ) ≤ (p.1 : ℝ) + 1))
      (mul_nonneg (le_of_lt (atom_positive p.1)) (le_of_lt (productWeight_positive n p.2)))
    nlinarith only [hx]
  apply e.summable_iff.mp
  simpa [Function.comp_def, e, Fin.consEquiv, productWeight_cons] using hs

set_option maxHeartbeats 800000 in
theorem cons_prefix_tsum (n : ℕ) (q : ℕ → (Fin n → ℕ) → ℝ)
    (hq0 : ∀ j c, 0 ≤ q j c) (hq1 : ∀ j c, q j c ≤ 1) :
    (∑' a : Fin (n + 1) → ℕ, productWeight (n + 1) a *
      ∑ j ∈ Finset.range (a 0), q j (Fin.tail a)) =
      ∑' c : Fin n → ℕ, productWeight n c * ∑' j, atom j * q j c := by
  let e := Fin.consEquiv (fun _ : Fin (n + 1) => ℕ)
  have hs := (cons_prefix_summable n q hq0 hq1).comp_injective e.injective
  simp only [Function.comp_def] at hs
  rw [← e.tsum_eq, hs.tsum_prod]
  simp only [e, Fin.consEquiv, Equiv.coe_fn_mk, productWeight_cons, Fin.cons_zero, Fin.tail_cons]
  have hc := Summable.tsum_comm (f := fun t (c : Fin n → ℕ) =>
    productWeight (n + 1) (e (t, c)) *
      ∑ j ∈ Finset.range ((e (t, c)) 0), q j (Fin.tail (e (t, c)))) hs
  simp only [e, Fin.consEquiv, Equiv.coe_fn_mk, productWeight_cons, Fin.cons_zero, Fin.tail_cons] at hc
  rw [← hc]
  apply tsum_congr
  intro c
  have hh := (weighted_prefix_summable (fun j => q j c)
    (fun j => hq0 j c) (fun j => hq1 j c)).tsum_mul_left (productWeight n c)
  have he : (∑' t, atom t * productWeight n c * ∑ j ∈ Finset.range t, q j c) =
      productWeight n c * ∑' t, atom t * ∑ j ∈ Finset.range t, q j c := by
    simpa only [mul_left_comm, mul_assoc, mul_comm] using hh
  rw [he, weighted_prefix_tsum _ (fun j => hq0 j c) (fun j => hq1 j c)]

theorem weighted_snoc_summable (n : ℕ) (F : (Fin n → ℕ) → ℝ)
    (hF0 : ∀ a, 0 ≤ F a) (hF : Summable (fun a => productWeight n a * F a)) :
    Summable (fun r : Fin (n + 1) → ℕ => productWeight (n + 1) r * F (Fin.init r)) := by
  let e := Fin.snocEquiv (fun _ : Fin (n + 1) => ℕ)
  have hs := independent_product_summable atom (fun a => productWeight n a * F a)
    (fun z => le_of_lt (atom_positive z))
    (fun a => mul_nonneg (le_of_lt (productWeight_positive n a)) (hF0 a))
    atom_summable hF
  apply e.summable_iff.mp
  simpa [e, Fin.snocEquiv, Function.comp_def, productWeight_snoc, mul_assoc, mul_left_comm,
    mul_comm] using hs

theorem weighted_snoc_tsum (n : ℕ) (F : (Fin n → ℕ) → ℝ)
    (hF0 : ∀ a, 0 ≤ F a) (hF : Summable (fun a => productWeight n a * F a)) :
    (∑' r : Fin (n + 1) → ℕ, productWeight (n + 1) r * F (Fin.init r)) =
      ∑' a, productWeight n a * F a := by
  let e := Fin.snocEquiv (fun _ : Fin (n + 1) => ℕ)
  have hs := (weighted_snoc_summable n F hF0 hF).comp_injective e.injective
  simp only [Function.comp_def] at hs
  rw [← e.tsum_eq, hs.tsum_prod]
  simp only [e, Fin.snocEquiv, Equiv.coe_fn_mk, productWeight_snoc, Fin.init_snoc]
  have hi (z : ℕ) : (∑' a : Fin n → ℕ, productWeight n a * atom z * F a) =
      atom z * (∑' a, productWeight n a * F a) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hF.tsum_mul_left (atom z)
  simp_rw [hi]
  rw [atom_summable.tsum_mul_right, atom_tsum, one_mul]

theorem cons_bounded_tsum (n : ℕ) (q : ℕ → (Fin n → ℕ) → ℝ)
    (hq0 : ∀ j c, 0 ≤ q j c) (hq1 : ∀ j c, q j c ≤ 1) :
    (∑' a : Fin (n + 1) → ℕ, productWeight (n + 1) a * q (a 0) (Fin.tail a)) =
      ∑' c : Fin n → ℕ, productWeight n c * ∑' j, atom j * q j c := by
  let e := Fin.consEquiv (fun _ : Fin (n + 1) => ℕ)
  have hs0 := product_bounded_summable (n + 1) (fun a => q (a 0) (Fin.tail a))
    (fun a => hq0 _ _) (fun a => hq1 _ _)
  have hs := hs0.comp_injective e.injective
  simp only [Function.comp_def] at hs
  rw [← e.tsum_eq, hs.tsum_prod]
  simp only [e, Fin.consEquiv, Equiv.coe_fn_mk, productWeight_cons, Fin.cons_zero, Fin.tail_cons]
  have hc := Summable.tsum_comm (f := fun j (c : Fin n → ℕ) =>
    productWeight (n + 1) (e (j, c)) * q ((e (j, c)) 0) (Fin.tail (e (j, c)))) hs
  simp only [e, Fin.consEquiv, Equiv.coe_fn_mk, productWeight_cons, Fin.cons_zero, Fin.tail_cons] at hc
  rw [← hc]
  apply tsum_congr
  intro c
  have hq : Summable (fun j => atom j * q j c) :=
    Summable.of_nonneg_of_le (fun j => mul_nonneg (le_of_lt (atom_positive j)) (hq0 j c))
      (fun j => by nlinarith [atom_positive j, hq1 j c]) atom_summable
  simpa only [mul_comm, mul_left_comm, mul_assoc] using hq.tsum_mul_left (productWeight n c)

noncomputable def ascendingIndicator (n : ℕ) (φ : Correction (succDepth n))
    (j : ℕ) (c : Fin n → ℕ) : ℝ :=
  (failed (gain (succDepth n) φ (.inl (Fin.cons j c))) : ℝ)

noncomputable def ascendingPrefix (n : ℕ) (φ : Correction (succDepth n))
    (a : Fin (n + 1) → ℕ) : ℝ :=
  ∑ j ∈ Finset.range (a 0), ascendingIndicator n φ j (Fin.tail a)

noncomputable def ascentContribution (h : Depth) (φ : Correction h) (r : History h) : ℝ :=
  ∑ j ∈ Finset.range (cyclicLength h r 0 - 1), (failed (ascentGain h φ r 0 (j + 2)) : ℝ)

theorem ascendingIndicator_nonneg (n : ℕ) (φ : Correction (succDepth n)) (j : ℕ) (c : Fin n → ℕ) :
    0 ≤ ascendingIndicator n φ j c := failed_real_nonneg _

theorem ascendingIndicator_le_one (n : ℕ) (φ : Correction (succDepth n)) (j : ℕ) (c : Fin n → ℕ) :
    ascendingIndicator n φ j c ≤ 1 := failed_real_le_one _

theorem ascendingPrefix_nonneg (n : ℕ) (φ : Correction (succDepth n))
    (a : Fin (n + 1) → ℕ) : 0 ≤ ascendingPrefix n φ a :=
  Finset.sum_nonneg (fun j _ => ascendingIndicator_nonneg n φ j _)

theorem ascendingPrefix_summable (n : ℕ) (φ : Correction (succDepth n)) :
    Summable (fun a => productWeight (n + 1) a * ascendingPrefix n φ a) :=
  cons_prefix_summable n (ascendingIndicator n φ)
    (ascendingIndicator_nonneg n φ) (ascendingIndicator_le_one n φ)

theorem ascent_contribution_snoc (n : ℕ) (φ : Correction (succDepth n))
    (a : Fin (n + 1) → ℕ) (z : ℕ) :
    ascentContribution (succDepth n) φ (Fin.snoc a z) = ascendingPrefix n φ a := by
  obtain ⟨⟨t, c⟩, ha⟩ := (Fin.consEquiv (fun _ : Fin (n + 1) => ℕ)).surjective a
  change Fin.cons t c = a at ha
  subst a
  erw [← Fin.cons_snoc_eq_snoc_cons]
  have hr : cyclicLength (succDepth n) (Fin.cons t (Fin.snoc c z)) 0 = t + 1 := by
    change (Fin.cons t (Fin.snoc c z) : Fin (n + 1 + 1) → ℕ)
      (Fin.ofNat (n + 1 + 1) 0) + 1 = t + 1
    have hzero : Fin.ofNat (n + 1 + 1) 0 = 0 := by apply Fin.ext; simp
    rw [hzero]
    rfl
  unfold ascentContribution ascendingPrefix
  erw [hr]
  simp only [Nat.add_sub_cancel, Fin.cons_zero, Fin.tail_cons, ascendingIndicator]
  apply Finset.sum_congr rfl
  intro j _
  erw [ascent_gain_cons_snoc]

theorem ascent_contribution_init (n : ℕ) (φ : Correction (succDepth n))
    (r : History (succDepth n)) :
    ascentContribution (succDepth n) φ r = ascendingPrefix n φ (Fin.init r) := by
  calc
    _ = ascentContribution (succDepth n) φ (Fin.snoc (Fin.init r) (r (Fin.last (n + 1)))) :=
      congrArg (ascentContribution (succDepth n) φ) (Fin.snoc_init_self r).symm
    _ = _ := ascent_contribution_snoc n φ _ _

theorem weighted_ascent_summable (n : ℕ) (φ : Correction (succDepth n)) :
    Summable (fun r : History (succDepth n) => historyWeight (succDepth n) r *
      ascentContribution (succDepth n) φ r) := by
  simp_rw [history_weight_product, ascent_contribution_init]
  exact weighted_snoc_summable (n + 1) (ascendingPrefix n φ)
    (ascendingPrefix_nonneg n φ) (ascendingPrefix_summable n φ)

theorem ascending_mass_prefix (n : ℕ) (φ : Correction (succDepth n)) :
    2 * ascendingMass (succDepth n) φ =
      ∑' c : Fin n → ℕ, productWeight n c * ∑' j, atom j * ascendingIndicator n φ j c := by
  have hs : Summable (fun a : AscendingIndex (succDepth n) =>
      selectedWeight (succDepth n) φ (.inl a)) :=
    Summable.of_nonneg_of_le (fun a => selectedWeight_nonneg _ _ _)
      (fun a => selectedWeight_le _ _ _) (ascending_summable _)
  calc
    _ = ∑' a : Fin (n + 1) → ℕ, 2 * selectedWeight (succDepth n) φ (.inl a) :=
      (hs.tsum_mul_left 2).symm
    _ = ∑' a : Fin (n + 1) → ℕ, productWeight (n + 1) a *
        ascendingIndicator n φ (a 0) (Fin.tail a) := by
      apply tsum_congr
      intro a
      erw [selected_eq_failed, ascending_weight_product]
      unfold ascendingIndicator
      erw [Fin.cons_self_tail]
      change 2 * ((1 / 2 : ℝ) * productWeight (n + 1) a *
        (failed (gain (succDepth n) φ (.inl a)) : ℝ)) =
          productWeight (n + 1) a * (failed (gain (succDepth n) φ (.inl a)) : ℝ)
      ring
    _ = _ := cons_bounded_tsum n (ascendingIndicator n φ)
      (ascendingIndicator_nonneg n φ) (ascendingIndicator_le_one n φ)

theorem weighted_ascent_tsum (n : ℕ) (φ : Correction (succDepth n)) :
    (∑' r : History (succDepth n), historyWeight (succDepth n) r *
      ascentContribution (succDepth n) φ r) = 2 * ascendingMass (succDepth n) φ := by
  simp_rw [history_weight_product, ascent_contribution_init]
  erw [weighted_snoc_tsum (n + 1) (ascendingPrefix n φ)
    (ascendingPrefix_nonneg n φ) (ascendingPrefix_summable n φ)]
  exact (cons_prefix_tsum n (ascendingIndicator n φ)
    (ascendingIndicator_nonneg n φ) (ascendingIndicator_le_one n φ)).trans
      (ascending_mass_prefix n φ).symm

theorem cyclic_normalization_succ (n : ℕ) (φ : Correction (succDepth n)) :
    Summable (fun r : History (succDepth n) => historyWeight (succDepth n) r *
      (blockFailures (succDepth n) φ r 0 2 : ℝ)) ∧
    (∑' r : History (succDepth n), historyWeight (succDepth n) r *
      (blockFailures (succDepth n) φ r 0 2 : ℝ)) =
      2 * ascendingMass (succDepth n) φ + 4 * exitMass (succDepth n) φ 0 := by
  have he (r : History (succDepth n)) : historyWeight (succDepth n) r *
      (blockFailures (succDepth n) φ r 0 2 : ℝ) =
      historyWeight (succDepth n) r * ascentContribution (succDepth n) φ r +
      historyWeight (succDepth n) r * (failed (exitGain (succDepth n) φ r 0 2) : ℝ) := by
    unfold blockFailures ascentContribution
    push_cast
    ring
  simp_rw [he]
  refine ⟨(weighted_ascent_summable n φ).add (weighted_exit_summable _ φ), ?_⟩
  rw [(weighted_ascent_summable n φ).tsum_add (weighted_exit_summable _ φ),
    weighted_ascent_tsum, weighted_exit_tsum]

theorem cyclic_normalization : CyclicNormalization := by
  intro h φ
  rcases h with ⟨m, hm⟩
  cases m with
  | zero => omega
  | succ n => exact cyclic_normalization_succ n φ

end ExternalO3RateNormalization
