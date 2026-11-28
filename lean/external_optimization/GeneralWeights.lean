import GeneralExpectedTypes
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Data.Fin.Tuple.Basic

/-! Pure finite-product geometric identities. No population or density law is assumed. -/
namespace ExternalO3GeneralWeights
open ExternalO3GeneralDraft
open scoped BigOperators

noncomputable def atom (a : ℕ) : ℝ := (2 : ℝ) ^ (-(a + 1 : ℤ))

theorem atom_positive (a : ℕ) : 0 < atom a := zpow_pos (by norm_num) _

theorem atom_geometric (a : ℕ) : atom a = (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ a := by
  unfold atom
  rw [neg_add, zpow_add₀ (show (2 : ℝ) ≠ 0 by norm_num)]
  simp [zpow_neg, one_div, inv_pow, mul_comm]

theorem atom_summable : Summable atom := by
  change Summable (fun a : ℕ => atom a)
  simpa only [atom_geometric] using summable_geometric_two.mul_left (1 / 2 : ℝ)

theorem atom_tsum : (∑' a : ℕ, atom a) = 1 := by
  simp_rw [atom_geometric]
  rw [summable_geometric_two.tsum_mul_left, tsum_geometric_two]
  norm_num

noncomputable def productWeight (n : ℕ) (a : Fin n → ℕ) : ℝ := ∏ i, atom (a i)

theorem productWeight_positive (n : ℕ) (a : Fin n → ℕ) : 0 < productWeight n a := by
  exact Finset.prod_pos (fun i _ => atom_positive (a i))

theorem productWeight_cons (n : ℕ) (a : ℕ) (b : Fin n → ℕ) :
    productWeight (n + 1) (Fin.cons a b) = atom a * productWeight n b := by
  simp [productWeight, Fin.prod_univ_succ]

theorem independent_product_summable {α β : Type*} (f : α → ℝ) (g : β → ℝ)
    (hf0 : ∀ a, 0 ≤ f a) (hg0 : ∀ b, 0 ≤ g b)
    (hf : Summable f) (hg : Summable g) :
    Summable (fun p : α × β => f p.1 * g p.2) := by
  apply (summable_prod_of_nonneg (fun p => mul_nonneg (hf0 p.1) (hg0 p.2))).mpr
  refine ⟨fun a => hg.mul_left (f a), ?_⟩
  simpa only [hg.tsum_mul_left] using hf.mul_right (∑' b, g b)

theorem productWeight_hasSum (n : ℕ) : HasSum (productWeight n) 1 := by
  induction n with
  | zero =>
    let : Fintype (Fin 0 → ℕ) := Fintype.ofSubsingleton (fun i => Fin.elim0 i)
    simpa [productWeight] using (hasSum_fintype (productWeight 0))
  | succ n ih =>
    have hs := independent_product_summable atom (productWeight n)
      (fun a => le_of_lt (atom_positive a))
      (fun b => le_of_lt (productWeight_positive n b)) atom_summable ih.summable
    have hh := atom_summable.hasSum.mul ih hs
    rw [atom_tsum, one_mul] at hh
    apply (Fin.consEquiv (fun _ : Fin (n + 1) => ℕ)).hasSum_iff.mp
    simpa [Function.comp_def, Fin.consEquiv, productWeight_cons] using hh

theorem productWeight_summable (n : ℕ) : Summable (productWeight n) :=
  (productWeight_hasSum n).summable

theorem productWeight_tsum (n : ℕ) : (∑' a : Fin n → ℕ, productWeight n a) = 1 :=
  (productWeight_hasSum n).tsum_eq

theorem productWeight_exponent (n : ℕ) (a : Fin n → ℕ) :
    productWeight n a = (2 : ℝ) ^ (-((∑ i : Fin n, (a i + 1) : ℕ) : ℤ)) := by
  induction n with
  | zero => simp [productWeight]
  | succ n ih =>
    rw [show a = Fin.cons (a 0) (fun i => a i.succ) from (Fin.cons_self_tail a).symm]
    rw [productWeight_cons, ih]
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    unfold atom
    rw [← zpow_add₀ (show (2 : ℝ) ≠ 0 by norm_num)]
    congr 1
    push_cast
    ring

theorem ascending_window_sum (h : Depth) (a : AscendingIndex h) :
    windowSum h (ascendingWindow h a) = (∑ i : Fin h.val, (a i + 1)) + 1 := by
  rcases h with ⟨n, hn⟩
  cases n with
  | zero => omega
  | succ n =>
    simp [windowSum, ascendingWindow, Fin.sum_univ_succ, Nat.add_assoc]
    omega

theorem ascending_weight_product (h : Depth) (a : AscendingIndex h) :
    weight h (.inl a) = (1 / 2 : ℝ) * productWeight h.val a := by
  rw [productWeight_exponent]
  change (2 : ℝ) ^ (-((windowSum h (ascendingWindow h a) : ℕ) : ℤ)) = _
  rw [ascending_window_sum, Nat.cast_add, Nat.cast_one, neg_add, zpow_add₀ (show (2 : ℝ) ≠ 0 by norm_num)]
  norm_num [zpow_neg, mul_comm]

theorem exit_atom (k : ℕ) : (2 : ℝ) ^ (-(k + 2 : ℤ)) = (1 / 2 : ℝ) * atom k := by
  unfold atom
  rw [show (-(k + 2 : ℤ)) = -1 + -(k + 1 : ℤ) by omega,
    zpow_add₀ (show (2 : ℝ) ≠ 0 by norm_num)]
  norm_num

theorem exit_weight_product (h : Depth) (k : ℕ) (b : Fin h.val → ℕ) :
    weight h (.inr (k, b)) = ((1 / 2 : ℝ) * atom k) * productWeight h.val b := by
  rw [productWeight_exponent]
  change (2 : ℝ) ^ (-((k + 2 + ∑ i : Fin h.val, (b i + 1) : ℕ) : ℤ)) = _
  rw [Nat.cast_add, neg_add, zpow_add₀ (show (2 : ℝ) ≠ 0 by norm_num)]
  simp only [Nat.cast_add, Nat.cast_ofNat, exit_atom]

theorem weight_positive (h : Depth) (e : Edge h) : 0 < weight h e := by
  cases e with
  | inl a => exact zpow_pos (by norm_num) _
  | inr p => exact zpow_pos (by norm_num) _

theorem ascending_summable (h : Depth) : Summable (fun a => weight h (.inl a)) := by
  simpa only [ascending_weight_product] using (productWeight_summable h.val).mul_left (1 / 2 : ℝ)

theorem ascending_tsum (h : Depth) : (∑' a, weight h (.inl a)) = (1 / 2 : ℝ) := by
  simp_rw [ascending_weight_product]
  rw [(productWeight_summable h.val).tsum_mul_left, productWeight_tsum, mul_one]

theorem exit_summable (h : Depth) : Summable (fun p : ExitIndex h => weight h (.inr p)) := by
  convert independent_product_summable
    (fun k => (1 / 2 : ℝ) * atom k) (productWeight h.val)
    (fun k => mul_nonneg (by norm_num) (le_of_lt (atom_positive k)))
    (fun b => le_of_lt (productWeight_positive h.val b))
    (atom_summable.mul_left (1 / 2 : ℝ)) (productWeight_summable h.val) using 1
  ext p
  exact exit_weight_product h p.1 p.2

theorem exit_tsum (h : Depth) : (∑' p : ExitIndex h, weight h (.inr p)) = (1 / 2 : ℝ) := by
  rw [(exit_summable h).tsum_prod]
  simp_rw [exit_weight_product, (productWeight_summable h.val).tsum_mul_left,
    productWeight_tsum, mul_one]
  rw [atom_summable.tsum_mul_left, atom_tsum, mul_one]

theorem weight_summable (h : Depth) : Summable (weight h) :=
  Summable.sum (weight h) (ascending_summable h) (exit_summable h)

theorem weight_tsum (h : Depth) : (∑' e : Edge h, weight h e) = 1 := by
  rw [Summable.tsum_sum (f := weight h) (ascending_summable h) (exit_summable h),
    ascending_tsum, exit_tsum]
  norm_num

theorem weight_law : WeightLaw :=
  fun h => ⟨weight_summable h, weight_tsum h, weight_positive h⟩

theorem selectedWeight_nonneg (h : Depth) (φ : Correction h) (e : Edge h) :
    0 ≤ selectedWeight h φ e := by
  classical
  unfold selectedWeight
  split
  · exact le_of_lt (weight_positive h e)
  · exact le_rfl

theorem selectedWeight_le (h : Depth) (φ : Correction h) (e : Edge h) :
    selectedWeight h φ e ≤ weight h e := by
  classical
  unfold selectedWeight
  split
  · exact le_rfl
  · exact le_of_lt (weight_positive h e)

theorem selected_mass_summable : SelectedMassSummable := by
  intro h φ
  exact Summable.of_nonneg_of_le (selectedWeight_nonneg h φ)
    (selectedWeight_le h φ) (weight_summable h)

theorem refined_exponent_split (m : ℕ) (data : RefinedIndex m) :
    refinedExponent m (decodedLengths m data) (decodedExits m data) =
      (∑ i : Fin (m + 1), (data.1 i + 1)) + (∑ i : Fin m, (data.2 i + 1)) := by
  simp [refinedExponent, decodedLengths, decodedExits, Fin.sum_univ_castSucc,
    Finset.sum_add_distrib]
  ring

theorem refined_weight_product (m : ℕ) (data : RefinedIndex m) :
    refinedWeight m data = productWeight (m + 1) data.1 * productWeight m data.2 := by
  rw [productWeight_exponent, productWeight_exponent]
  unfold refinedWeight
  rw [refined_exponent_split, Nat.cast_add, neg_add,
    zpow_add₀ (show (2 : ℝ) ≠ 0 by norm_num)]

theorem refined_weight_positive (m : ℕ) (data : RefinedIndex m) :
    0 < refinedWeight m data := zpow_pos (by norm_num) _

theorem refined_weight_summable (m : ℕ) : Summable (refinedWeight m) := by
  change Summable (fun data : RefinedIndex m => refinedWeight m data)
  simpa only [refined_weight_product] using independent_product_summable
    (productWeight (m + 1)) (productWeight m)
    (fun a => le_of_lt (productWeight_positive (m + 1) a))
    (fun b => le_of_lt (productWeight_positive m b))
    (productWeight_summable (m + 1)) (productWeight_summable m)

theorem refined_weight_tsum (m : ℕ) : (∑' data : RefinedIndex m, refinedWeight m data) = 1 := by
  rw [(refined_weight_summable m).tsum_prod]
  simp_rw [refined_weight_product, (productWeight_summable m).tsum_mul_left,
    productWeight_tsum, mul_one]
  exact productWeight_tsum (m + 1)

theorem refined_weight_law : RefinedWeightLaw :=
  fun m => ⟨refined_weight_summable m, refined_weight_tsum m, refined_weight_positive m⟩

end ExternalO3GeneralWeights
