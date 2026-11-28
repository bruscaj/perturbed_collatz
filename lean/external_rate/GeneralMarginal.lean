import GeneralWeights

/-! Geometric fiber marginalization only; no natural-density additivity. -/
namespace ExternalO3GeneralMarginal
open ExternalO3GeneralDraft ExternalO3GeneralWeights
open scoped BigOperators

theorem masked_summable {α : Type*} (f : α → ℝ) (hf0 : ∀ a, 0 ≤ f a)
    (hf : Summable f) (P : α → Prop) [DecidablePred P] : Summable (fun a => if P a then f a else 0) := by
  classical
  exact Summable.of_nonneg_of_le
    (fun a => by split <;> simp_all)
    (fun a => by split <;> simp_all) hf

theorem productWeight_snoc (n : ℕ) (a : Fin n → ℕ) (b : ℕ) :
    productWeight (n + 1) (Fin.snoc a b) = productWeight n a * atom b := by
  simp [productWeight, Fin.prod_univ_castSucc]

theorem prefix_tsum (n : ℕ) (b : Fin n → ℕ) :
    (∑' a : Fin (n + 1) → ℕ,
      if (fun i => a i.castSucc) = b then productWeight (n + 1) a else 0) =
      productWeight n b := by
  classical
  let e := Fin.snocEquiv (fun _ : Fin (n + 1) => ℕ)
  have hs := (masked_summable (productWeight (n + 1))
    (fun a => le_of_lt (productWeight_positive (n + 1) a))
    (productWeight_summable (n + 1)) (fun a => (fun i => a i.castSucc) = b)).comp_injective e.injective
  simp only [Function.comp_def] at hs
  rw [← e.tsum_eq, hs.tsum_prod]
  simp only [e, Fin.snocEquiv, Equiv.coe_fn_mk, Fin.snoc_castSucc,
    productWeight_snoc, tsum_ite_eq]
  rw [atom_summable.tsum_mul_left, atom_tsum, mul_one]

theorem head_tsum (n k : ℕ) :
    (∑' a : Fin (n + 1) → ℕ, if a 0 = k then productWeight (n + 1) a else 0) =
      atom k := by
  classical
  let e := Fin.consEquiv (fun _ : Fin (n + 1) => ℕ)
  have hs := (masked_summable (productWeight (n + 1))
    (fun a => le_of_lt (productWeight_positive (n + 1) a))
    (productWeight_summable (n + 1)) (fun a => a 0 = k)).comp_injective e.injective
  simp only [Function.comp_def] at hs
  rw [← e.tsum_eq, hs.tsum_prod]
  simp only [e, Fin.consEquiv, Equiv.coe_fn_mk, Fin.cons_zero, productWeight_cons]
  have hh (p : ℕ) : (∑' a : Fin n → ℕ,
      if p = k then atom p * productWeight n a else 0) = if p = k then atom p else 0 := by
    split <;> simp_all [(productWeight_summable n).tsum_mul_left, productWeight_tsum]
  simp_rw [hh]
  simp

def ascendingCode (h : Depth) (a : AscendingIndex h) : Fin h.val → ℕ :=
  fun i => if i.val = 0 then a i + 1 else a i

theorem projection_inl_iff (h : Depth) (d : RefinedIndex h.val) (a : AscendingIndex h) :
    refinementProjection h d = .inl a ↔
      (fun i : Fin h.val => d.1 i.castSucc) = ascendingCode h a := by
  classical
  unfold refinementProjection
  change (if 2 ≤ d.1 (zeroIndex h).castSucc + 1 then
    Sum.inl (ascendingOffsets h (fun i => d.1 i.castSucc + 1)) else _) = .inl a ↔ _
  by_cases hc : 2 ≤ d.1 (zeroIndex h).castSucc + 1
  · simp only [hc, ite_true, Sum.inl.injEq]
    constructor
    · intro hh
      funext i
      have hi := congrFun hh i
      dsimp [ascendingOffsets] at hi
      dsimp [ascendingCode]
      by_cases hz : i.val = 0
      · have he : i = zeroIndex h := Fin.ext hz
        subst i
        change d.1 (zeroIndex h).castSucc = a (zeroIndex h) + 1
        have hi' : d.1 (zeroIndex h).castSucc - 1 = a (zeroIndex h) := by
          simpa [zeroIndex] using hi
        omega
      · simpa only [hz, ite_false, Nat.add_sub_cancel] using hi
    · intro hh
      funext i
      have hi := congrFun hh i
      dsimp [ascendingCode] at hi
      dsimp [ascendingOffsets]
      by_cases hz : i.val = 0
      · simp only [hz, ite_true] at hi ⊢
        omega
      · simpa only [hz, ite_false, Nat.add_sub_cancel] using hi
  · simp only [hc, ite_false, Sum.inr_ne_inl, false_iff]
    intro hh
    have hi : d.1 (zeroIndex h).castSucc = a (zeroIndex h) + 1 := by
      simpa [ascendingCode, zeroIndex] using congrFun hh (zeroIndex h)
    omega

theorem projection_inr_iff (h : Depth) (d : RefinedIndex h.val)
    (k : ℕ) (b : Fin h.val → ℕ) :
    refinementProjection h d = .inr (k, b) ↔
      d.1 (zeroIndex h).castSucc = 0 ∧ d.2 (zeroIndex h) = k ∧
        (fun i : Fin h.val => d.1 i.succ) = b := by
  classical
  unfold refinementProjection
  change (if 2 ≤ d.1 (zeroIndex h).castSucc + 1 then _ else
    Sum.inr (d.2 (zeroIndex h), positiveOffsets h (fun i => d.1 i.succ + 1))) = .inr (k, b) ↔ _
  by_cases hc : 2 ≤ d.1 (zeroIndex h).castSucc + 1
  · simp only [hc, ite_true, Sum.inl_ne_inr, false_iff]
    rintro ⟨hh, _, _⟩
    omega
  · have hz : d.1 (zeroIndex h).castSucc = 0 := by omega
    have hoff : positiveOffsets h (fun i => d.1 i.succ + 1) = (fun i => d.1 i.succ) := by
      funext i
      exact Nat.add_sub_cancel _ _
    rw [hoff]
    simp [hz]

theorem ascendingCode_weight (h : Depth) (a : AscendingIndex h) :
    productWeight h.val (ascendingCode h a) = weight h (.inl a) := by
  rw [productWeight_exponent]
  change (2 : ℝ) ^ (-((∑ i : Fin h.val, (ascendingCode h a i + 1) : ℕ) : ℤ)) =
    (2 : ℝ) ^ (-((windowSum h (ascendingWindow h a) : ℕ) : ℤ))
  congr 3
  apply Finset.sum_congr rfl
  intro i _
  simp only [ascendingCode, ascendingWindow]
  split <;> omega

theorem fiber_summable (h : Depth) (e : Edge h) : Summable (refinedFiberWeight h e) := by
  classical
  exact masked_summable (refinedWeight h.val)
    (fun d => le_of_lt (refined_weight_positive h.val d)) (refined_weight_summable h.val)
    (fun d => refinementProjection h d = e)

theorem fiber_ascending_product (h : Depth) (a : AscendingIndex h) (d : RefinedIndex h.val) :
    refinedFiberWeight h (.inl a) d =
      (if (fun i : Fin h.val => d.1 i.castSucc) = ascendingCode h a then
        productWeight (h.val + 1) d.1 else 0) * productWeight h.val d.2 := by
  classical
  unfold refinedFiberWeight
  simp only [projection_inl_iff, refined_weight_product]
  split <;> simp_all

theorem fiber_ascending_tsum (h : Depth) (a : AscendingIndex h) :
    (∑' d : RefinedIndex h.val, refinedFiberWeight h (.inl a) d) = weight h (.inl a) := by
  rw [(fiber_summable h (.inl a)).tsum_prod]
  simp_rw [fiber_ascending_product, (productWeight_summable h.val).tsum_mul_left,
    productWeight_tsum, mul_one]
  rw [prefix_tsum, ascendingCode_weight]

theorem vector_eq_cons (h : Depth) (v : Fin (h.val + 1) → ℕ) (b : Fin h.val → ℕ) :
    v = Fin.cons 0 b ↔
      v (zeroIndex h).castSucc = 0 ∧ (fun i : Fin h.val => v i.succ) = b := by
  constructor
  · intro hh
    rw [hh]
    simp [zeroIndex]
  · rintro ⟨hh, ht⟩
    have h0 : v 0 = 0 := by simpa [zeroIndex] using hh
    calc
      v = Fin.cons (v 0) (fun i => v i.succ) := (Fin.cons_self_tail v).symm
      _ = Fin.cons 0 b := by rw [h0, ht]

theorem projection_inr_vector (h : Depth) (d : RefinedIndex h.val)
    (k : ℕ) (b : Fin h.val → ℕ) :
    refinementProjection h d = .inr (k, b) ↔
      d.1 = Fin.cons 0 b ∧ d.2 (zeroIndex h) = k := by
  rw [projection_inr_iff, vector_eq_cons]
  tauto

theorem fiber_exit_product (h : Depth) (k : ℕ) (b : Fin h.val → ℕ) (d : RefinedIndex h.val) :
    refinedFiberWeight h (.inr (k, b)) d =
      (if d.1 = Fin.cons 0 b then productWeight (h.val + 1) d.1 else 0) *
      (if d.2 (zeroIndex h) = k then productWeight h.val d.2 else 0) := by
  classical
  unfold refinedFiberWeight
  simp only [projection_inr_vector, refined_weight_product]
  by_cases h₁ : d.1 = Fin.cons 0 b <;>
    by_cases h₂ : d.2 (zeroIndex h) = k <;> simp [h₁, h₂]

theorem head_tsum_depth (h : Depth) (k : ℕ) :
    (∑' a : Fin h.val → ℕ, if a (zeroIndex h) = k then productWeight h.val a else 0) =
      atom k := by
  rcases h with ⟨n, hn⟩
  cases n with
  | zero => omega
  | succ n => exact head_tsum n k

theorem fiber_exit_tsum (h : Depth) (k : ℕ) (b : Fin h.val → ℕ) :
    (∑' d : RefinedIndex h.val, refinedFiberWeight h (.inr (k, b)) d) =
      weight h (.inr (k, b)) := by
  classical
  have hs : Summable (fun a : Fin h.val → ℕ =>
      if a (zeroIndex h) = k then productWeight h.val a else 0) :=
    masked_summable (productWeight h.val)
      (fun a => le_of_lt (productWeight_positive h.val a))
      (productWeight_summable h.val) (fun a => a (zeroIndex h) = k)
  rw [(fiber_summable h (.inr (k, b))).tsum_prod]
  simp_rw [fiber_exit_product, hs.tsum_mul_left, head_tsum_depth, ite_mul, zero_mul]
  simp only [tsum_ite_eq]
  rw [productWeight_cons, exit_weight_product]
  norm_num [atom]
  ring

theorem coarse_marginal_law : CoarseMarginalLaw := by
  intro h e
  refine ⟨fiber_summable h e, ?_⟩
  cases e with
  | inl a => exact fiber_ascending_tsum h a
  | inr p => exact fiber_exit_tsum h p.1 p.2

end ExternalO3GeneralMarginal
