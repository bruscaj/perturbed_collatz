import OptimizationEncoding
import OptimizationArithmetic
import GeneralWeights

/-! Exact finite retained/omitted masses. No optimization or density assumption. -/
namespace ExternalO3OptimizationMass
open scoped BigOperators
open ExternalO3GeneralDraft ExternalO3OptimizationDraft
open ExternalO3OptimizationEncoding ExternalO3GeneralWeights
noncomputable section
local instance (P : Prop) : Decidable P := Classical.propDecidable P

noncomputable def boundedWeight (n M : ℕ) (v : Fin n → Fin M) : ℝ :=
  ∏ i, atom (v i).val

theorem boundedWeight_cons (n M : ℕ) (a : Fin M) (v : Fin n → Fin M) :
    boundedWeight (n + 1) M (Fin.cons a v) = atom a.val * boundedWeight n M v := by
  simp [boundedWeight, Fin.prod_univ_succ]

theorem half_pow_eq_zpow (n : ℕ) : (1 / 2 : ℝ) ^ n = (2 : ℝ) ^ (-(n : ℤ)) := by
  simp [zpow_neg, one_div, inv_pow]

theorem atom_finite_sum_half (M : ℕ) :
    (∑ k : Fin M, atom k.val) = 1 - (1 / 2 : ℝ) ^ M := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih, atom_geometric, pow_succ]
    ring

theorem atom_finite_sum (M : ℕ) :
    (∑ k : Fin M, atom k.val) = 1 - (2 : ℝ) ^ (-(M : ℤ)) := by
  rw [atom_finite_sum_half, half_pow_eq_zpow]

theorem atom_succ (k : ℕ) : atom (k + 1) = (1 / 2 : ℝ) * atom k := by
  simp only [atom_geometric, pow_succ]
  ring

theorem positive_head_atom_sum (M : ℕ) (hM : 0 < M) :
    (∑ k : Fin M, if 0 < k.val then atom k.val else 0) =
      (1 / 2 : ℝ) - (2 : ℝ) ^ (-(M : ℤ)) := by
  cases M with
  | zero => omega
  | succ n =>
    simp only [Fin.sum_univ_succ, Fin.val_zero, lt_self_iff_false, ite_false,
      zero_add, Fin.val_succ, Nat.zero_lt_succ, ite_true]
    simp_rw [atom_succ]
    rw [← Finset.mul_sum, atom_finite_sum_half]
    rw [← half_pow_eq_zpow, pow_succ]
    ring

theorem exit_atom_sum (J : ℕ) (hJ : 1 ≤ J) :
    (∑ k : Fin (J - 1), (1 / 2 : ℝ) * atom k.val) =
      (1 / 2 : ℝ) - (2 : ℝ) ^ (-(J : ℤ)) := by
  rw [← Finset.mul_sum, atom_finite_sum_half, ← half_pow_eq_zpow]
  have hp : (1 / 2 : ℝ) ^ J = (1 / 2 : ℝ) ^ (J - 1) * (1 / 2 : ℝ) := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hp]
  ring

theorem boundedWeight_sum (n M : ℕ) :
    (∑ v : Fin n → Fin M, boundedWeight n M v) =
      (1 - (2 : ℝ) ^ (-(M : ℤ))) ^ n := by
  classical
  induction n with
  | zero => simp [boundedWeight]
  | succ n ih =>
    let e := Fin.consEquiv (fun _ : Fin (n + 1) => Fin M)
    rw [← e.sum_comp (boundedWeight (n + 1) M), Fintype.sum_prod_type]
    simp only [e, Fin.consEquiv, Equiv.coe_fn_mk, boundedWeight_cons]
    simp_rw [← Finset.mul_sum, ih]
    rw [← Finset.sum_mul, atom_finite_sum, pow_succ]
    ring

theorem boundedWeight_positive_head_sum (n M : ℕ) (hM : 0 < M) :
    (∑ v : Fin (n + 1) → Fin M,
      if 0 < (v 0).val then boundedWeight (n + 1) M v else 0) =
      ((1 / 2 : ℝ) - (2 : ℝ) ^ (-(M : ℤ))) *
        (1 - (2 : ℝ) ^ (-(M : ℤ))) ^ n := by
  classical
  let e := Fin.consEquiv (fun _ : Fin (n + 1) => Fin M)
  rw [← e.sum_comp (fun v => if 0 < (v 0).val then boundedWeight (n + 1) M v else 0),
    Fintype.sum_prod_type]
  simp only [e, Fin.consEquiv, Equiv.coe_fn_mk, Fin.cons_zero, boundedWeight_cons]
  have hi (k : Fin M) :
      (∑ v : Fin n → Fin M, if 0 < k.val then atom k.val * boundedWeight n M v else 0) =
      (if 0 < k.val then atom k.val else 0) * (∑ v, boundedWeight n M v) := by
    by_cases hk : 0 < k.val
    · simp only [hk, ite_true]
      rw [Finset.mul_sum]
    · simp only [hk, ite_false, Finset.sum_const_zero, zero_mul]
  simp_rw [hi, boundedWeight_sum]
  rw [← Finset.sum_mul, positive_head_atom_sum M hM]

theorem sum_subtype_mask {A : Type} [Fintype A] (P : A → Prop) [DecidablePred P] (f : A → ℝ) :
    (∑ a : {a // P a}, f a.val) = ∑ a : A, if P a then f a else 0 := by
  simpa only [Finset.sum_filter] using
    (Finset.sum_subtype (p := P) (Finset.univ.filter P) (by intro a; simp) f).symm

theorem ascending_edge_weight (h : Depth) (M J : ℕ) (a : AscendingEdge h M) :
    (rationalWeight h M J (.inl a) : ℝ) = boundedWeight h.val M a.val := by
  rw [rationalWeight_as_zpow]
  change (2 : ℝ) ^ (-((∑ i : Fin h.val, ((a.val i).val + 1) : ℕ) : ℤ)) = _
  exact (productWeight_exponent h.val (fun i => (a.val i).val)).symm

theorem exiting_edge_weight (h : Depth) (M J : ℕ) (k : Fin (J - 1)) (v : Vertex h M) :
    (rationalWeight h M J (.inr (k, v)) : ℝ) =
      ((1 / 2 : ℝ) * atom k.val) * boundedWeight h.val M v := by
  rw [edge_weight]
  exact exit_weight_product h k.val (fun i => (v i).val)

theorem ascending_mass (h : Depth) (M J : ℕ) (hM : 0 < M) :
    (∑ a : AscendingEdge h M, (rationalWeight h M J (.inl a) : ℝ)) =
      ((1 / 2 : ℝ) - (2 : ℝ) ^ (-(M : ℤ))) *
        (1 - (2 : ℝ) ^ (-(M : ℤ))) ^ (h.val - 1) := by
  classical
  simp_rw [ascending_edge_weight]
  refine (@sum_subtype_mask (Vertex h M) _ (fun v => 0 < (v (zeroIndex h)).val)
    (fun v => Nat.decLt 0 (v (zeroIndex h)).val) (boundedWeight h.val M)).trans ?_
  rcases h with ⟨r, hr⟩
  cases r with
  | zero => omega
  | succ n => exact boundedWeight_positive_head_sum n M hM

theorem exiting_mass (h : Depth) (M J : ℕ) (hJ : 1 ≤ J) :
    (∑ p : Fin (J - 1) × Vertex h M, (rationalWeight h M J (.inr p) : ℝ)) =
      ((1 / 2 : ℝ) - (2 : ℝ) ^ (-(J : ℤ))) *
        (1 - (2 : ℝ) ^ (-(M : ℤ))) ^ h.val := by
  classical
  rw [Fintype.sum_prod_type]
  simp_rw [exiting_edge_weight, ← Finset.mul_sum, boundedWeight_sum]
  rw [← Finset.sum_mul, exit_atom_sum J hJ]

theorem retained_mass_formula (h : Depth) (M J : ℕ) (hM : 0 < M) (hJ : 1 ≤ J) :
    retainedMass h M J =
      ((1 / 2 : ℝ) - (2 : ℝ) ^ (-(M : ℤ))) * (1 - (2 : ℝ) ^ (-(M : ℤ))) ^ (h.val - 1) +
      ((1 / 2 : ℝ) - (2 : ℝ) ^ (-(J : ℤ))) * (1 - (2 : ℝ) ^ (-(M : ℤ))) ^ h.val := by
  unfold retainedMass
  rw [Fintype.sum_sum_type, ascending_mass h M J hM, exiting_mass h M J hJ]

noncomputable def retainedLabels (h : Depth) (M J : ℕ) : Finset (Edge h) :=
  Finset.univ.image (edgeLabel h M J)

theorem retainedLabels_mem (h : Depth) (M J : ℕ) (e : Edge h) :
    e ∈ retainedLabels h M J ↔ Retained h M J e := by
  simp only [retainedLabels, Finset.mem_image, Finset.mem_univ, true_and]
  exact (retained_image h M J e).symm

theorem retained_mass_as_sum (h : Depth) (M J : ℕ) :
    retainedMass h M J = ∑ e ∈ retainedLabels h M J, weight h e := by
  unfold retainedMass retainedLabels
  rw [Finset.sum_image (fun a _ b _ hab => edgeLabel_injective h M J hab)]
  apply Finset.sum_congr rfl
  intro a _
  exact edge_weight h M J a

theorem kept_mask_summable (h : Depth) (M J : ℕ) :
    Summable (fun e : Edge h => if Retained h M J e then weight h e else 0) := by
  apply Summable.of_nonneg_of_le
    (fun e => by split_ifs; exact le_of_lt (weight_positive h e); exact le_rfl)
    (fun e => by split_ifs; exact le_rfl; exact le_of_lt (weight_positive h e))
    (weight_summable h)

theorem discarded_mask_summable (h : Depth) (M J : ℕ) :
    Summable (fun e : Edge h => if Retained h M J e then 0 else weight h e) := by
  apply Summable.of_nonneg_of_le
    (fun e => by split_ifs; exact le_rfl; exact le_of_lt (weight_positive h e))
    (fun e => by split_ifs; exact le_of_lt (weight_positive h e); exact le_rfl)
    (weight_summable h)

theorem kept_mass_tsum (h : Depth) (M J : ℕ) :
    (∑' e : Edge h, if Retained h M J e then weight h e else 0) = retainedMass h M J := by
  rw [tsum_eq_sum (s := retainedLabels h M J) (fun e he => by
    have hn : ¬ Retained h M J e := mt (retainedLabels_mem h M J e).mpr he
    simp only [hn, ite_false])]
  calc
    _ = ∑ e ∈ retainedLabels h M J, weight h e :=
      Finset.sum_congr rfl (fun e he => ite_eq_left ((retainedLabels_mem h M J e).mp he))
    _ = retainedMass h M J := (retained_mass_as_sum h M J).symm

theorem discarded_mass_complement (h : Depth) (M J : ℕ) :
    discardedMass h M J = 1 - retainedMass h M J := by
  have hp (e : Edge h) : (if Retained h M J e then weight h e else 0) +
      (if Retained h M J e then 0 else weight h e) = weight h e := by
    split_ifs <;> simp
  have hs : retainedMass h M J + discardedMass h M J = 1 := by
    rw [← kept_mass_tsum h M J]
    unfold discardedMass
    rw [← (kept_mask_summable h M J).tsum_add (discarded_mask_summable h M J)]
    simp_rw [hp]
    exact weight_tsum h
  linarith

theorem truncation_mass_identity : TruncationMassIdentity := by
  intro h M J hM hJ
  exact ⟨retained_mass_formula h M J (by omega) (by omega),
    discarded_mask_summable h M J, discarded_mass_complement h M J⟩

theorem one_sub_pow_le_mul (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (n : ℕ) :
    1 - (1 - x) ^ n ≤ (n : ℝ) * x := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp : (1 - x) ^ n ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    have hm := mul_le_mul_of_nonneg_right hp hx0
    simp only [one_mul] at hm
    simp only [pow_succ, Nat.cast_add, Nat.cast_one]
    nlinarith only [ih, hm]

theorem dyadic_nonneg (n : ℕ) : (0 : ℝ) ≤ 2 ^ (-(n : ℤ)) := by positivity

theorem dyadic_le_one (n : ℕ) : (2 : ℝ) ^ (-(n : ℤ)) ≤ 1 := by
  rw [← half_pow_eq_zpow]
  exact pow_le_one₀ (by norm_num) (by norm_num)

theorem discarded_mass_bound : DiscardedMassBound := by
  intro h M J hM hJ
  refine ⟨?_, ?_⟩
  · apply tsum_nonneg
    intro e
    split_ifs
    · exact le_rfl
    · exact le_of_lt (weight_positive h e)
  · let t : ℝ := (2 : ℝ) ^ (-(M : ℤ))
    let u : ℝ := (2 : ℝ) ^ (-(J : ℤ))
    have ht0 : 0 ≤ t := dyadic_nonneg M
    have ht1 : t ≤ 1 := dyadic_le_one M
    have hu0 : 0 ≤ u := dyadic_nonneg J
    have ha := one_sub_pow_le_mul t ht0 ht1 (h.val - 1)
    have hb := one_sub_pow_le_mul t ht0 ht1 h.val
    have hpa : (1 - t) ^ (h.val - 1) ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    have hpb : (1 - t) ^ h.val ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    have hta : t * (1 - t) ^ (h.val - 1) ≤ t := mul_le_of_le_one_right ht0 hpa
    have hub : u * (1 - t) ^ h.val ≤ u := mul_le_of_le_one_right hu0 hpb
    have hc : ((h.val - 1 : ℕ) : ℝ) = (h.val : ℝ) - 1 := by
      rw [Nat.cast_sub (by have hp := h.property; omega : 1 ≤ h.val), Nat.cast_one]
    rw [discarded_mass_complement, retained_mass_formula h M J (by omega) (by omega)]
    change 1 - (((1 / 2 : ℝ) - t) * (1 - t) ^ (h.val - 1) +
      ((1 / 2 : ℝ) - u) * (1 - t) ^ h.val) ≤ ((h.val : ℝ) + 1) * t + u
    nlinarith only [ha, hb, hta, hub, hc, ht0]

end
end ExternalO3OptimizationMass
