import RateMarkerUpper
import RateSymmetry
import GeneralMarginal

/-! Finite product maximum-event masses; no infinite orbit distribution. -/
namespace ExternalO3RateMaxMass
noncomputable section
open scoped BigOperators
open ExternalO3GeneralWeights ExternalO3GeneralMarginal ExternalO3RateSymmetry
local instance (P : Prop) : Decidable P := Classical.propDecidable P

noncomputable def eventMass (n : ℕ) (P : (Fin n → ℕ) → Prop) : ℝ := by
  classical
  exact ∑' a : Fin n → ℕ, if P a then productWeight n a else 0

def StrictMax (n : ℕ) (i : Fin n) (a : Fin n → ℕ) : Prop :=
  ∀ j : Fin n, j ≠ i → a j < a i

def WeakHead (n : ℕ) (a : Fin (n + 1) → ℕ) : Prop :=
  ∀ j : Fin n, a j.succ ≤ a 0

def WeakPrefix (n : ℕ) (a : Fin (n + 2) → ℕ) : Prop :=
  ∀ j : Fin n, a j.succ.castSucc ≤ a 0

theorem event_mask_summable (n : ℕ) (P : (Fin n → ℕ) → Prop) :
    Summable (fun a => if P a then productWeight n a else 0) := by
  classical
  exact masked_summable (productWeight n)
    (fun a => le_of_lt (productWeight_positive n a)) (productWeight_summable n) P

theorem eventMass_congr (n : ℕ) (P Q : (Fin n → ℕ) → Prop)
    (hPQ : ∀ a, P a ↔ Q a) : eventMass n P = eventMass n Q := by
  classical
  unfold eventMass
  apply tsum_congr
  intro a
  rw [hPQ a]

theorem eventMass_reindex (n : ℕ) (σ : Equiv.Perm (Fin n))
    (P : (Fin n → ℕ) → Prop) :
    eventMass n (fun a => P (reindex n σ a)) = eventMass n P := by
  classical
  have ht := weighted_tsum_reindex n σ (fun a => if P a then (1 : ℝ) else 0)
  simpa only [eventMass, mul_ite, mul_one, mul_zero] using ht

theorem strictMax_reindex (n : ℕ) (σ : Equiv.Perm (Fin n)) (i : Fin n)
    (a : Fin n → ℕ) : StrictMax n i (reindex n σ a) ↔ StrictMax n (σ i) a := by
  change (∀ j, j ≠ i → a (σ j) < a (σ i)) ↔ _
  constructor
  · intro hh j hj
    have hn : σ.symm j ≠ i := by
      intro he
      apply hj
      rw [← he]
      simp
    simpa using hh (σ.symm j) hn
  · intro hh j hj
    exact hh (σ j) (fun he => hj (σ.injective he))

theorem strict_max_mass_eq (n : ℕ) (i j : Fin n) :
    eventMass n (StrictMax n i) = eventMass n (StrictMax n j) := by
  calc
    _ = eventMass n (fun a => StrictMax n i (reindex n (Equiv.swap i j) a)) :=
      (eventMass_reindex n (Equiv.swap i j) (StrictMax n i)).symm
    _ = _ := eventMass_congr n _ _ (fun a => by
      rw [strictMax_reindex, Equiv.swap_apply_left])

theorem strictMax_unique (n : ℕ) (a : Fin n → ℕ) (i j : Fin n)
    (hi : StrictMax n i a) (hj : StrictMax n j a) : i = j := by
  by_contra hn
  have h1 := hi j (Ne.symm hn)
  have h2 := hj i hn
  omega

theorem strict_masks_sum_le (n : ℕ) (a : Fin n → ℕ) :
    (∑ i : Fin n, if StrictMax n i a then productWeight n a else 0) ≤ productWeight n a := by
  classical
  by_cases hh : ∃ i, StrictMax n i a
  · obtain ⟨i, hi⟩ := hh
    have he (j : Fin n) : StrictMax n j a ↔ j = i := by
      constructor
      · exact fun hj => strictMax_unique n a j i hj hi
      · rintro rfl
        exact hi
    simp_rw [he]
    simp
  · have hn : ∀ i, ¬ StrictMax n i a := by simpa using hh
    simp only [hn, ite_false, Finset.sum_const_zero]
    exact le_of_lt (productWeight_positive n a)

theorem strict_max_masses_sum_le (n : ℕ) :
    (∑ i : Fin n, eventMass n (StrictMax n i)) ≤ 1 := by
  classical
  have hs := hasSum_sum (s := Finset.univ)
    (fun (i : Fin n) _ => (event_mask_summable n (StrictMax n i)).hasSum)
  have hl := Summable.tsum_le_tsum (strict_masks_sum_le n) hs.summable (productWeight_summable n)
  rw [hs.tsum_eq, productWeight_tsum] at hl
  exact hl

theorem strict_max_mass_le (n : ℕ) (hn : 0 < n) (i : Fin n) :
    eventMass n (StrictMax n i) ≤ 1 / (n : ℝ) := by
  have he : (∑ j : Fin n, eventMass n (StrictMax n j)) =
      (n : ℝ) * eventMass n (StrictMax n i) := by
    calc
      _ = ∑ _j : Fin n, eventMass n (StrictMax n i) :=
        Finset.sum_congr rfl (fun j _ => (strict_max_mass_eq n i j).symm)
      _ = _ := by simp
  have hl := strict_max_masses_sum_le n
  rw [he] at hl
  apply (le_div_iff₀ (Nat.cast_pos.mpr hn)).2
  nlinarith only [hl]

theorem atom_successor (a : ℕ) : atom (a + 1) = (1 / 2 : ℝ) * atom a := by
  simp only [atom_geometric, pow_succ]
  ring

theorem atom_prefix_sum (a : ℕ) :
    (∑ t ∈ Finset.range (a + 1), atom t) = 1 - atom a := by
  induction a with
  | zero => norm_num [atom]
  | succ a ih =>
    rw [Finset.sum_range_succ, ih, atom_successor]
    ring

theorem atom_le_tsum (a : ℕ) : (∑' t : ℕ, if t ≤ a then atom t else 0) = 1 - atom a := by
  classical
  rw [tsum_eq_sum (s := Finset.range (a + 1)) (fun t ht => by
    have hn : ¬ t ≤ a := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using ht
    simp [hn])]
  calc
    _ = ∑ t ∈ Finset.range (a + 1), atom t := Finset.sum_congr rfl (fun t ht =>
      ite_eq_left (Nat.le_of_lt_succ (Finset.mem_range.mp ht)))
    _ = _ := atom_prefix_sum a

theorem bounded_product_mass (n a : ℕ) :
    eventMass n (fun b => ∀ j, b j ≤ a) = (1 - atom a) ^ n := by
  classical
  induction n with
  | zero =>
    have he (b : Fin 0 → ℕ) : ∀ j, b j ≤ a := fun j => Fin.elim0 j
    simpa only [eventMass, he, forall_true_iff, ite_true, pow_zero] using productWeight_tsum 0
  | succ n ih =>
    let P : (Fin n → ℕ) → Prop := fun b => ∀ j, b j ≤ a
    let e := Fin.consEquiv (fun _ : Fin (n + 1) => ℕ)
    have hs := (event_mask_summable (n + 1) (fun b => ∀ j, b j ≤ a)).comp_injective e.injective
    simp only [Function.comp_def] at hs
    unfold eventMass
    rw [← e.tsum_eq, hs.tsum_prod]
    simp only [e, Fin.consEquiv, Equiv.coe_fn_mk, Fin.forall_fin_succ,
      Fin.cons_zero, Fin.cons_succ, productWeight_cons]
    have hi (t : ℕ) :
        (∑' b : Fin n → ℕ, if t ≤ a ∧ (∀ j, b j ≤ a) then atom t * productWeight n b else 0) =
          if t ≤ a then atom t * eventMass n P else 0 := by
      by_cases ht : t ≤ a
      · simp only [ht, true_and, ite_true]
        simpa only [eventMass, mul_ite, mul_zero] using
          (event_mask_summable n P).tsum_mul_left (atom t)
      · simp only [ht, false_and, ite_false, tsum_zero]
    simp_rw [hi]
    have ha := masked_summable atom (fun t => le_of_lt (atom_positive t))
      atom_summable (fun t => t ≤ a)
    have hh : (∑' t : ℕ, if t ≤ a then atom t * eventMass n P else 0) =
        (∑' t : ℕ, if t ≤ a then atom t else 0) * eventMass n P := by
      simpa only [ite_mul, zero_mul] using ha.tsum_mul_right (eventMass n P)
    rw [hh, atom_le_tsum]
    change (1 - atom a) * eventMass n (fun b => ∀ j, b j ≤ a) = _
    rw [ih, pow_succ]
    ring

theorem weak_head_mass_eq (n : ℕ) :
    eventMass (n + 1) (WeakHead n) = ∑' a : ℕ, atom a * (1 - atom a) ^ n := by
  classical
  let e := Fin.consEquiv (fun _ : Fin (n + 1) => ℕ)
  have hs := (event_mask_summable (n + 1) (WeakHead n)).comp_injective e.injective
  simp only [Function.comp_def] at hs
  unfold eventMass
  rw [← e.tsum_eq, hs.tsum_prod]
  simp only [e, Fin.consEquiv, Equiv.coe_fn_mk, WeakHead,
    Fin.cons_zero, Fin.cons_succ, productWeight_cons]
  apply tsum_congr
  intro t
  have hh := (event_mask_summable n (fun b => ∀ j, b j ≤ t)).tsum_mul_left (atom t)
  have he : (∑' b : Fin n → ℕ, if ∀ j, b j ≤ t then atom t * productWeight n b else 0) =
      atom t * eventMass n (fun b => ∀ j, b j ≤ t) := by
    simpa only [eventMass, mul_ite, mul_zero] using hh
  rw [he, bounded_product_mass]

theorem atom_eq_half_pow (a : ℕ) : atom a = (1 / 2 : ℝ) ^ (a + 1) := by
  rw [atom_geometric, pow_succ]
  ring

theorem weak_head_mass_le (n : ℕ) :
    eventMass (n + 1) (WeakHead n) ≤ 2 / ((n : ℝ) + 1) := by
  rw [weak_head_mass_eq]
  simp_rw [atom_eq_half_pow]
  exact ExternalO3RateMarkerUpper.weak_max_tsum_le n

theorem weakPrefix_snoc (n z : ℕ) (b : Fin (n + 1) → ℕ) :
    WeakPrefix n (Fin.snoc b z) ↔ WeakHead n b := by
  change (∀ j : Fin n, (Fin.snoc b z : Fin (n + 2) → ℕ) j.succ.castSucc ≤
    (Fin.snoc b z : Fin (n + 2) → ℕ) (0 : Fin (n + 1)).castSucc) ↔ _
  simp only [Fin.snoc_castSucc, WeakHead]

theorem weak_prefix_mass_eq (n : ℕ) :
    eventMass (n + 2) (WeakPrefix n) = eventMass (n + 1) (WeakHead n) := by
  classical
  let e := Fin.snocEquiv (fun _ : Fin (n + 2) => ℕ)
  have hs := (event_mask_summable (n + 2) (WeakPrefix n)).comp_injective e.injective
  simp only [Function.comp_def] at hs
  unfold eventMass
  rw [← e.tsum_eq, hs.tsum_prod]
  simp only [e, Fin.snocEquiv, Equiv.coe_fn_mk, productWeight_snoc, weakPrefix_snoc]
  have hi (z : ℕ) :
      (∑' b : Fin (n + 1) → ℕ, if WeakHead n b then productWeight (n + 1) b * atom z else 0) =
        eventMass (n + 1) (WeakHead n) * atom z := by
    simpa only [eventMass, ite_mul, zero_mul] using
      (event_mask_summable (n + 1) (WeakHead n)).tsum_mul_right (atom z)
  simp_rw [hi]
  rw [atom_summable.tsum_mul_left, atom_tsum, mul_one]
  rfl

theorem weak_prefix_mass_le (n : ℕ) :
    eventMass (n + 2) (WeakPrefix n) ≤ 2 / ((n : ℝ) + 1) := by
  rw [weak_prefix_mass_eq]
  exact weak_head_mass_le n

end
end ExternalO3RateMaxMass
