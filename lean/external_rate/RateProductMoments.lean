import RateMoments

/-! Exact moments of the finite geometric product. No trajectory-iid premise. -/
namespace ExternalO3RateProductMoments
open ExternalO3GeneralWeights ExternalO3RateMoments
open scoped BigOperators

def lengthSum (n : ℕ) (a : Fin n → ℕ) : ℝ := ∑ i, ((a i : ℝ) + 1)

def centeredSum (n : ℕ) (a : Fin n → ℕ) : ℝ := ∑ i, ((a i : ℝ) - 1)

theorem lengthSum_nonneg (n : ℕ) (a : Fin n → ℕ) : 0 ≤ lengthSum n a := by
  exact Finset.sum_nonneg (fun i _ => by positivity)

theorem lengthSum_cons (n a : ℕ) (b : Fin n → ℕ) :
    lengthSum (n + 1) (Fin.cons a b) = ((a : ℝ) + 1) + lengthSum n b := by
  simp [lengthSum, Fin.sum_univ_succ]

theorem centeredSum_eq (n : ℕ) (a : Fin n → ℕ) :
    centeredSum n a = lengthSum n a - 2 * (n : ℝ) := by
  simp only [centeredSum, lengthSum, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  ring

theorem product_hasSum_nonneg {α β : Type*} {f : α → ℝ} {g : β → ℝ} {s t : ℝ}
    (hf0 : ∀ a, 0 ≤ f a) (hg0 : ∀ b, 0 ≤ g b)
    (hf : HasSum f s) (hg : HasSum g t) :
    HasSum (fun p : α × β => f p.1 * g p.2) (s * t) :=
  hf.mul hg (independent_product_summable f g hf0 hg0 hf.summable hg.summable)

theorem tuple_hasSum_of_cons (n : ℕ) (f : (Fin (n + 1) → ℕ) → ℝ) (s : ℝ)
    (hf : HasSum (fun p : ℕ × (Fin n → ℕ) => f (Fin.cons p.1 p.2)) s) : HasSum f s := by
  apply (Fin.consEquiv (fun _ : Fin (n + 1) => ℕ)).hasSum_iff.mp
  simpa [Function.comp_def, Fin.consEquiv] using hf

theorem length_first_hasSum (n : ℕ) :
    HasSum (fun a : Fin n → ℕ => productWeight n a * lengthSum n a) (2 * (n : ℝ)) := by
  induction n with
  | zero => simp [lengthSum]
  | succ n ih =>
    have h₁ := product_hasSum_nonneg
      (fun a : ℕ => mul_nonneg (le_of_lt (atom_positive a)) (by positivity))
      (fun b : Fin n → ℕ => le_of_lt (productWeight_positive n b))
      atom_length_hasSum (productWeight_hasSum n)
    have h₂ := product_hasSum_nonneg
      (fun a : ℕ => le_of_lt (atom_positive a))
      (fun b : Fin n → ℕ => mul_nonneg (le_of_lt (productWeight_positive n b)) (lengthSum_nonneg n b))
      atom_hasSum ih
    apply tuple_hasSum_of_cons n
    convert h₁.add h₂ using 1
    · funext p
      rw [productWeight_cons, lengthSum_cons]
      ring
    · push_cast
      ring

theorem length_second_hasSum (n : ℕ) :
    HasSum (fun a : Fin n → ℕ => productWeight n a * (lengthSum n a) ^ 2)
      (4 * (n : ℝ) ^ 2 + 2 * (n : ℝ)) := by
  induction n with
  | zero => simp [lengthSum]
  | succ n ih =>
    have h₁ := product_hasSum_nonneg
      (fun a : ℕ => mul_nonneg (le_of_lt (atom_positive a)) (sq_nonneg _))
      (fun b : Fin n → ℕ => le_of_lt (productWeight_positive n b))
      atom_length_sq_hasSum (productWeight_hasSum n)
    have h₂ := product_hasSum_nonneg
      (fun a : ℕ => mul_nonneg (le_of_lt (atom_positive a)) (by positivity))
      (fun b : Fin n → ℕ => mul_nonneg (le_of_lt (productWeight_positive n b)) (lengthSum_nonneg n b))
      atom_length_hasSum (length_first_hasSum n)
    have h₃ := product_hasSum_nonneg
      (fun a : ℕ => le_of_lt (atom_positive a))
      (fun b : Fin n → ℕ => mul_nonneg (le_of_lt (productWeight_positive n b)) (sq_nonneg _))
      atom_hasSum ih
    apply tuple_hasSum_of_cons n
    convert (h₁.add (h₂.mul_left 2)).add h₃ using 1
    · funext p
      rw [productWeight_cons, lengthSum_cons]
      ring
    · push_cast
      ring

theorem centered_first_hasSum (n : ℕ) :
    HasSum (fun a : Fin n → ℕ => productWeight n a * centeredSum n a) 0 := by
  convert (length_first_hasSum n).sub ((productWeight_hasSum n).mul_left (2 * (n : ℝ))) using 1
  · funext a
    rw [centeredSum_eq]
    ring
  · ring

theorem centered_second_hasSum (n : ℕ) :
    HasSum (fun a : Fin n → ℕ => productWeight n a * (centeredSum n a) ^ 2)
      (2 * (n : ℝ)) := by
  convert ((length_second_hasSum n).sub ((length_first_hasSum n).mul_left (4 * (n : ℝ)))).add
    ((productWeight_hasSum n).mul_left (4 * (n : ℝ) ^ 2)) using 1
  · funext a
    rw [centeredSum_eq]
    ring
  · ring

end ExternalO3RateProductMoments
