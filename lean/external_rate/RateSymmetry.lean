import RateMoments

/-! Finite-coordinate exchangeability from the explicit geometric product. -/
namespace ExternalO3RateSymmetry
open ExternalO3GeneralWeights
open scoped BigOperators

/-- Reindex finite offset vectors, not integer trajectories. -/
def reindex (n : ℕ) (σ : Equiv.Perm (Fin n)) : (Fin n → ℕ) ≃ (Fin n → ℕ) where
  toFun r := fun i => r (σ i)
  invFun r := fun i => r (σ.symm i)
  left_inv r := by funext i; simp
  right_inv r := by funext i; simp

theorem productWeight_reindex (n : ℕ) (σ : Equiv.Perm (Fin n)) (r : Fin n → ℕ) :
    productWeight n (reindex n σ r) = productWeight n r := by
  exact Equiv.prod_comp σ (fun i => atom (r i))

/-- A weighted sum is invariant under every finite-coordinate permutation. -/
theorem weighted_tsum_reindex (n : ℕ) (σ : Equiv.Perm (Fin n))
    (f : (Fin n → ℕ) → ℝ) :
    (∑' r : Fin n → ℕ, productWeight n r * f (reindex n σ r)) =
      ∑' r : Fin n → ℕ, productWeight n r * f r := by
  calc
    _ = ∑' r : Fin n → ℕ, productWeight n (reindex n σ r) * f (reindex n σ r) := by
      apply tsum_congr
      intro r
      rw [productWeight_reindex]
    _ = _ := (reindex n σ).tsum_eq (fun r => productWeight n r * f r)

end ExternalO3RateSymmetry
