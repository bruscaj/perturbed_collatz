import OptimizationCode
import Mathlib.Algebra.BigOperators.Fin

/-! Exact little-endian radix coding, including the graph's labelled vertices.
No cycle-feasibility or optimization correctness assertion occurs here. -/
namespace ExternalO3OptimizationVertexCode

open ExternalO3OptimizationCode ExternalO3OptimizationDraft
open scoped BigOperators

/-- Coordinate zero is the least significant digit. -/
def radixEquiv (M n : ℕ) (_hM : 0 < M) : (Fin n → Fin M) ≃ Fin (M ^ n) :=
  finFunctionFinEquiv

theorem radixEquiv_symm_digit (M n : ℕ) (hM : 0 < M)
    (c : Fin (M ^ n)) (i : Fin n) :
    ((radixEquiv M n hM).symm c i).val = digit M c.val i.val := by
  rfl

theorem radixEquiv_apply_sum (M n : ℕ) (hM : 0 < M) (v : Fin n → Fin M) :
    (radixEquiv M n hM v).val = ∑ i : Fin n, (v i).val * M ^ i.val := by
  rfl

theorem radixEquiv_digit (M n : ℕ) (hM : 0 < M)
    (v : Fin n → Fin M) (i : Fin n) :
    digit M (radixEquiv M n hM v).val i.val = (v i).val := by
  rw [← radixEquiv_symm_digit M n hM]
  exact congrArg (fun f : Fin n → Fin M => (f i).val)
    ((radixEquiv M n hM).symm_apply_apply v)

/-- Frozen vertices have exactly `depth p` positive-length offsets in base `base p`. -/
def vertexCodeEquiv (p : Input) :
    Vertex (ExternalO3RateDraft.succDepth p.1) (base p) ≃ Fin (vertices p) :=
  radixEquiv (base p) (depth p) (by unfold base; omega)

theorem vertexCodeEquiv_symm_digit (p : Input) (c : Fin (vertices p))
    (i : Fin (depth p)) :
    ((vertexCodeEquiv p).symm c i).val = digit (base p) c.val i.val := by
  rfl

theorem vertexCodeEquiv_digit (p : Input)
    (v : Vertex (ExternalO3RateDraft.succDepth p.1) (base p)) (i : Fin (depth p)) :
    digit (base p) (vertexCodeEquiv p v).val i.val = (v i).val :=
  radixEquiv_digit (base p) (depth p) (by unfold base; omega) v i

theorem radixEquiv_head_tail (M n : ℕ) (hM : 0 < M) (v : Fin (n + 1) → Fin M) :
    (radixEquiv M (n + 1) hM v).val =
      (v 0).val + M * (radixEquiv M n hM (fun i => v i.succ)).val := by
  simp only [radixEquiv_apply_sum, Fin.sum_univ_succ, Fin.val_zero, pow_zero,
    mul_one, Fin.val_succ, pow_succ']
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem radixEquiv_dropLast_mod (M n : ℕ) (hM : 0 < M)
    (v : Fin (n + 1) → Fin M) :
    (radixEquiv M (n + 1) hM v).val % M ^ n =
      (radixEquiv M n hM (fun i => v i.castSucc)).val := by
  have heq : (radixEquiv M (n + 1) hM v).val =
      (radixEquiv M n hM (fun i => v i.castSucc)).val +
        (v (Fin.last n)).val * M ^ n := by
    simp only [radixEquiv_apply_sum, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]
  rw [heq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt]
  exact (radixEquiv M n hM (fun i => v i.castSucc)).isLt

theorem vertexCodeEquiv_ascTarget (p : Input)
    (v : Vertex (ExternalO3RateDraft.succDepth p.1) (base p))
    (hv : 0 < (v (ExternalO3GeneralDraft.zeroIndex (ExternalO3RateDraft.succDepth p.1))).val) :
    (vertexCodeEquiv p (ascTarget (ExternalO3RateDraft.succDepth p.1) (base p) v)).val =
      (vertexCodeEquiv p v).val - 1 := by
  change (radixEquiv (base p) (p.1 + 1) _ _).val =
    (radixEquiv (base p) (p.1 + 1) _ v).val - 1
  erw [radixEquiv_head_tail, radixEquiv_head_tail]
  have ht : (fun i : Fin p.1 =>
      ascTarget (ExternalO3RateDraft.succDepth p.1) (base p) v i.succ) =
      (fun i : Fin p.1 => v i.succ) := by
    funext i
    simp [ascTarget]
  rw [ht]
  simp only [ascTarget, Fin.val_zero, ↓reduceIte]
  change 0 < (v (0 : Fin (p.1 + 1))).val at hv
  omega

theorem vertexCodeEquiv_exitSource (p : Input)
    (v : Vertex (ExternalO3RateDraft.succDepth p.1) (base p)) :
    (vertexCodeEquiv p (exitSource (ExternalO3RateDraft.succDepth p.1) (base p) v)).val =
      base p * ((vertexCodeEquiv p v).val % base p ^ (depth p - 1)) := by
  change (radixEquiv (base p) (p.1 + 1) _ _).val =
    base p * ((radixEquiv (base p) (p.1 + 1) _ v).val % base p ^ (p.1 + 1 - 1))
  erw [Nat.add_sub_cancel, radixEquiv_head_tail, radixEquiv_dropLast_mod]
  have ht : (fun i : Fin p.1 =>
      exitSource (ExternalO3RateDraft.succDepth p.1) (base p) v i.succ) =
      (fun i : Fin p.1 => v i.castSucc) := by
    funext i
    simp only [exitSource, Fin.val_succ, Nat.add_eq_zero_iff, one_ne_zero,
      and_false, ↓reduceIte, Nat.add_sub_cancel]
    rfl
  rw [ht]
  simp [exitSource]

end ExternalO3OptimizationVertexCode
