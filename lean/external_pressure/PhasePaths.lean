import PhaseCocycle

/-! Complete bounded enumeration of the frozen natural closed phase paths.
The n bound is proved from the exact tick alphabet, not chosen as a cutoff. -/
namespace ExternalBridgePressurePaths
open ExternalBridgePressureDraft ExternalBridgePressurePhase

theorem natural_depth_bound (x : ℝ) (n : ℕ) (j : Fin (n+1) → ℕ)
    (hj : NaturalPathLegal x n j) (t : Fin (n+1)) : j t ≤ t.val := by
  induction t using Fin.induction with
  | zero => simpa only [hj.1,Fin.val_zero] using (Nat.zero_le 0)
  | succ i ih =>
    have hs := hj.2.2 i
    have hg := phase_increment_alphabet x i.val
    have hc : (j i.castSucc : ℤ) ≤ (i.val : ℤ) := by exact_mod_cast ih
    have hb : (j i.succ : ℤ) ≤ ((i.val+1 : ℕ) : ℤ) := by
      rcases hg with hg | hg <;> rw [hg] at hs <;> push_cast <;> omega
    exact_mod_cast hb

theorem natural_path_encoding (x : ℝ) (n : ℕ) (j : Fin (n+1) → ℕ) :
    NaturalPathLegal x n j ↔
      ∃ k : Path n, PathLegal x n k ∧ ∀ t, (k t).val = j t := by
  constructor
  · intro hj
    let k : Path n := fun t => ⟨j t,(natural_depth_bound x n j hj t).trans_lt t.isLt⟩
    refine ⟨k,?_,fun _ => rfl⟩
    change NaturalPathLegal x n (fun t => j t)
    exact hj
  · rintro ⟨k,hk,he⟩
    have hf : (fun t => (k t).val) = j := funext he
    unfold PathLegal at hk
    rwa [hf] at hk

theorem phase_path_completeness : PhasePathCompleteness := by
  intro x _ _ n
  exact ⟨fun j hj t => natural_depth_bound x n j hj t,natural_path_encoding x n⟩

end ExternalBridgePressurePaths
