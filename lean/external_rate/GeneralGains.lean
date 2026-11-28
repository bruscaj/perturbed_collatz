import GeneralArithmetic
import Gains

/-! Exact source-model increments; equality remains failure at every finite depth. -/
namespace ExternalO3GeneralGains
open ExternalO3GeneralDraft ExternalO3GeneralArithmetic
open ExternalO3Spec (IsOddSeed stride blockLength strideValuation)
open ExternalO3Arithmetic

theorem positive_window_decode (h : Depth) (x : ℕ) (hx : IsOddSeed x) :
    positiveWindow h (positiveOffsets h (window h x)) = window h x := by
  funext i
  have hp := window_validity h x hx i
  simp only [positiveWindow, positiveOffsets]
  omega

theorem ascending_window_decode (h : Depth) (x : ℕ) (hx : IsOddSeed x)
    (hr : 2 ≤ blockLength x) :
    ascendingWindow h (ascendingOffsets h (window h x)) = window h x := by
  funext i
  have hp := window_validity h x hx i
  by_cases hi : i.val = 0
  · have hh : window h x i = blockLength x := by simp [window, futureBlockSeed, hi]
    simp only [ascendingWindow, ascendingOffsets, hi, ite_true]
    omega
  · simp only [ascendingWindow, ascendingOffsets, hi, ite_false]
    omega

theorem literal_gain_identity : LiteralGainIdentity := by
  intro h φ n
  let x := 2 * n + 1
  have hx : IsOddSeed x := ⟨by omega, by omega⟩
  have hlog := ExternalO3Gains.literal_log_increment x hx
  change rawPotential h φ (stride x) - rawPotential h φ x =
    gain h φ (label h n) + ExternalO3Gains.logError x
  by_cases hr : 2 ≤ blockLength x
  · have hd := ascending_window_decode h x hx hr
    have ht := ascending_window_transport h x hx hr
    have hk := valuation_one_of_long_block x hx hr
    have hg : gain h φ (label h n) = Real.log 3 - Real.log 2 +
        φ (window h (stride x)) - φ (window h x) := by
      simp only [label, show 2 ≤ blockLength (2 * n + 1) from hr, ite_true, gain]
      rw [hd, ← ht, Real.log_div (by norm_num) (by norm_num)]
    rw [hk] at hlog
    simp only [Nat.cast_one, one_mul] at hlog
    rw [hg]
    unfold rawPotential
    linarith
  · have hb : blockLength x = 1 := by
      have hp := block_length_positive x hx
      omega
    have hk := exit_valuation_of_short_block x hx hb
    have hd := positive_window_decode h (stride x) (stride_output x)
    have ht := exit_window_transport h x hb
    have hg : gain h φ (label h n) = Real.log 3 - (strideValuation x : ℝ) * Real.log 2 +
        φ (window h (stride x)) - φ (window h x) := by
      simp only [label, show ¬2 ≤ blockLength (2 * n + 1) from hr, ite_false, gain]
      rw [hd, Nat.sub_add_cancel hk, ← ht]
    rw [hg]
    unfold rawPotential
    linarith

theorem cell_stabilization : CellStabilization := by
  intro h φ e
  obtain ⟨M, hM⟩ := ExternalO3Gains.stable_seed_error (gain h φ e)
  refine ⟨M, fun n hn he => ?_⟩
  have hx : IsOddSeed (2 * n + 1) := ⟨by omega, by omega⟩
  have hinc := literal_gain_identity h φ n
  rw [he] at hinc
  change (IsOddSeed (2 * n + 1) ∧
    rawPotential h φ (stride (2 * n + 1)) ≥ rawPotential h φ (2 * n + 1)) ↔ _
  rw [and_iff_right hx]
  change (rawPotential h φ (2 * n + 1) ≤ rawPotential h φ (stride (2 * n + 1))) ↔
    0 ≤ gain h φ e
  rw [← sub_nonneg, hinc]
  exact hM n hn

end ExternalO3GeneralGains
