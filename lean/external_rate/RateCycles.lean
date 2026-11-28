import RateExpectedTypes

/-! Pointwise finite cyclic histories. No expectations of the correction. -/
namespace ExternalO3RateCycles
open scoped BigOperators
open ExternalO3GeneralDraft ExternalO3RateDraft

theorem cyclicLength_pos (h : Depth) (r : History h) (i : ℕ) :
    0 < cyclicLength h r i := by
  simp [cyclicLength]

theorem sum_ascent_gains (h : Depth) (φ : Correction h) (r : History h)
    (i t : ℕ) :
    (∑ j ∈ Finset.range t, ascentGain h φ r i (j + 2)) =
      (t : ℝ) * Real.log ((3 : ℝ) / 2) + φ (cyclicWindow h r i 1) -
        φ (cyclicWindow h r i (t + 1)) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [ascentGain, Nat.cast_add, Nat.cast_one]
    rw [show t + 2 - 1 = t + 1 by omega]
    simp only [Nat.add_assoc]
    ring

theorem log_three_identity : Real.log 3 - 2 * Real.log 2 =
    Real.log ((3 : ℝ) / 2) - Real.log 2 := by
  rw [Real.log_div (by norm_num : (3 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
  ring

theorem block_gain_telescope (h : Depth) (φ : Correction h) (r : History h)
    (i : ℕ) :
    blockGain h φ r i 2 =
      (cyclicLength h r i : ℝ) * Real.log ((3 : ℝ) / 2) - Real.log 2 +
      φ (cyclicWindow h r (i + 1) (cyclicLength h r (i + 1))) -
      φ (cyclicWindow h r i (cyclicLength h r i)) := by
  have hr := cyclicLength_pos h r i
  have he : cyclicLength h r i - 1 + 1 = cyclicLength h r i := by omega
  have hc : ((cyclicLength h r i - 1 : ℕ) : ℝ) = (cyclicLength h r i : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ cyclicLength h r i), Nat.cast_one]
  rw [blockGain, sum_ascent_gains, he, hc]
  simp only [exitGain, Nat.cast_ofNat]
  have hl := log_three_identity
  linarith

theorem cyclicLength_period (h : Depth) (r : History h) (i : ℕ) :
    cyclicLength h r (h.val + 1 + i) = cyclicLength h r i := by
  unfold cyclicLength
  congr 2
  apply Fin.ext
  simp

theorem complete_window_period (h : Depth) (r : History h) :
    cyclicWindow h r (h.val + 1) (cyclicLength h r (h.val + 1)) =
      cyclicWindow h r 0 (cyclicLength h r 0) := by
  funext j
  have hp := cyclicLength_period h r 0
  simp only [Nat.add_zero] at hp
  simp only [cyclicWindow, Nat.zero_add]
  split_ifs
  · exact hp
  · exact cyclicLength_period h r j.val

theorem cyclic_telescoping : CyclicTelescoping := by
  intro h φ r
  let f : ℕ → ℝ := fun i => φ (cyclicWindow h r i (cyclicLength h r i))
  have hf : f (h.val + 1) = f 0 := congrArg φ (complete_window_period h r)
  have hs : (∑ i : Fin (h.val + 1), (f (i.val + 1) - f i.val)) = 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => f (i + 1) - f i)]
    simpa [hf] using (Finset.sum_range_sub f (h.val + 1))
  calc
    (∑ i : Fin (h.val + 1), blockGain h φ r i.val 2) =
        (∑ i : Fin (h.val + 1),
          (((cyclicLength h r i.val : ℝ) * Real.log ((3 : ℝ) / 2) - Real.log 2) +
            (f (i.val + 1) - f i.val))) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [block_gain_telescope]
      dsimp [f]
      ring
    _ = cycleGain h r := by rw [Finset.sum_add_distrib, hs, add_zero]; rfl

theorem failed_le_one (g : ℝ) : failed g ≤ 1 := by
  unfold failed
  split_ifs <;> omega

theorem gain_nonpos_of_failed_zero (g : ℝ) (hz : failed g = 0) : g ≤ 0 := by
  by_contra hn
  have hp : 0 ≤ g := le_of_lt (lt_of_not_ge hn)
  simp [failed, hp] at hz

theorem blockFailures_le_length (h : Depth) (φ : Correction h) (r : History h)
    (i k : ℕ) : blockFailures h φ r i k ≤ cyclicLength h r i := by
  have hs : (∑ j ∈ Finset.range (cyclicLength h r i - 1),
      failed (ascentGain h φ r i (j + 2))) ≤ cyclicLength h r i - 1 := by
    calc
      _ ≤ ∑ _j ∈ Finset.range (cyclicLength h r i - 1), 1 :=
        Finset.sum_le_sum (fun j _ => failed_le_one _)
      _ = _ := by simp
  have he := failed_le_one (exitGain h φ r i k)
  have hr := cyclicLength_pos h r i
  unfold blockFailures
  omega

theorem block_gain_nonpos_of_no_failures (h : Depth) (φ : Correction h)
    (r : History h) (i k : ℕ) (hz : blockFailures h φ r i k = 0) :
    blockGain h φ r i k ≤ 0 := by
  have hex : failed (exitGain h φ r i k) = 0 := by
    unfold blockFailures at hz
    omega
  have has : ∀ j ∈ Finset.range (cyclicLength h r i - 1),
      failed (ascentGain h φ r i (j + 2)) = 0 := by
    intro j hj
    have hb := Finset.single_le_sum (fun t _ => Nat.zero_le
      (failed (ascentGain h φ r i (t + 2)))) hj
    unfold blockFailures at hz
    omega
  unfold blockGain
  exact add_nonpos (Finset.sum_nonpos (fun j hj =>
    gain_nonpos_of_failed_zero _ (has j hj))) (gain_nonpos_of_failed_zero _ hex)

theorem cyclic_forcing : CyclicForcing := by
  intro h φ r
  refine ⟨fun i => blockFailures_le_length h φ r i.val 2, ?_⟩
  intro hpos
  by_contra hn
  have hz : cycleFailures h φ r = 0 := by omega
  have hb : ∀ i : Fin (h.val + 1), blockFailures h φ r i.val 2 = 0 := by
    intro i
    have hh := Finset.single_le_sum (fun j _ => Nat.zero_le
      (blockFailures h φ r j.val 2)) (Finset.mem_univ i)
    unfold cycleFailures at hz
    omega
  have hs : (∑ i : Fin (h.val + 1), blockGain h φ r i.val 2) ≤ 0 :=
    Finset.sum_nonpos (fun i _ => block_gain_nonpos_of_no_failures h φ r i.val 2 (hb i))
  rw [cyclic_telescoping h φ r] at hs
  exact (not_lt_of_ge hs) hpos

end ExternalO3RateCycles
