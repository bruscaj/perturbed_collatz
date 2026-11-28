import WordPartitions

/-! Ordered auxiliary phases: exact cap crossings and last-letter transport. -/
namespace ExternalBridgePressureWordPhaseUp
open ExternalFiniteBridgeDraft ExternalBridgePressureDraft ExternalBridgePressureWordDraft
open ExternalFiniteBridgeEncoding ExternalBridgePressureWordReward
open scoped BigOperators

theorem cap_mono (x y : ℝ) (hxy : x ≤ y) (t : ℕ) : auxCap x t ≤ auxCap y t :=
  Int.floor_mono (by linarith)

theorem shifted_floor_bounds (x u : ℝ) (hx : ClosedPhase x) :
    Int.floor u ≤ Int.floor (x+u) ∧ Int.floor (x+u) ≤ Int.floor u+1 := by
  constructor
  · exact Int.floor_mono (by linarith [hx.1])
  · have h := Int.floor_mono (show x+u ≤ u+1 by linarith [hx.2])
    simpa only [Int.floor_add_one] using h

theorem shifted_floor_high (x u : ℝ) :
    Int.floor u+1 ≤ Int.floor (x+u) ↔ 1-x ≤ Int.fract u := by
  rw [Int.le_floor]
  simp only [Int.cast_add,Int.cast_one,Int.fract]
  constructor <;> intro h <;> linarith

theorem cap_difference_geometry : CapDifferenceGeometry := by
  intro x y n hxy
  have hm := cap_mono x y hxy.2.2
  have hd (t : ℕ) : auxCap y t - auxCap x t = 0 ∨ auxCap y t - auxCap x t = 1 := by
    have hx := shifted_floor_bounds x ((t : ℝ)*slope) hxy.1
    have hy := shifted_floor_bounds y ((t : ℝ)*slope) hxy.2.1
    have := hm t
    unfold auxCap at *
    omega
  refine ⟨hd, ?_, ?_⟩
  · calc
      Dcount x y n ≤ Nat.card (Fin n) :=
        Nat.card_le_card_of_injective (fun t : CapDifference x y n => t.val) Subtype.val_injective
      _ = n := by simp
  · intro t
    have hx := shifted_floor_bounds x ((t : ℝ)*slope) hxy.1
    have hy := shifted_floor_bounds y ((t : ℝ)*slope) hxy.2.1
    have hcX := shifted_floor_high x ((t : ℝ)*slope)
    have hcY := shifted_floor_high y ((t : ℝ)*slope)
    unfold auxCap
    constructor
    · intro h
      constructor
      · exact hcY.mp (by omega)
      · by_contra hh
        have hh' := hcX.mpr (le_of_not_gt hh)
        omega
    · rintro ⟨hy',hx'⟩
      have hy'' := hcY.mpr hy'
      have hx'' : ¬ Int.floor ((t : ℝ)*slope)+1 ≤ Int.floor (x+(t : ℝ)*slope) := by
        intro h
        exact (not_le.mpr hx') (hcX.mp h)
      omega

theorem phase_up_interior (x y : ℝ) (n : ℕ) (w : Word n) (t : Fin n) :
    wordPrefix n (phaseUp x y n w) t.castSucc = wordPrefix n w t.castSucc := by
  unfold wordPrefix
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val < t.val
  · have hn : i.val+1 ≠ n := by have := t.isLt; omega
    simp only [Fin.val_castSucc,hi,ite_true,phaseUp,hn,ite_false]
  · simp only [Fin.val_castSucc,hi,ite_false]

theorem phase_up_endpoint (x y : ℝ) (n : ℕ) (hn : 1 ≤ n) (w : Word n) :
    wordPrefix n (phaseUp x y n w) (Fin.last n) = wordPrefix n w (Fin.last n) +
      ((auxCap y n-auxCap x n).toNat : ℤ) := by
  let i : Fin n := ⟨n-1,by omega⟩
  have hi : i.val+1=n := by dsimp [i]; omega
  have he : i.succ = Fin.last n := Fin.ext hi
  rw [← he,wordPrefix_step,wordPrefix_step,phase_up_interior]
  simp only [phaseUp,hi,ite_true,Nat.cast_add]
  ring

theorem phase_up_transport : PhaseUpTransport := by
  intro x y n hxy hn
  have hc := cap_mono x y hxy.2.2 n
  have he : ((auxCap y n-auxCap x n).toNat : ℤ) = auxCap y n-auxCap x n :=
    Int.toNat_of_nonneg (by omega)
  refine ⟨he,fun w hw => ⟨?_,phase_up_interior x y n w⟩⟩
  refine ⟨hw.1,?_,?_,?_⟩
  · intro i
    have := hw.2.1 i
    unfold phaseUp
    split <;> omega
  · rw [phase_up_endpoint x y n hn,he,hw.2.2.1]
    omega
  · intro t
    rw [phase_up_interior]
    exact (hw.2.2.2 t).trans (cap_mono x y hxy.2.2 t.val)

theorem phase_up_injective (x y : ℝ) (n : ℕ) : Function.Injective (phaseUp x y n) := by
  intro a b hab
  funext i
  have h := congrFun hab i
  simp only [phaseUp] at h
  split at h <;> omega

theorem phase_up_reward (x y : ℝ) (n : ℕ) (w : Word n) :
    reward n (phaseUp x y n w) = reward n w := by
  unfold reward
  apply Finset.sum_congr rfl
  intro t _
  rw [phase_up_interior]

theorem phase_up_injection_reward : PhaseUpInjectionReward := by
  intro x y n hxy hn
  refine ⟨phase_up_injective x y n,fun w hw => ⟨phase_up_reward x y n w,?_⟩⟩
  have hy := (phase_up_transport x y n hxy hn).2 w hw |>.1
  rw [(normalized_reward_law y n _ hxy.2.1 hy).1,
    (normalized_reward_law x n w hxy.1 hw).1,phase_up_reward]
  have he : Real.rpow 2 (-y) = Real.rpow 2 (-(y-x))*Real.rpow 2 (-x) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  rw [he]
  ring

end ExternalBridgePressureWordPhaseUp
