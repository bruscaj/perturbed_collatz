import WordPartitions
import BridgeTransport
import BridgeRewards

/-! Finite strict-rung transport using the proved last-letter bijection only. -/
namespace ExternalBridgePressureWordRung
open ExternalFiniteBridgeDraft ExternalBridgePressureDraft ExternalBridgePressureWordDraft
open ExternalFiniteBridgeArithmetic ExternalFiniteBridgeTransport ExternalFiniteBridgeRewards
open ExternalBridgePressureWordReward
open scoped BigOperators
noncomputable section

theorem floor_aux_zero (n : ℕ) (w : Word n) :
    FloorWord slope n w ↔ AuxWord 0 n w := by
  have hc (t : ℕ) : auxCap 0 t = floorAt slope t := by simp [auxCap,floorAt]
  simp only [AuxWord,hc]
  constructor
  · rintro ⟨hn,hpos,hend,hcap⟩
    exact ⟨hn,hpos,hend,fun i => hcap i.castSucc⟩
  · rintro ⟨hn,hpos,hend,hcap⟩
    refine ⟨hn,hpos,hend,fun t => ?_⟩
    induction t using Fin.lastCases with
    | last => simpa only [Fin.val_last,hend] using le_refl (floorAt slope n)
    | cast i => exact hcap i

noncomputable def floorAuxZeroEquiv (n : ℕ) :
    {w : Word n // FloorWord slope n w} ≃ AuxWords 0 n where
  toFun w := ⟨w.val,(floor_aux_zero n w.val).mp w.property⟩
  invFun w := ⟨w.val,(floor_aux_zero n w.val).mpr w.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem rung_word_transport : RungWordTransport := by
  intro r lam hr
  obtain ⟨e,he,_⟩ := source_floor_bijection slope r
    (le_of_lt source_slope_facts.1) hr (source_slope_nonintegral r hr.1)
  simp only [auxPartition,Nat.ne_of_gt hr.1,ite_false,sourcePartition]
  rw [← (e.trans (floorAuxZeroEquiv r)).tsum_eq]
  apply tsum_congr
  intro w
  have hp := (floor_aux_zero r (e w).val).mp (e w).property
  change Real.exp (lam*reward r w.val) = Real.exp (lam*auxReward 0 r (e w).val)
  rw [(normalized_reward_law 0 r (e w).val (by constructor <;> norm_num) hp).1]
  simp only [Real.rpow_eq_pow,neg_zero,Real.rpow_zero,one_mul,he]
  rw [(reward_endpoint_invariant r w.val).1]

end
end ExternalBridgePressureWordRung
