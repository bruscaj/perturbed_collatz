import WordFiniteComparison

/-! Explicit distinction between auxiliary phase one and physical phase zero. -/
namespace ExternalBridgePressureWordEndpoint
open ExternalFiniteBridgeDraft ExternalBridgePressureDraft ExternalBridgePressureWordDraft
open ExternalBridgePressurePhase ExternalBridgePressureWordPartitions
open scoped BigOperators

theorem floor_slope_one : Int.floor slope = 1 := by
  apply Int.floor_eq_iff.mpr
  constructor <;> norm_num
  · exact le_of_lt slope_gt_one
  · exact slope_lt_two

theorem one_word_laws (w : Word 1) :
    (AuxWord 0 1 w ↔ w 0=1) ∧ (AuxWord 1 1 w ↔ w 0=2) := by
  have hzero (x : ℝ) : auxCap x 0 = Int.floor x := by simp [auxCap]
  have h0 : auxCap 0 1=1 := by simpa [auxCap] using floor_slope_one
  have h1 : auxCap 1 1=2 := by
    simpa [auxCap,add_comm,Int.floor_add_one] using congrArg (fun z : ℤ => z+1) floor_slope_one
  simp only [AuxWord,PositiveWord,Fin.forall_fin_one,wordPrefix,Fin.sum_univ_one,
    Fin.val_last,Fin.val_zero,Fin.val_castSucc,lt_self_iff_false,ite_false,
    h0,h1,hzero,Int.floor_zero,Int.floor_one]
  constructor <;> constructor <;> intro h
  · exact_mod_cast h.2.2.1
  · norm_num [h]
  · exact_mod_cast h.2.2.1
  · norm_num [h]

theorem one_reward (x : ℝ) (w : Word 1) : auxReward x 1 w = Real.rpow 2 (-x) := by
  simp [auxReward,auxTerm,ExternalFiniteBridgeEncoding.wordPrefix_zero]

theorem one_partition (x c : ℝ) (k : ℕ)
    (hlaw : ∀ w : Word 1,AuxWord x 1 w ↔ w 0=k) :
    auxPartition x 1 c = Real.exp (c*Real.rpow 2 (-x)) := by
  classical
  let w0 : AuxWords x 1 := ⟨fun _ => k,(hlaw _).mpr rfl⟩
  have he (w : AuxWords x 1) : w=w0 := by
    apply Subtype.ext
    funext i
    have hi : i=0 := Fin.eq_zero i
    subst i
    exact (hlaw w.val).mp w.property
  simp only [auxPartition,one_ne_zero,ite_false]
  rw [tsum_eq_single w0]
  · rw [one_reward]
  · intro w hw
    exact (hw (he w)).elim

theorem physical_one_phase_period : rewardPartition 1 1 = rewardPartition 0 1 := by
  funext lam
  unfold rewardPartition
  apply Finset.sum_congr rfl
  intro j _
  have hl : PathLegal 1 1 j ↔ PathLegal 0 1 j := by
    simp [PathLegal,NaturalPathLegal,Fin.forall_fin_one,phaseIncrement,phaseFloor,
      floor_slope_one,add_comm,Int.floor_add_one]
  by_cases hj : PathLegal 0 1 j
  · have hj1 := hl.mpr hj
    simp only [hj,hj1,ite_true]
    congr 1
    simp [pathReward,phaseWeight,phaseTick]
  · have hj1 : ¬ PathLegal 1 1 j := fun h => hj (hl.mp h)
    simp only [hj,hj1,ite_false]

theorem auxiliary_endpoint_witness : AuxiliaryEndpointWitness := by
  refine ⟨one_word_laws,fun lam => ?_⟩
  have h0 := one_partition 0 lam 1 (fun w => (one_word_laws w).1)
  have h1 := one_partition 1 lam 2 (fun w => (one_word_laws w).2)
  norm_num [Real.rpow_eq_pow] at h0 h1
  refine ⟨h0,?_,?_,?_,?_⟩
  · simpa only [mul_one_div] using h1
  · rw [auxLogPartition,h0,Real.log_exp]
  · rw [auxLogPartition,h1,Real.log_exp]
    ring
  · rw [physical_one_phase_period,← word_path_partition_equality 0 1 lam (by constructor <;> norm_num),h0]

end ExternalBridgePressureWordEndpoint
