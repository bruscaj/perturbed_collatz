import WordPhysical

/-! Finite partition reindexing through the exact auxiliary-word enumerations. -/
namespace ExternalBridgePressureWordPartitions
open ExternalFiniteBridgeDraft ExternalBridgePressureDraft ExternalBridgePressureWordDraft
open ExternalBridgePressureWordArithmetic ExternalBridgePressureWordPopulation
open ExternalBridgePressureWordPhysical
open scoped BigOperators
noncomputable section
local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem tsum_predicate_finite {α : Type*} [Fintype α] (P : α → Prop) (f : α → ℝ) :
    (∑' a : {a // P a}, f a.val) = ∑ a, if P a then f a else 0 := by
  classical
  rw [tsum_fintype]
  calc
    (∑ a : {a // P a}, f a.val) = ∑ a ∈ Finset.univ.filter P, f a :=
      (Finset.sum_subtype _ (by simp) f).symm
    _ = _ := by rw [Finset.sum_filter]

noncomputable def boundedAuxEquiv (x : ℝ) (n : ℕ) (hx : ClosedPhase x) :
    AuxWords x n ≃ {a : BoundedWord n // AuxWord x n (decodeBoundedWord n a)} where
  toFun w := ⟨encodeAuxWord x n hx w, w.property⟩
  invFun a := ⟨decodeBoundedWord n a.val, a.property⟩
  left_inv _ := rfl
  right_inv a := by
    apply Subtype.ext
    apply decode_bounded_word_injective n
    rfl

theorem aux_partition_finite_sum : AuxPartitionFiniteSum := by
  intro x n lam hx
  have := aux_words_finite x n hx
  let := Fintype.ofFinite (AuxWords x n)
  refine ⟨(hasSum_fintype _).summable, ?_, ?_⟩
  · by_cases hn : n=0
    · simp [auxPartition, auxFinitePartition, hn]
    · simp only [auxPartition,auxFinitePartition,hn,ite_false]
      calc
        (∑' w : AuxWords x n, Real.exp (lam*auxReward x n w.val)) =
            ∑' a : {a : BoundedWord n // AuxWord x n (decodeBoundedWord n a)},
              Real.exp (lam*auxReward x n (decodeBoundedWord n a.val)) :=
          (boundedAuxEquiv x n hx).tsum_eq (fun a => Real.exp (lam*auxReward x n (decodeBoundedWord n a.val)))
        _ = _ := by
          exact tsum_predicate_finite (α := BoundedWord n)
            (fun a => AuxWord x n (decodeBoundedWord n a))
            (fun a => Real.exp (lam*auxReward x n (decodeBoundedWord n a)))
  · intro hn
    simp [auxPartition, Nat.ne_of_gt hn]

theorem reward_partition_zero (x lam : ℝ) : rewardPartition x 0 lam = 1 := by
  simp [rewardPartition, PathLegal, NaturalPathLegal, pathReward]

theorem word_path_partition_equality : WordPathPartitionEquality := by
  intro x n lam hx
  by_cases hn : n=0
  · subst n
    rw [(zero_volume_convention x lam).2.1, reward_partition_zero]
  · have hpos : 1 ≤ n := by omega
    simp only [auxPartition,hn,ite_false]
    calc
      (∑' w : AuxWords x n, Real.exp (lam*auxReward x n w.val)) =
          ∑' j : {j : Path n // PathLegal x n j}, Real.exp (lam*pathReward x n j.val) := by
        rw [← (wordPathEquiv x n hx hpos).tsum_eq]
        apply tsum_congr
        intro w
        rw [word_path_reward x n hx w.val w.property]
        rfl
      _ = rewardPartition x n lam := by
        exact tsum_predicate_finite (α := Path n)
          (PathLegal x n) (fun j => Real.exp (lam*pathReward x n j))

theorem closing_phase_bounds (r : ℕ) : ActualPhase (defect slope r) := by
  constructor
  · exact sub_nonneg.mpr (Int.le_ceil _)
  · have h := Int.ceil_lt_add_one ((r : ℝ)*slope)
    unfold defect
    linarith

theorem closing_cap_endpoint (r : ℕ) :
    auxCap (defect slope r) r = Int.ceil ((r : ℝ)*slope) := by
  unfold auxCap defect
  rw [sub_add_cancel, Int.floor_intCast]

theorem source_aux_closing (r : ℕ) (w : Word r) :
    SourceWord slope r w ↔ AuxWord (defect slope r) r w := by
  simp only [SourceWord,AuxWord,closing_cap_endpoint]
  have hc (t : ℕ) : auxCap (defect slope r) t = literalCap slope r t := by
    unfold auxCap literalCap
    rw [add_comm]
  simp only [hc]

noncomputable def sourceClosingEquiv (r : ℕ) :
    {w : Word r // SourceWord slope r w} ≃ AuxWords (defect slope r) r where
  toFun w := ⟨w.val, (source_aux_closing r w.val).mp w.property⟩
  invFun w := ⟨w.val, (source_aux_closing r w.val).mpr w.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem closing_phase_transport : ClosingPhaseTransport := by
  intro r lam hr
  have hp := closing_phase_bounds r
  have hm : Real.rpow 2 (defect slope r) * Real.rpow 2 (-(defect slope r)) = 1 := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    simp
  simp only [auxPartition, Nat.ne_of_gt hr, ite_false, sourcePartition]
  rw [← (sourceClosingEquiv r).tsum_eq]
  apply tsum_congr
  intro w
  change Real.exp (lam*reward r w.val) =
    Real.exp ((lam*Real.rpow 2 (defect slope r))*auxReward (defect slope r) r w.val)
  rw [(ExternalBridgePressureWordReward.normalized_reward_law _ _ _
    ⟨hp.1,le_of_lt hp.2⟩ ((source_aux_closing r w.val).mp w.property)).1]
  congr 1
  calc
    lam*reward r w.val = lam*(1*reward r w.val) := by ring
    _ = _ := by rw [← hm]; ring

end
end ExternalBridgePressureWordPartitions
