import GeneralArithmetic

/-!
Source binding for the exact finite refinements. The labels read actual
Syracuse block lengths and actual terminal stride valuations. Offset decoding
is justified by proved positivity and first-exit arithmetic, not a symbolic
sampling assumption. No source/specification file is changed.
-/
namespace ExternalO3GeneralRefinementLabels

open ExternalO3GeneralDraft ExternalO3GeneralArithmetic
open ExternalO3Spec (IsOddSeed stride strideValuation blockLength)

theorem future_length_positive (x : ℕ) (hx : IsOddSeed x) (i : ℕ) :
    0 < blockLength (futureBlockSeed x i) :=
  ExternalO3Arithmetic.block_length_positive _ (futureBlockSeed_odd x hx i)

theorem future_exit_ge_two (x : ℕ) (hx : IsOddSeed x) (i : ℕ) :
    2 ≤ strideValuation
      ((Nat.iterate stride (blockLength (futureBlockSeed x i) - 1)) (futureBlockSeed x i)) :=
  (ExternalO3Arithmetic.block_length_law _ (futureBlockSeed_odd x hx i)).2.2

theorem decoded_length_actual (m n : ℕ) (i : Fin (m + 1)) :
    decodedLengths m (refinedLabel m n) i = blockLength (futureBlockSeed (2 * n + 1) i.val) := by
  have hx : IsOddSeed (2 * n + 1) := ⟨by omega, by omega⟩
  have hp := future_length_positive (2 * n + 1) hx i.val
  dsimp [decodedLengths, refinedLabel]
  omega

theorem decoded_lengths_actual (m n : ℕ) :
    decodedLengths m (refinedLabel m n) =
      fun i => blockLength (futureBlockSeed (2 * n + 1) i.val) := by
  funext i
  exact decoded_length_actual m n i

theorem decoded_exit_actual (m n : ℕ) (i : Fin m) :
    decodedExits m (refinedLabel m n) i =
      strideValuation
        ((Nat.iterate stride (blockLength (futureBlockSeed (2 * n + 1) i.val) - 1))
          (futureBlockSeed (2 * n + 1) i.val)) := by
  have hx : IsOddSeed (2 * n + 1) := ⟨by omega, by omega⟩
  have hp := future_exit_ge_two (2 * n + 1) hx i.val
  dsimp [decodedExits, refinedLabel]
  omega

/-- Every decoded offset datum is in the source class of positive blocks/exits. -/
theorem decoded_data_valid (m : ℕ) (data : RefinedIndex m) :
    ValidBlockData m (decodedLengths m data) (decodedExits m data) := by
  constructor
  · intro i
    simp [decodedLengths]
  · intro i
    simp [decodedExits]

theorem refined_label_cell : RefinedLabelCell := by
  intro m data n
  constructor
  · intro he
    rw [← he]
    refine ⟨⟨by omega, by omega⟩, ?_, ?_⟩
    · intro i
      exact (decoded_length_actual m n i).symm
    · intro i
      rw [decoded_length_actual, decoded_exit_actual]
      simp only [Fin.val_castSucc]
  · rintro ⟨_, hlength, hexit⟩
    apply Prod.ext
    · funext i
      change blockLength (futureBlockSeed (2 * n + 1) i.val) - 1 = data.1 i
      rw [hlength i]
      simp [decodedLengths]
    · funext i
      change strideValuation
        ((Nat.iterate stride (blockLength (futureBlockSeed (2 * n + 1) i.val) - 1))
          (futureBlockSeed (2 * n + 1) i.val)) - 2 = data.2 i
      have hl := hlength i.castSucc
      change blockLength (futureBlockSeed (2 * n + 1) i.val) =
        decodedLengths m data i.castSucc at hl
      rw [hl, hexit i]
      simp [decodedExits]

theorem futureBlockSeed_zero (x : ℕ) : futureBlockSeed x 0 = x := rfl

/-- The first recorded exit offset is the immediate stride's valuation exactly
when the current remaining block has length one. -/
theorem refined_first_exit_short (h : Depth) (n : ℕ)
    (hr : blockLength (2 * n + 1) = 1) :
    (refinedLabel h.val n).2 (zeroIndex h) = strideValuation (2 * n + 1) - 2 := by
  simp [refinedLabel, zeroIndex, futureBlockSeed, hr]

theorem refinement_projection_law : RefinementProjectionLaw := by
  intro h n
  let x := 2 * n + 1
  have hx : IsOddSeed x := ⟨by dsimp [x]; omega, by dsimp [x]; omega⟩
  by_cases hr : 2 ≤ blockLength x
  · change 2 ≤ blockLength (2 * n + 1) at hr
    simp only [refinementProjection, decoded_lengths_actual, futureBlockSeed_zero,
      label, ite_eq_left hr]
    rfl
  · change ¬2 ≤ blockLength (2 * n + 1) at hr
    have hb : blockLength x = 1 := by
      have hp := ExternalO3Arithmetic.block_length_positive x hx
      dsimp only [x] at hp ⊢
      omega
    have hfirst := refined_first_exit_short h n hb
    have htail : (fun i : Fin h.val => blockLength (futureBlockSeed x i.succ.val)) =
        window h (stride x) := by
      funext i
      change blockLength (futureBlockSeed x (i.val + 1)) =
        blockLength (futureBlockSeed (stride x) i.val)
      rw [futureBlockSeed_succ_of_short x hb i.val]
    dsimp only [x] at htail
    simp only [refinementProjection, decoded_lengths_actual, futureBlockSeed_zero,
      label, ite_eq_right hr, hfirst, htail]

end ExternalO3GeneralRefinementLabels
