import WordPhaseUp

/-! Exact clamp-prefix transport and finite fiber recovery. -/
namespace ExternalBridgePressureWordClamp
open ExternalFiniteBridgeDraft ExternalBridgePressureDraft ExternalBridgePressureWordDraft
open ExternalFiniteBridgeEncoding ExternalBridgePressureWordArithmetic ExternalBridgePressureWordPhaseUp
open scoped BigOperators

theorem clamp_profile_positive (x y : ℝ) (n : ℕ) (hxy : OrderedPhases x y)
    (w : Word n) (hw : AuxWord y n w) : PositivePrefix n (clampProfile x n w) := by
  refine ⟨?_,fun i => ?_⟩
  · have hc : 0 ≤ auxCap x 0 := by
      simpa [auxCap] using Int.floor_nonneg.mpr hxy.1.1
    simp only [clampProfile,wordPrefix_zero,Fin.val_zero,min_eq_left hc]
  · have ha := (wordPrefix_positive n w hw.2.1).2 i
    have hc := aux_cap_increment x i.val
    simp only [clampProfile,Fin.val_succ,Fin.val_castSucc]
    omega

theorem clamp_prefix (x y : ℝ) (n : ℕ) (hxy : OrderedPhases x y)
    (w : Word n) (hw : AuxWord y n w) :
    wordPrefix n (clampWord x n w) = clampProfile x n w :=
  wordPrefix_prefixLetters n _ (clamp_profile_positive x y n hxy w hw)

theorem clamp_word_transport : ClampWordTransport := by
  intro x y n hxy _ w hw
  have hp := clamp_profile_positive x y n hxy w hw
  have he := clamp_prefix x y n hxy w hw
  refine ⟨hp,he,hw.1,prefixLetters_positive n _ hp,?_,?_⟩
  · rw [he]
    simp only [clampProfile,Fin.val_last,hw.2.2.1]
    exact min_eq_right (cap_mono x y hxy.2.2 n)
  · intro t
    rw [he]
    exact min_le_right _ _

theorem recover_clamp_profile (x y : ℝ) (n : ℕ) (hxy : OrderedPhases x y)
    (w : Word n) (hw : AuxWord y n w) :
    recoverClampProfile x y n (clampWord x n w) (clampBits x y n w) = wordPrefix n w := by
  funext t
  unfold recoverClampProfile
  split_ifs with ht hd hb
  · have hcap := hw.2.2.2 ⟨t.val,ht⟩
    have hg := (cap_difference_geometry x y n hxy).1 t.val
    have he : (⟨t.val,ht⟩ : Fin n).castSucc = t := Fin.ext rfl
    have hbit : auxCap x t.val < wordPrefix n w t := by
      simpa only [clampBits,decide_eq_true_eq,he] using hb
    rw [he] at hcap
    change wordPrefix n w t ≤ auxCap y t.val at hcap
    omega
  · rw [clamp_prefix x y n hxy w hw]
    have he : (⟨t.val,ht⟩ : Fin n).castSucc = t := Fin.ext rfl
    have hbit : ¬ auxCap x t.val < wordPrefix n w t := by
      simpa only [clampBits,decide_eq_true_eq,he] using hb
    exact min_eq_left (le_of_not_gt hbit)
  · rw [clamp_prefix x y n hxy w hw]
    have hcap := hw.2.2.2 ⟨t.val,ht⟩
    have he : (⟨t.val,ht⟩ : Fin n).castSucc = t := Fin.ext rfl
    rw [he] at hcap
    change wordPrefix n w t ≤ auxCap y t.val at hcap
    have hm := cap_mono x y hxy.2.2 t.val
    unfold clampProfile
    apply min_eq_left
    omega
  · have he : t = Fin.last n := Fin.ext (by have := t.isLt; simp only [Fin.val_last]; omega)
    subst t
    exact hw.2.2.1.symm

theorem recover_clamp_word (x y : ℝ) (n : ℕ) (hxy : OrderedPhases x y)
    (w : Word n) (hw : AuxWord y n w) :
    recoverClampWord x y n (clampWord x n w) (clampBits x y n w) = w := by
  unfold recoverClampWord
  rw [recover_clamp_profile x y n hxy w hw,prefixLetters_wordPrefix]

theorem clamp_code_injective (x y : ℝ) (n : ℕ) (hxy : OrderedPhases x y) :
    Function.Injective (fun w : AuxWords y n => clampCode x y n w.val) := by
  intro a b hab
  have h := congrArg (fun p => recoverClampWord x y n p.1 p.2) hab
  simp only [clampCode,recover_clamp_word x y n hxy a.val a.property,
    recover_clamp_word x y n hxy b.val b.property] at h
  exact Subtype.ext h

theorem clamp_fiber_encoding : ClampFiberEncoding := by
  intro x y n hxy _
  refine ⟨clamp_code_injective x y n hxy,fun w hw => ?_⟩
  refine ⟨recover_clamp_profile x y n hxy w hw,recover_clamp_word x y n hxy w hw,?_⟩
  intro t ht
  have hc : 0 ≤ auxCap x 0 := by simpa [auxCap] using Int.floor_nonneg.mpr hxy.1.1
  have he : t.val.castSucc = (0 : Fin (n+1)) := Fin.ext ht
  simp only [clampBits,ht,he,wordPrefix_zero,decide_eq_false_iff_not]
  omega

end ExternalBridgePressureWordClamp
