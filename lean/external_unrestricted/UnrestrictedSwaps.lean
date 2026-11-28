import UnrestrictedExpectedTypes
import BridgeEncoding
import Mathlib.Data.Finset.Powerset

/-! Generic adjacent 21→12 swaps, with no global positivity hypothesis on words.
All target predicates and operations are the unchanged frozen specification. -/
namespace ExternalM4UnrestrictedSwaps
open ExternalFiniteBridgeDraft ExternalM4UnrestrictedDraft
open ExternalFiniteBridgeEncoding
open scoped BigOperators

theorem admissible_sites_subset (r : ℕ) (w : Word r) (S T : Finset (Fin r))
    (hS : AdmissibleSites r w S) (hT : T ⊆ S) : AdmissibleSites r w T :=
  ⟨fun i hi => hS.1 i (hT hi), fun i hi j hj hij => hS.2 i (hT hi) j (hT hj) hij⟩

theorem no_predecessor_of_mem (r : ℕ) (S : Finset (Fin r))
    (hS : DisjointSites r S) (i : Fin r) (hi : i ∈ S) :
    ¬ ∃ j ∈ S, j.val + 1 = i.val := by
  rintro ⟨j, hj, hji⟩
  have hne : j ≠ i := by intro h; subst j; omega
  have hd := hS j hj i hi hne
  omega

theorem marker_next (r : ℕ) (S : Finset (Fin r)) (i : Fin r) :
    (∃ j ∈ S, j.val + 1 = i.val + 1) ↔ i ∈ S := by
  constructor
  · rintro ⟨j,hj,h⟩
    have : j = i := Fin.ext (by omega)
    simpa [this] using hj
  · intro hi; exact ⟨i,hi,rfl⟩

theorem swap_letter_delta (r : ℕ) (w : Word r) (S : Finset (Fin r))
    (hS : AdmissibleSites r w S) (i : Fin r) :
    (applySwaps r w S i : ℤ) = (w i : ℤ) +
      (if ∃ j ∈ S, j.val + 1 = i.val then (1 : ℤ) else 0) -
      (if ∃ j ∈ S, j.val + 1 = i.val + 1 then (1 : ℤ) else 0) := by
  classical
  simp only [marker_next]
  by_cases hi : i ∈ S
  · have hn := no_predecessor_of_mem r S hS.2 i hi
    obtain ⟨_, hw, _⟩ := hS.1 i hi
    simp [applySwaps, hi, hn, hw]
  · by_cases hp : ∃ j ∈ S, j.val + 1 = i.val
    · obtain ⟨j,hj,hji⟩ := hp
      obtain ⟨hb,_,hw⟩ := hS.1 j hj
      have he : (⟨j.val + 1,hb⟩ : Fin r) = i := Fin.ext hji
      rw [he] at hw
      have hp' : ∃ j ∈ S, j.val + 1 = i.val := ⟨j,hj,hji⟩
      simp [applySwaps, hi, hp', hw]
    · simp [applySwaps, hi, hp]

theorem swap_prefix_law : SwapPrefixLaw := by
  classical
  intro r w S hS t
  induction t using Fin.induction with
  | zero => simp [wordPrefix_zero]
  | succ i ih =>
    rw [wordPrefix_step, wordPrefix_step, ih, swap_letter_delta r w S hS i]
    simp only [Fin.val_castSucc, Fin.val_succ]
    omega

theorem swapped_positive (r : ℕ) (w : Word r) (S : Finset (Fin r))
    (hw : PositiveWord r w) : PositiveWord r (applySwaps r w S) := by
  classical
  intro i
  unfold applySwaps
  split_ifs <;> first | omega | exact hw i

theorem last_not_intermediate (r : ℕ) (w : Word r) (S : Finset (Fin r))
    (hS : AdmissibleSites r w S) : ¬ ∃ i ∈ S, i.val + 1 = r := by
  rintro ⟨i,hi,he⟩
  obtain ⟨hb,_,_⟩ := hS.1 i hi
  omega

theorem swap_preserves_source : SwapPreservesSource := by
  classical
  intro r w S hw hS
  have hp := swapped_positive r w S hw.2.1
  have he : wordPrefix r (applySwaps r w S) (Fin.last r) =
      wordPrefix r w (Fin.last r) := by
    rw [swap_prefix_law r w S hS]
    simp [last_not_intermediate r w S hS]
  have hc : ∀ t : Fin r, wordPrefix r (applySwaps r w S) t.castSucc ≤
      literalCap slope r t.val := by
    intro t
    rw [swap_prefix_law r w S hS]
    have ht := hw.2.2.2 t
    split_ifs <;> omega
  exact ⟨hp,he,hc,hw.1,hp,he.trans hw.2.2.1,hc⟩

theorem swapped_at_site (r : ℕ) (w : Word r) (S T : Finset (Fin r))
    (hS : AdmissibleSites r w S) (hT : T ⊆ S) (i : Fin r) (hi : i ∈ S) :
    applySwaps r w T i = if i ∈ T then 1 else 2 := by
  classical
  have hn : ¬ ∃ j ∈ T, j.val + 1 = i.val := by
    rintro ⟨j,hj,hji⟩
    exact no_predecessor_of_mem r S hS.2 i hi ⟨j,hT hj,hji⟩
  obtain ⟨_,hw,_⟩ := hS.1 i hi
  simp [applySwaps,hn,hw]

theorem swap_family_injective : SwapFamilyInjective := by
  classical
  intro r w S hS T U he
  apply Subtype.ext
  ext i
  by_cases hi : i ∈ S
  · have hh := congrFun he i
    change applySwaps r w T.val i = applySwaps r w U.val i at hh
    rw [swapped_at_site r w S T.val hS T.property i hi,
      swapped_at_site r w S U.val hS U.property i hi] at hh
    split_ifs at hh <;> simp_all
  · have hT : i ∉ T.val := fun h => hi (T.property h)
    have hU : i ∉ U.val := fun h => hi (U.property h)
    simp [hT,hU]

theorem swap_cube_card : SwapCubeCard := by
  classical
  intro r S
  let e : SwapCube r S ≃ {T // T ∈ S.powerset} :=
    { toFun := fun T => ⟨T.val, Finset.mem_powerset.mpr T.property⟩
      invFun := fun T => ⟨T.val, Finset.mem_powerset.mp T.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_powerset]

theorem reward_difference_at (r : ℕ) (w : Word r) (S : Finset (Fin r))
    (hS : AdmissibleSites r w S) (t : Fin r) :
    (2 : ℝ) ^ wordPrefix r w t.castSucc / (3 : ℝ) ^ t.val -
      (2 : ℝ) ^ wordPrefix r (applySwaps r w S) t.castSucc / (3 : ℝ) ^ t.val =
    if ∃ i ∈ S, i.val + 1 = t.val then
      (2 : ℝ) ^ wordPrefix r w t.castSucc / (3 : ℝ) ^ t.val / 2 else 0 := by
  classical
  rw [swap_prefix_law r w S hS]
  simp only [Fin.val_castSucc]
  split_ifs with hm
  · rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
    ring
  · simp

theorem sum_intermediate_loss (r : ℕ) (w : Word r) (S : Finset (Fin r))
    (hS : AdmissibleSites r w S) :
    (∑ t : Fin r, if ∃ i ∈ S, i.val + 1 = t.val then
      (2 : ℝ) ^ wordPrefix r w t.castSucc / (3 : ℝ) ^ t.val / 2 else 0) =
      swapLoss r w S := by
  classical
  rw [← Finset.sum_filter]
  symm
  unfold swapLoss
  apply Finset.sum_bij (fun i hi => (⟨i.val + 1, (hS.1 i hi).choose⟩ : Fin r))
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨i,hi,rfl⟩
  · intro i hi j hj he
    apply Fin.ext
    have hh := congrArg Fin.val he
    dsimp at hh
    omega
  · intro t ht
    obtain ⟨i,hi,he⟩ := (Finset.mem_filter.mp ht).2
    refine ⟨i,hi,?_⟩
    exact Fin.ext he
  · intro i hi
    have he : (⟨i.val + 1, (hS.1 i hi).choose⟩ : Fin r).castSucc = i.succ :=
      Fin.ext rfl
    simp only [he]

theorem swap_reward_identity : SwapRewardIdentity := by
  classical
  intro r w S hS
  unfold reward
  rw [← Finset.sum_sub_distrib]
  simp_rw [reward_difference_at r w S hS]
  exact sum_intermediate_loss r w S hS

end ExternalM4UnrestrictedSwaps
