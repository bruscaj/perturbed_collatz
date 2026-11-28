import BridgeEncoding
import BridgeArithmetic
import BridgeRewards
import BridgeTransport
import Mathlib.SetTheory.Cardinal.Finite

namespace ExternalFiniteBridgeFinite
open ExternalFiniteBridgeDraft ExternalFiniteBridgeEncoding
open ExternalFiniteBridgeArithmetic ExternalFiniteBridgeRewards
open scoped BigOperators

theorem wordPrefix_last (r : ℕ) (w : Word r) :
    wordPrefix r w (Fin.last r) = ∑ i : Fin r, (w i : ℤ) := by
  unfold wordPrefix
  apply Finset.sum_congr rfl
  intro i _
  simp only [Fin.val_last, i.isLt, ite_true]

theorem finite_endpoint_words (r : ℕ) (s : ℤ) :
    Finite {w : Word r // wordPrefix r w (Fin.last r) = s} := by
  let f : {w : Word r // wordPrefix r w (Fin.last r) = s} → (Fin r → Fin (s.toNat + 1)) :=
    fun w i => ⟨w.val i, by
      have hle : (w.val i : ℤ) ≤ s := by
        have hb := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin r))) =>
          Int.natCast_nonneg (w.val j)) (Finset.mem_univ i)
        rw [← wordPrefix_last, w.property] at hb
        exact hb
      have := hle.trans (Int.self_le_toNat s)
      omega⟩
  apply Finite.of_injective f
  intro a b hab
  apply Subtype.ext
  funext i
  exact congrArg Fin.val (congrFun hab i)

theorem depth_prefix_positive (θ : ℝ) (r : ℕ) (J : Depth r) (hJ : DepthBridge θ r J) :
    PositivePrefix r (fun t => floorAt θ t.val - J t) := by
  refine ⟨?_, ?_⟩
  · simp [hJ.1, floorAt]
  · intro i
    have hs := hJ.2.2.2 i
    simp only [Fin.val_succ, Fin.val_castSucc]
    omega

theorem depth_letters_prefix (θ : ℝ) (r : ℕ) (J : Depth r) (hJ : DepthBridge θ r J) :
    wordPrefix r (depthLetters θ r J) = fun t => floorAt θ t.val - J t := by
  exact wordPrefix_prefixLetters r _ (depth_prefix_positive θ r J hJ)

theorem depth_letters_endpoint (θ : ℝ) (r : ℕ) (J : Depth r) (hJ : DepthBridge θ r J) :
    wordPrefix r (depthLetters θ r J) (Fin.last r) = floorAt θ r := by
  rw [depth_letters_prefix θ r J hJ]
  simp only [Fin.val_last, hJ.2.1, sub_zero]

theorem wordDepth_depthLetters (θ : ℝ) (r : ℕ) (J : Depth r) (hJ : DepthBridge θ r J) :
    wordDepth θ r (depthLetters θ r J) = J := by
  funext t
  simp only [wordDepth, depth_letters_prefix θ r J hJ]
  omega

theorem depthLetters_wordDepth (θ : ℝ) (r : ℕ) (w : Word r) :
    depthLetters θ r (wordDepth θ r w) = w := by
  have he : (fun t : Fin (r+1) => floorAt θ t.val - wordDepth θ r w t) = wordPrefix r w := by
    funext t
    simp [wordDepth]
  unfold depthLetters
  rw [he, prefixLetters_wordPrefix]

theorem floor_word_depth (θ : ℝ) (r : ℕ) (w : Word r) (hw : FloorWord θ r w) :
    DepthBridge θ r (wordDepth θ r w) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [wordDepth, floorAt, wordPrefix_zero]
  · simp only [wordDepth, Fin.val_last, hw.2.2.1, sub_self]
  · intro t
    exact sub_nonneg.mpr (hw.2.2.2 t)
  · intro i
    have hs := (wordPrefix_positive r w hw.2.1).2 i
    simp only [wordDepth, Fin.val_succ, Fin.val_castSucc]
    omega

theorem depth_floor_word (θ : ℝ) (r : ℕ) (hr : 0 < r) (J : Depth r)
    (hJ : DepthBridge θ r J) : FloorWord θ r (depthLetters θ r J) := by
  refine ⟨hr, prefixLetters_positive r _ (depth_prefix_positive θ r J hJ),
    depth_letters_endpoint θ r J hJ, ?_⟩
  intro t
  rw [depth_letters_prefix θ r J hJ]
  change floorAt θ t.val - J t ≤ floorAt θ t.val
  have := hJ.2.2.1 t
  omega

noncomputable def floor_depth_equiv (θ : ℝ) (r : ℕ) (hr : 0 < r) :
    {w : Word r // FloorWord θ r w} ≃ {J : Depth r // DepthBridge θ r J} where
  toFun w := ⟨wordDepth θ r w.val, floor_word_depth θ r w.val w.property⟩
  invFun J := ⟨depthLetters θ r J.val, depth_floor_word θ r hr J.val J.property⟩
  left_inv w := Subtype.ext (depthLetters_wordDepth θ r w.val)
  right_inv J := Subtype.ext (wordDepth_depthLetters θ r J.val J.property)

theorem finite_populations : FinitePopulations := by
  intro θ r
  constructor
  · have := finite_endpoint_words r (Int.ceil ((r : ℝ) * θ))
    exact Finite.of_injective
      (fun w : {w : Word r // SourceWord θ r w} =>
        (⟨w.val, w.property.2.2.1⟩ : {w : Word r // wordPrefix r w (Fin.last r) = Int.ceil ((r : ℝ) * θ)}))
      (by intro a b h; exact Subtype.ext (congrArg
        (fun z : {w : Word r // wordPrefix r w (Fin.last r) = Int.ceil ((r : ℝ) * θ)} => z.val) h))
  constructor
  · have := finite_endpoint_words r (floorAt θ r)
    exact Finite.of_injective
      (fun w : {w : Word r // FloorWord θ r w} =>
        (⟨w.val, w.property.2.2.1⟩ : {w : Word r // wordPrefix r w (Fin.last r) = floorAt θ r}))
      (by intro a b h; exact Subtype.ext (congrArg
        (fun z : {w : Word r // wordPrefix r w (Fin.last r) = floorAt θ r} => z.val) h))
  · have := finite_endpoint_words r (floorAt θ r)
    apply Finite.of_injective
      (fun J : {J : Depth r // DepthBridge θ r J} =>
        (⟨depthLetters θ r J.val, depth_letters_endpoint θ r J.val J.property⟩ :
          {w : Word r // wordPrefix r w (Fin.last r) = floorAt θ r}))
    intro a b hab
    apply Subtype.ext
    have he := congrArg (fun w => wordDepth θ r w) (congrArg Subtype.val hab)
    simpa only [wordDepth_depthLetters θ r a.val a.property,
      wordDepth_depthLetters θ r b.val b.property] using he

noncomputable def source_floor_equiv (r : ℕ) (hr : StrictRung slope r) :
    {w : Word r // SourceWord slope r w} ≃ {w : Word r // FloorWord slope r w} :=
  Classical.choose (ExternalFiniteBridgeTransport.source_floor_bijection slope r
    (le_of_lt source_slope_facts.1) hr (source_slope_nonintegral r hr.1))

theorem source_floor_equiv_apply (r : ℕ) (hr : StrictRung slope r)
    (w : {w : Word r // SourceWord slope r w}) :
    (source_floor_equiv r hr w).val = lowerLast r w.val := by
  exact (Classical.choose_spec (ExternalFiniteBridgeTransport.source_floor_bijection slope r
    (le_of_lt source_slope_facts.1) hr (source_slope_nonintegral r hr.1))).1 w

theorem source_floor_equiv_symm (r : ℕ) (hr : StrictRung slope r)
    (w : {w : Word r // FloorWord slope r w}) :
    ((source_floor_equiv r hr).symm w).val = raiseLast r w.val := by
  exact (Classical.choose_spec (ExternalFiniteBridgeTransport.source_floor_bijection slope r
    (le_of_lt source_slope_facts.1) hr (source_slope_nonintegral r hr.1))).2 w

noncomputable def source_depth_equiv (r : ℕ) (hr : StrictRung slope r) :
    {w : Word r // SourceWord slope r w} ≃ {J : Depth r // DepthBridge slope r J} :=
  (source_floor_equiv r hr).trans (floor_depth_equiv slope r hr.1)

theorem source_depth_equiv_apply (r : ℕ) (hr : StrictRung slope r)
    (w : {w : Word r // SourceWord slope r w}) :
    (source_depth_equiv r hr w).val = sourceBridgeDepth slope r w.val := by
  change wordDepth slope r (source_floor_equiv r hr w).val = _
  rw [source_floor_equiv_apply]
  rfl

theorem source_depth_equiv_symm (r : ℕ) (hr : StrictRung slope r)
    (J : {J : Depth r // DepthBridge slope r J}) :
    ((source_depth_equiv r hr).symm J).val = raiseLast r (depthLetters slope r J.val) := by
  change ((source_floor_equiv r hr).symm ((floor_depth_equiv slope r hr.1).symm J)).val = _
  rw [source_floor_equiv_symm]
  rfl

theorem source_depth_bijection : SourceDepthBijection := by
  intro r hr
  exact ⟨source_depth_equiv r hr, source_depth_equiv_apply r hr, source_depth_equiv_symm r hr⟩

noncomputable def selected_equiv {A B : Type} (P : A → Prop) (Q : B → Prop)
    (f : A → ℝ) (g : B → ℝ) (e : {a // P a} ≃ {b // Q b})
    (he : ∀ a, f a.val = g (e a).val) (q : ℝ) :
    {a // P a ∧ q ≤ f a} ≃ {b // Q b ∧ q ≤ g b} where
  toFun a := ⟨(e ⟨a.val, a.property.1⟩).val,
    (e ⟨a.val, a.property.1⟩).property, by
      rw [← he]; exact a.property.2⟩
  invFun b := ⟨(e.symm ⟨b.val, b.property.1⟩).val,
    (e.symm ⟨b.val, b.property.1⟩).property, by
      have hh := he (e.symm ⟨b.val, b.property.1⟩)
      rw [e.apply_symm_apply] at hh
      rw [hh]; exact b.property.2⟩
  left_inv a := by
    apply Subtype.ext
    exact congrArg (fun z : {a // P a} => z.val) (e.symm_apply_apply ⟨a.val, a.property.1⟩)
  right_inv b := by
    apply Subtype.ext
    exact congrArg (fun z : {b // Q b} => z.val) (e.apply_symm_apply ⟨b.val, b.property.1⟩)

theorem threshold_count_preservation : ThresholdCountPreservation := by
  intro r hr q
  have hfin := finite_populations slope r
  have hsf : ∀ w : {w : Word r // SourceWord slope r w},
      reward r w.val = reward r (source_floor_equiv r hr w).val := by
    intro w
    rw [source_floor_equiv_apply]
    exact (reward_endpoint_invariant r w.val).1.symm
  have hsd : ∀ w : {w : Word r // SourceWord slope r w},
      reward r w.val = depthReward slope r (source_depth_equiv r hr w).val := by
    intro w
    rw [source_depth_equiv_apply]
    exact source_depth_reward r w.val
  exact ⟨Nat.card_congr (selected_equiv _ _ (reward r) (reward r) (source_floor_equiv r hr) hsf q),
    Nat.card_congr (selected_equiv _ _ (reward r) (depthReward slope r) (source_depth_equiv r hr) hsd q)⟩

end ExternalFiniteBridgeFinite
