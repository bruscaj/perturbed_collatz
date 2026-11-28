import OptimizationExpectedTypes

/-! Exact finite vertex/edge dictionary, retaining labeled parallel exits. -/
namespace ExternalO3OptimizationEncoding
open ExternalO3OptimizationDraft ExternalO3GeneralDraft
open scoped BigOperators

theorem decodeVertex_injective (h : Depth) (M : ℕ) : Function.Injective (decodeVertex h M) := by
  intro v w hv
  funext i
  apply Fin.ext
  have hi := congrFun hv i
  simp only [decodeVertex] at hi
  omega

theorem vertex_image (h : Depth) (M : ℕ) (w : Window h) :
    (∃ v : Vertex h M, decodeVertex h M v = w) ↔ ∀ i, 1 ≤ w i ∧ w i ≤ M := by
  constructor
  · rintro ⟨v, rfl⟩ i
    have hi := (v i).isLt
    simp only [decodeVertex]
    omega
  · intro hw
    let v : Vertex h M := fun i => ⟨w i - 1, by have := hw i; omega⟩
    refine ⟨v, ?_⟩
    funext i
    have := hw i
    simp only [decodeVertex, v]
    omega

theorem vertex_encoding_and_extension : VertexEncodingAndExtension := by
  intro h M _hM
  refine ⟨decodeVertex_injective h M, vertex_image h M, ?_⟩
  intro ψ
  exact ⟨Function.extend (decodeVertex h M) ψ (fun _ => 0),
    fun v => (decodeVertex_injective h M).extend_apply ψ (fun _ => 0) v⟩

theorem ascending_head_positive (h : Depth) (M : ℕ) (a : AscendingEdge h M)
    (i : Fin h.val) (hi : i.val = 0) : 0 < (a.val i).val := by
  have he : i = zeroIndex h := Fin.ext hi
  simpa only [he] using a.property

theorem labelSource_ascending (h : Depth) (M J : ℕ) (a : AscendingEdge h M) :
    labelSource h (edgeLabel h M J (.inl a)) = decodeVertex h M a.val := by
  funext i
  by_cases hi : i.val = 0
  · have hp := ascending_head_positive h M a i hi
    simp only [labelSource, edgeLabel, ascendingWindow, hi, ite_true, decodeVertex]
    omega
  · simp only [labelSource, edgeLabel, ascendingWindow, hi, ite_false, decodeVertex]

theorem source_window (h : Depth) (M J : ℕ) (a : TruncatedEdge h M J) :
    decodeVertex h M (edgeSource h M J a) = labelSource h (edgeLabel h M J a) := by
  cases a with
  | inl a => exact (labelSource_ascending h M J a).symm
  | inr p =>
    rcases p with ⟨k,v⟩
    funext i
    by_cases hi : i.val = 0
    · simp [edgeSource, exitSource, decodeVertex, labelSource, edgeLabel, prependOne, hi]
    · simp [edgeSource, exitSource, decodeVertex, labelSource, edgeLabel, prependOne, positiveWindow, hi]

theorem target_window (h : Depth) (M J : ℕ) (a : TruncatedEdge h M J) :
    decodeVertex h M (edgeTarget h M J a) = labelTarget h (edgeLabel h M J a) := by
  cases a with
  | inl a =>
    funext i
    by_cases hi : i.val = 0
    · have hp := ascending_head_positive h M a i hi
      simp only [edgeTarget, ascTarget, decodeVertex, labelTarget, edgeLabel,
        decrementHead, ascendingWindow, hi, ite_true]
      omega
    · simp only [edgeTarget, ascTarget, decodeVertex, labelTarget, edgeLabel,
        decrementHead, ascendingWindow, hi, ite_false]
  | inr p => rfl

theorem rationalWeight_as_zpow (h : Depth) (M J : ℕ) (a : TruncatedEdge h M J) :
    (rationalWeight h M J a : ℝ) = (2 : ℝ) ^ (-((weightExponent h M J a : ℕ) : ℤ)) := by
  simp [rationalWeight, zpow_neg, zpow_natCast]

theorem edge_weight (h : Depth) (M J : ℕ) (a : TruncatedEdge h M J) :
    (rationalWeight h M J a : ℝ) = weight h (edgeLabel h M J a) := by
  rw [rationalWeight_as_zpow]
  cases a with
  | inl a =>
    change (2 : ℝ) ^ (-((weightExponent h M J (.inl a) : ℕ) : ℤ)) =
      (2 : ℝ) ^ (-((windowSum h (labelSource h (edgeLabel h M J (.inl a))) : ℕ) : ℤ))
    rw [labelSource_ascending]
    rfl
  | inr p => rfl

theorem corrected_gain (h : Depth) (M J : ℕ) (a : TruncatedEdge h M J) (φ : Correction h) :
    edgeGain (truncatedGraph h M J) (fun v => φ (decodeVertex h M v)) a =
      gain h φ (edgeLabel h M J a) := by
  change Real.log 3 - (halvingExponent h M J a : ℝ) * Real.log 2 +
    φ (decodeVertex h M (edgeTarget h M J a)) -
    φ (decodeVertex h M (edgeSource h M J a)) = _
  rw [source_window, target_window]
  cases a with
  | inl a =>
    simp only [halvingExponent, Nat.cast_one, one_mul, edgeLabel, labelTarget, labelSource, gain]
    rw [Real.log_div (by norm_num) (by norm_num)]
  | inr p => rfl

theorem edgeLabel_injective (h : Depth) (M J : ℕ) : Function.Injective (edgeLabel h M J) := by
  intro a b hab
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      apply congrArg Sum.inl
      apply Subtype.ext
      apply decodeVertex_injective h M
      have hs := congrArg (labelSource h) hab
      rw [labelSource_ascending, labelSource_ascending] at hs
      exact hs
    | inr b => simp [edgeLabel] at hab
  | inr a =>
    cases b with
    | inl b => simp [edgeLabel] at hab
    | inr b =>
      rcases a with ⟨k,v⟩
      rcases b with ⟨l,w⟩
      have hp := Sum.inr.inj hab
      apply congrArg Sum.inr
      apply Prod.ext
      · apply Fin.ext
        exact congrArg Prod.fst hp
      · funext i
        apply Fin.ext
        exact congrArg (fun p => p.2 i) hp

theorem retained_label (h : Depth) (M J : ℕ) (a : TruncatedEdge h M J) :
    Retained h M J (edgeLabel h M J a) := by
  cases a with
  | inl a =>
    intro i
    have he := congrFun (labelSource_ascending h M J a) i
    change ascendingWindow h (fun j => if j.val = 0 then (a.val j).val - 1 else (a.val j).val) i =
      (a.val i).val + 1 at he
    change ascendingWindow h (fun j => if j.val = 0 then (a.val j).val - 1 else (a.val j).val) i ≤ M
    rw [he]
    have := (a.val i).isLt
    omega
  | inr p =>
    rcases p with ⟨k,v⟩
    change k.val + 2 ≤ J ∧ ∀ i, (v i).val + 1 ≤ M
    constructor
    · have := k.isLt
      omega
    · intro i
      have := (v i).isLt
      omega

theorem retained_image (h : Depth) (M J : ℕ) (e : Edge h) :
    Retained h M J e ↔ ∃ a, edgeLabel h M J a = e := by
  constructor
  · intro he
    cases e with
    | inl b =>
      have hw : ∀ i, 1 ≤ ascendingWindow h b i ∧ ascendingWindow h b i ≤ M := by
        intro i
        refine ⟨?_, he i⟩
        simp only [ascendingWindow]
        split_ifs <;> omega
      obtain ⟨v,hv⟩ := (vertex_image h M (ascendingWindow h b)).mpr hw
      have hp : 0 < (v (zeroIndex h)).val := by
        have hi := congrFun hv (zeroIndex h)
        simp only [decodeVertex, ascendingWindow, show (zeroIndex h).val = 0 from rfl, ite_true] at hi
        omega
      let a : AscendingEdge h M := ⟨v,hp⟩
      refine ⟨.inl a, ?_⟩
      apply congrArg Sum.inl
      funext i
      have hi := congrFun hv i
      by_cases hi0 : i.val = 0
      · simp only [a, hi0, ite_true]
        simp only [decodeVertex, ascendingWindow, hi0, ite_true] at hi
        omega
      · simp only [a, hi0, ite_false]
        simp only [decodeVertex, ascendingWindow, hi0, ite_false] at hi
        omega
    | inr p =>
      rcases p with ⟨k,b⟩
      change k + 2 ≤ J ∧ ∀ i, b i + 1 ≤ M at he
      let kf : Fin (J - 1) := ⟨k, by omega⟩
      let v : Vertex h M := fun i => ⟨b i, by have := he.2 i; omega⟩
      exact ⟨.inr (kf,v), rfl⟩
  · rintro ⟨a,rfl⟩
    exact retained_label h M J a

/-- Both endpoint windows, every labeled edge and its exact dyadic/gain data. -/
theorem edge_encoding_and_weights : EdgeEncodingAndWeights := by
  intro h M J _hM _hJ
  refine ⟨edgeLabel_injective h M J, retained_image h M J, ?_⟩
  intro a
  exact ⟨source_window h M J a, target_window h M J a, edge_weight h M J a,
    corrected_gain h M J a⟩

end ExternalO3OptimizationEncoding
