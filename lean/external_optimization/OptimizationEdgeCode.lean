import OptimizationVertexCode

/-! Exact finite edge IDs, preserving the distinct parallel exit labels. -/
namespace ExternalO3OptimizationEdgeCode

open ExternalO3OptimizationCode ExternalO3OptimizationDraft
open ExternalO3OptimizationVertexCode
open scoped BigOperators

abbrev CanonicalEdge (p : Input) :=
  TruncatedEdge (ExternalO3RateDraft.succDepth p.1) (base p) (cap p)

abbrev ValidCode (p : Input) := {c : Fin (edges p) // valid p c.val = true}

def encodeNat (p : Input) : CanonicalEdge p → ℕ
  | .inl a => (vertexCodeEquiv p a.val).val
  | .inr (k, v) => (k.val + 1) * vertices p + (vertexCodeEquiv p v).val

theorem vertices_pos (p : Input) : 0 < vertices p := by
  exact pow_pos (by unfold base; omega) _

theorem encodeNat_lt (p : Input) (a : CanonicalEdge p) : encodeNat p a < edges p := by
  have hN := vertices_pos p
  have hJ : 2 ≤ cap p := by unfold cap; omega
  rcases a with a | ⟨k,v⟩
  · have hv := (vertexCodeEquiv p a.val).isLt
    change (vertexCodeEquiv p a.val).val < cap p * vertices p
    nlinarith
  · have hv := (vertexCodeEquiv p v).isLt
    have hk : k.val + 2 ≤ cap p := by have := k.isLt; omega
    change (k.val + 1) * vertices p + (vertexCodeEquiv p v).val < cap p * vertices p
    nlinarith

theorem encodeNat_tag_asc (p : Input)
    (a : AscendingEdge (ExternalO3RateDraft.succDepth p.1) (base p)) :
    tag p (encodeNat p (.inl a)) = 0 := by
  exact Nat.div_eq_of_lt (vertexCodeEquiv p a.val).isLt

theorem encodeNat_vertex_asc (p : Input)
    (a : AscendingEdge (ExternalO3RateDraft.succDepth p.1) (base p)) :
    vertex p (encodeNat p (.inl a)) = (vertexCodeEquiv p a.val).val := by
  exact Nat.mod_eq_of_lt (vertexCodeEquiv p a.val).isLt

theorem encodeNat_tag_exit (p : Input) (k : Fin (cap p - 1))
    (v : Vertex (ExternalO3RateDraft.succDepth p.1) (base p)) :
    tag p (encodeNat p (.inr (k,v))) = k.val + 1 := by
  change ((k.val+1)*vertices p+(vertexCodeEquiv p v).val)/vertices p = k.val+1
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (vertices_pos p),
    Nat.div_eq_of_lt (vertexCodeEquiv p v).isLt, Nat.zero_add]

theorem encodeNat_vertex_exit (p : Input) (k : Fin (cap p - 1))
    (v : Vertex (ExternalO3RateDraft.succDepth p.1) (base p)) :
    vertex p (encodeNat p (.inr (k,v))) = (vertexCodeEquiv p v).val := by
  change ((k.val+1)*vertices p+(vertexCodeEquiv p v).val)%vertices p = _
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (vertexCodeEquiv p v).isLt]

theorem encodeNat_valid (p : Input) (a : CanonicalEdge p) : valid p (encodeNat p a) = true := by
  simp only [valid, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true]
  refine ⟨encodeNat_lt p a, ?_⟩
  rcases a with a | ⟨k,v⟩
  · right
    rw [encodeNat_vertex_asc]
    have hd := vertexCodeEquiv_digit p a.val
      (ExternalO3GeneralDraft.zeroIndex (ExternalO3RateDraft.succDepth p.1))
    simp only [digit, ExternalO3GeneralDraft.zeroIndex, pow_zero, Nat.div_one] at hd
    rw [hd]
    exact a.property
  · left
    rw [encodeNat_tag_exit]
    omega

def encode (p : Input) (a : CanonicalEdge p) : ValidCode p :=
  ⟨⟨encodeNat p a, encodeNat_lt p a⟩, encodeNat_valid p a⟩

theorem encodeNat_injective (p : Input) : Function.Injective (encodeNat p) := by
  intro a b hab
  have ht := congrArg (tag p) hab
  have hv := congrArg (vertex p) hab
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      simp only [encodeNat_vertex_asc] at hv
      apply congrArg Sum.inl
      apply Subtype.ext
      apply (vertexCodeEquiv p).injective
      exact Fin.ext hv
    | inr b =>
      rcases b with ⟨k,v⟩
      simp only [encodeNat_tag_asc, encodeNat_tag_exit] at ht
      omega
  | inr a =>
    rcases a with ⟨k,v⟩
    cases b with
    | inl b =>
      simp only [encodeNat_tag_asc, encodeNat_tag_exit] at ht
      omega
    | inr b =>
      rcases b with ⟨l,w⟩
      simp only [encodeNat_tag_exit] at ht
      change k.val + 1 = l.val + 1 at ht
      simp only [encodeNat_vertex_exit] at hv
      apply congrArg Sum.inr
      apply Prod.ext
      · exact Fin.ext (Nat.add_right_cancel ht)
      · apply (vertexCodeEquiv p).injective
        exact Fin.ext hv

theorem encode_injective (p : Input) : Function.Injective (encode p) := by
  intro a b hab
  exact encodeNat_injective p (congrArg (fun c : ValidCode p => c.val.val) hab)

theorem encode_surjective (p : Input) : Function.Surjective (encode p) := by
  intro c
  have hN := vertices_pos p
  let q : Fin (vertices p) := ⟨vertex p c.val.val, Nat.mod_lt _ hN⟩
  let v := (vertexCodeEquiv p).symm q
  have hv : (vertexCodeEquiv p v).val = vertex p c.val.val := by
    exact congrArg Fin.val ((vertexCodeEquiv p).apply_symm_apply q)
  have hc := c.property
  simp only [valid, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at hc
  have ht : tag p c.val.val < cap p := by
    exact (Nat.div_lt_iff_lt_mul hN).mpr c.val.isLt
  have hd := Nat.div_add_mod c.val.val (vertices p)
  by_cases hz : tag p c.val.val = 0
  · have hp : 0 < vertex p c.val.val % base p := by
      rcases hc.2 with hn | hp
      · exact False.elim (hn hz)
      · exact hp
    have hhead : 0 < (v (ExternalO3GeneralDraft.zeroIndex
        (ExternalO3RateDraft.succDepth p.1))).val := by
      have hh := vertexCodeEquiv_digit p v (ExternalO3GeneralDraft.zeroIndex
        (ExternalO3RateDraft.succDepth p.1))
      simp only [digit, ExternalO3GeneralDraft.zeroIndex, pow_zero, Nat.div_one] at hh
      rw [hv] at hh
      exact hp.trans_eq hh
    refine ⟨.inl ⟨v,hhead⟩, ?_⟩
    apply Subtype.ext
    apply Fin.ext
    change (vertexCodeEquiv p v).val = c.val.val
    rw [hv]
    change vertices p * tag p c.val.val + vertex p c.val.val = c.val.val at hd
    rw [hz] at hd
    simpa using hd
  · let k : Fin (cap p - 1) := ⟨tag p c.val.val - 1, by omega⟩
    refine ⟨.inr (k,v), ?_⟩
    apply Subtype.ext
    apply Fin.ext
    change (k.val+1)*vertices p+(vertexCodeEquiv p v).val = c.val.val
    rw [hv]
    have hk : k.val + 1 = tag p c.val.val := by dsimp [k]; omega
    rw [hk]
    simpa [tag,vertex,Nat.mul_comm] using hd

/-- Actual labelled edges are exactly the valid program IDs. -/
noncomputable def edgeCodeEquiv (p : Input) : CanonicalEdge p ≃ ValidCode p :=
  Equiv.ofBijective (encode p) ⟨encode_injective p, encode_surjective p⟩

theorem edgeCodeEquiv_val (p : Input) (a : CanonicalEdge p) :
    (edgeCodeEquiv p a).val.val = encodeNat p a := by rfl

theorem source_encodeNat (p : Input) (a : CanonicalEdge p) :
    source p (encodeNat p a) =
      (vertexCodeEquiv p (edgeSource (ExternalO3RateDraft.succDepth p.1) (base p) (cap p) a)).val := by
  rcases a with a | ⟨k,v⟩
  · simp only [source, encodeNat_tag_asc, ↓reduceIte, encodeNat_vertex_asc, edgeSource]
  · simp only [source, encodeNat_tag_exit, Nat.add_one_ne_zero, ↓reduceIte,
      encodeNat_vertex_exit, edgeSource]
    exact (vertexCodeEquiv_exitSource p v).symm

theorem target_encodeNat (p : Input) (a : CanonicalEdge p) :
    target p (encodeNat p a) =
      (vertexCodeEquiv p (edgeTarget (ExternalO3RateDraft.succDepth p.1) (base p) (cap p) a)).val := by
  rcases a with a | ⟨k,v⟩
  · simp only [target, encodeNat_tag_asc, ↓reduceIte, encodeNat_vertex_asc, edgeTarget]
    exact (vertexCodeEquiv_ascTarget p a.val a.property).symm
  · simp only [target, encodeNat_tag_exit, Nat.add_one_ne_zero, ↓reduceIte,
      encodeNat_vertex_exit, edgeTarget]

theorem halvings_encodeNat (p : Input) (a : CanonicalEdge p) :
    halvings p (encodeNat p a) =
      halvingExponent (ExternalO3RateDraft.succDepth p.1) (base p) (cap p) a := by
  rcases a with a | ⟨k,v⟩
  · simp only [halvings, encodeNat_tag_asc, ↓reduceIte, halvingExponent]
  · simp only [halvings, encodeNat_tag_exit, Nat.add_one_ne_zero, ↓reduceIte, halvingExponent]

theorem sumTo_eq_fin_sum (n : ℕ) (f : ℕ → ℕ) :
    sumTo n f = ∑ i : Fin n, f i.val := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change sumTo n f + f n = ∑ i : Fin (n+1), f i.val
    rw [Fin.sum_univ_castSucc, ih]
    rfl

theorem digitSum_vertexCode (p : Input)
    (v : Vertex (ExternalO3RateDraft.succDepth p.1) (base p)) :
    digitSum (base p) (depth p) (vertexCodeEquiv p v).val =
      ∑ i : Fin (depth p), (v i).val := by
  rw [digitSum, sumTo_eq_fin_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact vertexCodeEquiv_digit p v i

theorem exponent_encodeNat (p : Input) (a : CanonicalEdge p) :
    exponent p (encodeNat p a) =
      weightExponent (ExternalO3RateDraft.succDepth p.1) (base p) (cap p) a := by
  rcases a with a | ⟨k,v⟩
  · simp only [exponent, encodeNat_tag_asc, ↓reduceIte, encodeNat_vertex_asc,
      digitSum_vertexCode, weightExponent]
    change 0 + depth p + (∑ i : Fin (depth p), (a.val i).val) =
      ∑ i : Fin (depth p), ((a.val i).val + 1)
    simp [Finset.sum_add_distrib, Nat.add_comm]
  · simp only [exponent, encodeNat_tag_exit, Nat.add_one_ne_zero, ↓reduceIte,
      encodeNat_vertex_exit, digitSum_vertexCode, weightExponent, halvings, encodeNat_tag_exit,
      Nat.add_one_ne_zero, ↓reduceIte]
    change (k.val + 1 + 1) + depth p + (∑ i : Fin (depth p), (v i).val) =
      (k.val + 2) + ∑ i : Fin (depth p), ((v i).val + 1)
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
    omega

theorem edgeCodeEquiv_source (p : Input) (a : CanonicalEdge p) :
    source p (edgeCodeEquiv p a).val.val =
      (vertexCodeEquiv p (edgeSource (ExternalO3RateDraft.succDepth p.1) (base p) (cap p) a)).val :=
  source_encodeNat p a

theorem edgeCodeEquiv_target (p : Input) (a : CanonicalEdge p) :
    target p (edgeCodeEquiv p a).val.val =
      (vertexCodeEquiv p (edgeTarget (ExternalO3RateDraft.succDepth p.1) (base p) (cap p) a)).val :=
  target_encodeNat p a

theorem edgeCodeEquiv_halvings (p : Input) (a : CanonicalEdge p) :
    halvings p (edgeCodeEquiv p a).val.val =
      halvingExponent (ExternalO3RateDraft.succDepth p.1) (base p) (cap p) a :=
  halvings_encodeNat p a

theorem edgeCodeEquiv_exponent (p : Input) (a : CanonicalEdge p) :
    exponent p (edgeCodeEquiv p a).val.val =
      weightExponent (ExternalO3RateDraft.succDepth p.1) (base p) (cap p) a :=
  exponent_encodeNat p a

theorem edgeCodeEquiv_asc_val (p : Input)
    (a : AscendingEdge (ExternalO3RateDraft.succDepth p.1) (base p)) :
    (edgeCodeEquiv p (.inl a)).val.val = (vertexCodeEquiv p a.val).val := by rfl

theorem edgeCodeEquiv_exit_val (p : Input) (k : Fin (cap p - 1))
    (v : Vertex (ExternalO3RateDraft.succDepth p.1) (base p)) :
    (edgeCodeEquiv p (.inr (k,v))).val.val =
      (k.val+1)*vertices p + (vertexCodeEquiv p v).val := by rfl

theorem common_eq (p : Input) :
    common p = commonExponent (ExternalO3RateDraft.succDepth p.1) (base p) (cap p) := by rfl

theorem edgeCodeEquiv_units (p : Input) (a : CanonicalEdge p) :
    units p (edgeCodeEquiv p a).val.val =
      2 ^ (commonExponent (ExternalO3RateDraft.succDepth p.1) (base p) (cap p) -
        weightExponent (ExternalO3RateDraft.succDepth p.1) (base p) (cap p) a) := by
  rw [units, edgeCodeEquiv_exponent, common_eq]

end ExternalO3OptimizationEdgeCode
