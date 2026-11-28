import OptimizationCode
import OptimizationEncoding
import OptimizationPaths
import OptimizationArithmetic
import OptimizationEdgeCode

/-! Executable-loop and computability foundations. No A01 assertion is made
before the concrete code-to-canonical graph correctness proof is complete. -/
namespace ExternalO3OptimizationAlgorithm
open ExternalO3OptimizationCode ExternalO3OptimizationVertexCode ExternalO3OptimizationEdgeCode
open ExternalO3OptimizationDraft
open scoped BigOperators

theorem foldTo_zero {α : Type} (z : α) (f : ℕ → α → α) : foldTo 0 z f = z := rfl

theorem foldTo_succ {α : Type} (n : ℕ) (z : α) (f : ℕ → α → α) :
    foldTo (n + 1) z f = f n (foldTo n z f) := rfl

theorem sumTo_eq_sum_range (n : ℕ) (f : ℕ → ℕ) : sumTo n f = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [sumTo, foldTo_succ, Finset.sum_range_succ] using congrArg (fun v => v + f n) ih

theorem allTo_eq_true (n : ℕ) (f : ℕ → Bool) : allTo n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => simp [allTo, foldTo]
  | succ n ih =>
    simp only [allTo, foldTo_succ, Bool.and_eq_true] at *
    constructor
    · rintro ⟨hl,hr⟩ i hi
      rcases lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | rfl
      · exact ih.mp hl i hi
      · exact hr
    · intro h
      exact ⟨ih.mpr (fun i hi => h i (by omega)), h n (by omega)⟩

theorem primrec_pow : Primrec₂ (fun a b : ℕ => a ^ b) := by
  have hs : Primrec₂ (fun (a : ℕ) (p : ℕ × ℕ) => p.2 * a) :=
    (Primrec.nat_mul.comp (Primrec.snd.comp Primrec.snd) Primrec.fst).to₂
  apply (Primrec.nat_rec (Primrec.const 1) hs).of_eq
  intro a n
  induction n with
  | zero => rfl
  | succ n ih => simpa only [Nat.rec_add_one, pow_succ] using congrArg (fun v => v * a) ih

theorem primrec_foldTo {α β : Type} [Primcodable α] [Primcodable β]
    {n : α → ℕ} {z : α → β} {f : α → ℕ × β → β}
    (hn : Primrec n) (hz : Primrec z) (hf : Primrec₂ f) :
    Primrec (fun a => foldTo (n a) (z a) (fun i v => f a (i,v))) := by
  exact Primrec.nat_rec' hn hz hf

theorem primrec_sumTo {α : Type} [Primcodable α] {n : α → ℕ} {f : α → ℕ → ℕ}
    (hn : Primrec n) (hf : Primrec₂ f) : Primrec (fun a => sumTo (n a) (f a)) :=
  primrec_foldTo hn (Primrec.const 0)
    (Primrec.nat_add.comp (Primrec.snd.comp Primrec.snd)
      (hf.comp Primrec.fst (Primrec.fst.comp Primrec.snd))).to₂

theorem primrec_allTo {α : Type} [Primcodable α] {n : α → ℕ} {f : α → ℕ → Bool}
    (hn : Primrec n) (hf : Primrec₂ f) : Primrec (fun a => allTo (n a) (f a)) :=
  primrec_foldTo hn (Primrec.const true)
    (Primrec.and.comp (Primrec.snd.comp Primrec.snd)
      (hf.comp Primrec.fst (Primrec.fst.comp Primrec.snd))).to₂

theorem primrec_digit : Primrec (fun p : ℕ × ℕ × ℕ => digit p.1 p.2.1 p.2.2) :=
  Primrec.nat_mod.comp
    (Primrec.nat_div.comp (Primrec.fst.comp Primrec.snd)
      (primrec_pow.comp Primrec.fst (Primrec.snd.comp Primrec.snd))) Primrec.fst

theorem primrec_digitSum : Primrec (fun p : ℕ × ℕ × ℕ => digitSum p.1 p.2.1 p.2.2) :=
  primrec_sumTo (Primrec.fst.comp Primrec.snd)
    (primrec_digit.comp ((Primrec.fst.comp Primrec.fst).pair
      ((Primrec.snd.comp (Primrec.snd.comp Primrec.fst)).pair Primrec.snd))).to₂

theorem primrec_depth : Primrec depth := Primrec.nat_add.comp Primrec.fst (Primrec.const 1)
theorem primrec_base : Primrec base := Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 2)
theorem primrec_cap : Primrec cap := Primrec.nat_add.comp (Primrec.snd.comp Primrec.snd) (Primrec.const 2)
theorem primrec_vertices : Primrec vertices := primrec_pow.comp primrec_base primrec_depth
theorem primrec_edges : Primrec edges := Primrec.nat_mul.comp primrec_cap primrec_vertices

theorem primrec_tag : Primrec₂ tag := Primrec.nat_div.comp Primrec.snd (primrec_vertices.comp Primrec.fst)
theorem primrec_vertex : Primrec₂ vertex := Primrec.nat_mod.comp Primrec.snd (primrec_vertices.comp Primrec.fst)

theorem primrec_valid : Primrec₂ valid :=
  Primrec.and.comp
    (Primrec.nat_lt.comp Primrec.snd (primrec_edges.comp Primrec.fst)).decide
    (Primrec.or.comp (Primrec.eq.comp primrec_tag (Primrec.const 0)).not.decide
      (Primrec.nat_lt.comp (Primrec.const 0)
        (Primrec.nat_mod.comp primrec_vertex (primrec_base.comp Primrec.fst))).decide)

theorem primrec_source : Primrec₂ source :=
  Primrec.ite (Primrec.eq.comp primrec_tag (Primrec.const 0)) primrec_vertex
    (Primrec.nat_mul.comp (primrec_base.comp Primrec.fst)
      (Primrec.nat_mod.comp primrec_vertex
        (primrec_pow.comp (primrec_base.comp Primrec.fst)
          (Primrec.nat_sub.comp (primrec_depth.comp Primrec.fst) (Primrec.const 1)))))

theorem primrec_target : Primrec₂ target :=
  Primrec.ite (Primrec.eq.comp primrec_tag (Primrec.const 0))
    (Primrec.nat_sub.comp primrec_vertex (Primrec.const 1)) primrec_vertex

theorem primrec_halvings : Primrec₂ halvings :=
  Primrec.ite (Primrec.eq.comp primrec_tag (Primrec.const 0)) (Primrec.const 1)
    (Primrec.nat_add.comp primrec_tag (Primrec.const 1))

theorem primrec_exponent : Primrec₂ exponent :=
  Primrec.nat_add.comp
    (Primrec.nat_add.comp
      (Primrec.ite (Primrec.eq.comp primrec_tag (Primrec.const 0)) (Primrec.const 0) primrec_halvings)
      (primrec_depth.comp Primrec.fst))
    (primrec_digitSum.comp ((primrec_base.comp Primrec.fst).pair
      ((primrec_depth.comp Primrec.fst).pair primrec_vertex)))

theorem primrec_common : Primrec common :=
  Primrec.nat_add.comp primrec_cap (Primrec.nat_mul.comp primrec_depth primrec_base)

theorem primrec_units : Primrec₂ units :=
  primrec_pow.comp (Primrec.const 2)
    (Primrec.nat_sub.comp (primrec_common.comp Primrec.fst) primrec_exponent)

theorem primrec_deleted : Primrec₂ deleted :=
  (Primrec.eq.comp (Primrec.nat_mod.comp
    (Primrec.nat_div.comp Primrec.fst (primrec_pow.comp (Primrec.const 2) Primrec.snd))
    (Primrec.const 2)) (Primrec.const 1)).decide

theorem primrec_edgeAt : Primrec (fun p : Input × ℕ × ℕ => edgeAt p.1 p.2.1 p.2.2) :=
  primrec_digit.comp ((primrec_edges.comp Primrec.fst).pair Primrec.snd)

theorem primrec_wordHalvings :
    Primrec (fun a : Input × ℕ × ℕ => wordHalvings a.1 a.2.1 a.2.2) :=
  primrec_sumTo (Primrec.fst.comp Primrec.snd)
    (primrec_halvings.comp (Primrec.fst.comp Primrec.fst)
      (primrec_edgeAt.comp ((Primrec.fst.comp Primrec.fst).pair
        ((Primrec.snd.comp (Primrec.snd.comp Primrec.fst)).pair Primrec.snd)))).to₂

theorem primrec_survivingClosed :
    Primrec (fun a : Input × ℕ × ℕ × ℕ => survivingClosed a.1 a.2.1 a.2.2.1 a.2.2.2) := by
  let hp : Primrec (fun x : (Input × ℕ × ℕ × ℕ) × ℕ => x.1.1) := Primrec.fst.comp Primrec.fst
  let hm : Primrec (fun x : (Input × ℕ × ℕ × ℕ) × ℕ => x.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  let hn : Primrec (fun x : (Input × ℕ × ℕ × ℕ) × ℕ => x.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  let hq : Primrec (fun x : (Input × ℕ × ℕ × ℕ) × ℕ => x.1.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  let he := primrec_edgeAt.comp (hp.pair (hq.pair Primrec.snd))
  let hnext := primrec_edgeAt.comp (hp.pair (hq.pair
    (Primrec.nat_mod.comp (Primrec.nat_add.comp Primrec.snd (Primrec.const 1)) hn)))
  exact primrec_allTo (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    (Primrec.and.comp
      (Primrec.and.comp (primrec_valid.comp hp he) (Primrec.not.comp (primrec_deleted.comp hm he)))
      (Primrec.eq.comp (primrec_target.comp hp he) (primrec_source.comp hp hnext)).decide).to₂

theorem primrec_safe : Primrec₂ safe := by
  let hp : Primrec (fun x : ((Input × ℕ) × ℕ) × ℕ => x.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  let hm : Primrec (fun x : ((Input × ℕ) × ℕ) × ℕ => x.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  let hn : Primrec (fun x : ((Input × ℕ) × ℕ) × ℕ => x.1.2 + 1) :=
    Primrec.nat_add.comp (Primrec.snd.comp Primrec.fst) (Primrec.const 1)
  let hc := primrec_survivingClosed.comp (hp.pair (hm.pair (hn.pair Primrec.snd)))
  let hh := primrec_wordHalvings.comp (hp.pair (hn.pair Primrec.snd))
  let ht := (Primrec.nat_lt.comp (primrec_pow.comp (Primrec.const 3) hn)
    (primrec_pow.comp (Primrec.const 2) hh)).decide
  have hbody := Primrec.or.comp (Primrec.not.comp hc) ht
  have hbound : Primrec (fun x : (Input × ℕ) × ℕ => edges x.1.1 ^ (x.2 + 1)) :=
    primrec_pow.comp (primrec_edges.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.nat_add.comp Primrec.snd (Primrec.const 1))
  exact primrec_allTo (primrec_vertices.comp Primrec.fst) (primrec_allTo hbound hbody.to₂).to₂

theorem primrec_boolIte {α β : Type} [Primcodable α] [Primcodable β]
    {c : α → Bool} {f g : α → β} (hc : Primrec c) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => if c a then f a else g a) :=
  Primrec.ite (Primrec.eq.comp hc (Primrec.const true)) hf hg

theorem primrec_cost : Primrec₂ cost :=
  primrec_sumTo (primrec_edges.comp Primrec.fst)
    (primrec_boolIte
      (Primrec.and.comp (primrec_valid.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
        (primrec_deleted.comp (Primrec.snd.comp Primrec.fst) Primrec.snd))
      (primrec_units.comp (Primrec.fst.comp Primrec.fst) Primrec.snd) (Primrec.const 0)).to₂

theorem primrec_allCost : Primrec allCost :=
  primrec_sumTo primrec_edges (primrec_boolIte primrec_valid primrec_units (Primrec.const 0)).to₂

/-- Genuine uniform primitive recursiveness of the total integer program.
This does NOT assert its equality to the canonical optimizer. -/
theorem primrec_optimizer : Primrec optimizer :=
  primrec_foldTo (primrec_pow.comp (Primrec.const 2) primrec_edges) primrec_allCost
    (primrec_boolIte
      (primrec_safe.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.nat_min.comp (Primrec.snd.comp Primrec.snd)
        (primrec_cost.comp Primrec.fst (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd)).to₂

theorem computable_optimizer : Computable optimizer := primrec_optimizer.to_comp

/-- Exact first-order meaning of the bounded Boolean closed-word test. -/
theorem survivingClosed_eq_true (p : Input) (mask n q : ℕ) :
    survivingClosed p mask n q = true ↔ ∀ i < n,
      valid p (edgeAt p q i) = true ∧ deleted mask (edgeAt p q i) = false ∧
      target p (edgeAt p q i) = source p (edgeAt p q ((i + 1) % n)) := by
  rw [survivingClosed, allTo_eq_true]
  apply forall_congr'
  intro i
  apply forall_congr'
  intro _
  simp [Bool.and_eq_true, and_assoc]

/-- All and only closed surviving edge words of lengths 1,...,N are tested. -/
theorem safe_eq_true (p : Input) (mask : ℕ) : safe p mask = true ↔
    ∀ n : ℕ, 1 ≤ n → n ≤ vertices p → ∀ q : ℕ, q < edges p ^ n →
      survivingClosed p mask n q = true → 3 ^ n < 2 ^ wordHalvings p n q := by
  rw [safe, allTo_eq_true]
  constructor
  · intro h n hn hN q hq hc
    have hk := h (n - 1) (by omega)
    have he : n - 1 + 1 = n := by omega
    rw [he, allTo_eq_true] at hk
    have hb := hk q hq
    simpa only [hc, Bool.not_true, Bool.false_or, decide_eq_true_eq] using hb
  · intro h k hk
    rw [allTo_eq_true]
    intro q hq
    by_cases hc : survivingClosed p mask (k + 1) q = true
    · have hn := h (k + 1) (by omega) (by omega) q hq hc
      simp only [hc, Bool.not_true, Bool.false_or, decide_eq_true_eq]
      exact hn
    · have hf : survivingClosed p mask (k + 1) q = false := Bool.eq_false_iff.mpr hc
      simp only [hf, Bool.not_false, Bool.true_or]

/-- The bounded search computes the minimum of its accepted costs and fallback. -/
theorem foldTo_min_spec (n B : ℕ) (ok : ℕ → Bool) (value : ℕ → ℕ) :
    let result := foldTo n B (fun i best => if ok i then min best (value i) else best)
    result ≤ B ∧ (∀ i < n, ok i = true → result ≤ value i) ∧
      (result = B ∨ ∃ i < n, ok i = true ∧ result = value i) := by
  dsimp only
  induction n with
  | zero => simp [foldTo]
  | succ n ih =>
    rw [foldTo_succ]
    cases hn : ok n with
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      refine ⟨ih.1, ?_, ?_⟩
      · intro i hi hok
        have hil : i < n := by
          by_contra h
          have hie : i = n := by omega
          have he : false = true := hn.symm.trans (hie ▸ hok)
          cases he
        exact ih.2.1 i hil hok
      · rcases ih.2.2 with he | ⟨i,hi,hok,he⟩
        · exact Or.inl he
        · exact Or.inr ⟨i, by omega, hok, he⟩
    | true =>
      simp only [ite_true]
      refine ⟨(Nat.min_le_left _ _).trans ih.1, ?_, ?_⟩
      · intro i hi hok
        rcases lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hil | rfl
        · exact (Nat.min_le_left _ _).trans (ih.2.1 i hil hok)
        · exact Nat.min_le_right _ _
      · by_cases hb : foldTo n B (fun i best => if ok i then min best (value i) else best) ≤ value n
        · rw [Nat.min_eq_left hb]
          rcases ih.2.2 with he | ⟨i,hi,hok,he⟩
          · exact Or.inl he
          · exact Or.inr ⟨i, by omega, hok, he⟩
        · rw [Nat.min_eq_right (by omega)]
          exact Or.inr ⟨n, by omega, hn, rfl⟩

theorem optimizer_spec (p : Input) :
    optimizer p ≤ allCost p ∧
    (∀ mask < 2 ^ edges p, safe p mask = true → optimizer p ≤ cost p mask) ∧
    (optimizer p = allCost p ∨ ∃ mask < 2 ^ edges p, safe p mask = true ∧ optimizer p = cost p mask) :=
  foldTo_min_spec (2 ^ edges p) (allCost p) (safe p) (cost p)

theorem deleted_eq_testBit (mask e : ℕ) : deleted mask e = mask.testBit e :=
  Nat.testBit_eq_decide_div_mod_eq.symm

theorem deleted_all_ones (E e : ℕ) : deleted (2 ^ E - 1) e = decide (e < E) := by
  rw [deleted_eq_testBit, Nat.testBit_two_pow_sub_one]

theorem valid_bound (p : Input) (e : ℕ) (he : valid p e = true) : e < edges p :=
  of_decide_eq_true (Bool.and_eq_true_iff.mp he).1

theorem safe_all_ones (p : Input) : safe p (2 ^ edges p - 1) = true := by
  rw [safe_eq_true]
  intro n hn _ q _ hc
  have hs := (survivingClosed_eq_true p (2 ^ edges p - 1) n q).mp hc 0 (by omega)
  have he := valid_bound p (edgeAt p q 0) hs.1
  have hd : deleted (2 ^ edges p - 1) (edgeAt p q 0) = true := by
    rw [deleted_all_ones]
    exact decide_eq_true he
  have hfalse : false = true := hs.2.1.symm.trans hd
  cases hfalse

theorem cost_all_ones (p : Input) : cost p (2 ^ edges p - 1) = allCost p := by
  unfold cost allCost
  apply congrArg (sumTo (edges p))
  funext e
  cases hv : valid p e with
  | false => simp only [Bool.false_and, Bool.false_eq_true, ite_false]
  | true =>
    have he := valid_bound p e hv
    have hd : deleted (2 ^ edges p - 1) e = true := by
      rw [deleted_all_ones]
      exact decide_eq_true he
    simp only [hd, Bool.true_and, ite_true]

/-- The fallback is itself represented by an accepted bounded mask. -/
theorem optimizer_attains (p : Input) : ∃ mask < 2 ^ edges p,
    safe p mask = true ∧ optimizer p = cost p mask := by
  rcases (optimizer_spec p).2.2 with he | ⟨mask,hm,hs,he⟩
  · refine ⟨2 ^ edges p - 1, ?_, safe_all_ones p, ?_⟩
    · have hp : 0 < 2 ^ edges p := by positivity
      omega
    · rw [he, cost_all_ones]
  · exact ⟨mask,hm,hs,he⟩

/-- Decode a numeric mask into its exact canonical deletion subset. This proof
adapter is not called by the executable optimizer. -/
noncomputable def maskSubset (p : Input) (mask : ℕ) : Finset (CanonicalEdge p) := by
  classical
  exact Finset.univ.filter (fun a => deleted mask (edgeCodeEquiv p a).val.val = true)

theorem mem_maskSubset (p : Input) (mask : ℕ) (a : CanonicalEdge p) :
    a ∈ maskSubset p mask ↔ deleted mask (edgeCodeEquiv p a).val.val = true := by
  classical
  simp [maskSubset]

theorem mask_covers_subset {E : Type} [DecidableEq E] (B : ℕ)
    (c : E ↪ Fin B) (D : Finset E) :
    ∃ mask < 2 ^ B, ∀ e, deleted mask (c e).val = decide (e ∈ D) := by
  classical
  let bits : Fin B → Fin 2 := fun i => if ∃ e, e ∈ D ∧ c e = i then 1 else 0
  refine ⟨(radixEquiv 2 B (by decide) bits).val,
    (radixEquiv 2 B (by decide) bits).isLt, ?_⟩
  intro e
  change decide (digit 2 (radixEquiv 2 B (by decide) bits).val (c e).val = 1) = decide (e ∈ D)
  rw [radixEquiv_digit]
  have hm : (∃ f, f ∈ D ∧ c f = c e) ↔ e ∈ D := by
    constructor
    · rintro ⟨f,hf,he⟩
      exact c.injective he ▸ hf
    · intro he
      exact ⟨e,he,rfl⟩
  dsimp only [bits]
  simp only [hm]
  by_cases he : e ∈ D <;> simp [he]


theorem maskSubset_surjective (p : Input) (D : Finset (CanonicalEdge p)) :
    ∃ mask < 2 ^ edges p, maskSubset p mask = D := by
  classical
  let c : CanonicalEdge p ↪ Fin (edges p) := {
    toFun := fun a => (edgeCodeEquiv p a).val
    inj' := by
      intro a b he
      apply (edgeCodeEquiv p).injective
      exact Subtype.ext he }
  obtain ⟨mask,hm,hD⟩ := mask_covers_subset (edges p) c D
  refine ⟨mask,hm,?_⟩
  ext a
  rw [mem_maskSubset]
  change deleted mask (c a).val = true ↔ a ∈ D
  rw [hD]
  exact Iff.of_eq (decide_eq_true_eq (p := a ∈ D))

theorem cost_eq_deletionUnits (p : Input) (mask : ℕ) :
    cost p mask = deletionUnits (ExternalO3RateDraft.succDepth p.1) (base p) (cap p) (maskSubset p mask) := by
  classical
  let f : CanonicalEdge p → ℕ := fun a =>
    if deleted mask (edgeCodeEquiv p a).val.val then units p (edgeCodeEquiv p a).val.val else 0
  let g : Fin (edges p) → ℕ := fun c =>
    if valid p c.val && deleted mask c.val then units p c.val else 0
  let c : CanonicalEdge p → Fin (edges p) := fun a => (edgeCodeEquiv p a).val
  have hc : Function.Injective c := by
    intro a b he
    apply (edgeCodeEquiv p).injective
    exact Subtype.ext he
  have hzero : ∀ b, b ∉ Set.range c → g b = 0 := by
    intro b hb
    have hn : valid p b.val ≠ true := by
      intro hv
      let t : ValidCode p := ⟨b,hv⟩
      have he := congrArg Subtype.val ((edgeCodeEquiv p).apply_symm_apply t)
      exact hb ⟨(edgeCodeEquiv p).symm t,he⟩
    have hf : valid p b.val = false := Bool.eq_false_iff.mpr hn
    simp [g,hf]
  have heq : ∀ a, f a = g (c a) := by
    intro a
    have hv := (edgeCodeEquiv p a).property
    simp only [f,g,c,hv,Bool.true_and]
  unfold cost
  rw [sumTo_eq_fin_sum]
  calc
    _ = ∑ a : CanonicalEdge p, f a :=
      (Fintype.sum_of_injective c hc f g hzero heq).symm
    _ = _ := by
      unfold deletionUnits maskSubset
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a _
      by_cases hd : deleted mask (edgeCodeEquiv p a).val.val = true
      · simp only [f,hd,ite_true]
        exact edgeCodeEquiv_units p a
      · simp [f,hd]

end ExternalO3OptimizationAlgorithm
