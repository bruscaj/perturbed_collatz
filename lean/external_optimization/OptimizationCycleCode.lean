import OptimizationAlgorithm
import OptimizationEdgeCode

/-! Transport between labelled finite graph cycles and the executable radix
word tests. All cycles and tested words have strictly positive length. -/
noncomputable section
namespace ExternalO3OptimizationCycleCode

open ExternalO3OptimizationCode ExternalO3OptimizationDraft
open ExternalO3OptimizationVertexCode ExternalO3OptimizationEdgeCode
open ExternalO3OptimizationAlgorithm
open scoped BigOperators

abbrev CGraph (p : Input) :=
  truncatedGraph (ExternalO3RateDraft.succDepth p.1) (base p) (cap p)

abbrev CWalk (p : Input) :=
  WalkData (Vertex (ExternalO3RateDraft.succDepth p.1) (base p)) (CanonicalEdge p)

theorem edges_pos (p : Input) : 0 < edges p := by
  exact Nat.mul_pos (by unfold cap; omega) (vertices_pos p)

def cycleWord (p : Input) (c : CWalk p) : Fin (edges p ^ c.length) :=
  radixEquiv (edges p) c.length (edges_pos p)
    (fun i => (edgeCodeEquiv p (c.edge i)).val)

theorem cycleWord_at (p : Input) (c : CWalk p) (i : Fin c.length) :
    edgeAt p (cycleWord p c).val i.val = encodeNat p (c.edge i) := by
  exact radixEquiv_digit (edges p) c.length (edges_pos p)
    (fun j => (edgeCodeEquiv p (c.edge j)).val) i

theorem cycleWord_halvings (p : Input) (c : CWalk p) :
    wordHalvings p c.length (cycleWord p c).val =
      ∑ i, halvingExponent (ExternalO3RateDraft.succDepth p.1) (base p) (cap p) (c.edge i) := by
  rw [wordHalvings, sumTo_eq_fin_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [cycleWord_at, halvings_encodeNat]

theorem cycle_next_source {V E : Type} (g : FiniteGraph V E)
    (c : WalkData V E) (hc : IsCycle g c) (i : Fin c.length) :
    g.target (c.edge i) = g.source (c.edge ⟨(i.val+1)%c.length, Nat.mod_lt _ hc.1⟩) := by
  rw [hc.2.1 i |>.2, hc.2.1 _ |>.1]
  by_cases hi : i.val+1 < c.length
  · apply congrArg c.vertex
    apply Fin.ext
    exact (Nat.mod_eq_of_lt hi).symm
  · have he : i.val+1 = c.length := by omega
    calc
      c.vertex i.succ = c.vertex (Fin.last c.length) := congrArg c.vertex (Fin.ext he)
      _ = c.vertex 0 := hc.2.2
      _ = c.vertex (⟨(i.val+1)%c.length, Nat.mod_lt _ hc.1⟩ : Fin c.length).castSucc := by
        apply congrArg c.vertex
        apply Fin.ext
        simp [he]

def wordEdge (p : Input) (mask n q : ℕ) (hc : survivingClosed p mask n q = true)
    (i : Fin n) : CanonicalEdge p :=
  (edgeCodeEquiv p).symm ⟨⟨edgeAt p q i.val,
    valid_bound p _ ((survivingClosed_eq_true p mask n q).mp hc i.val i.isLt).1⟩,
    ((survivingClosed_eq_true p mask n q).mp hc i.val i.isLt).1⟩

theorem wordEdge_code (p : Input) (mask n q : ℕ) (hc : survivingClosed p mask n q = true)
    (i : Fin n) : encodeNat p (wordEdge p mask n q hc i) = edgeAt p q i.val := by
  exact congrArg (fun c : ValidCode p => c.val.val) ((edgeCodeEquiv p).apply_symm_apply _)

def wordWalk (p : Input) (mask n q : ℕ) (hn : 0 < n)
    (hc : survivingClosed p mask n q = true) : CWalk p where
  length := n
  edge := wordEdge p mask n q hc
  vertex := fun i => edgeSource (ExternalO3RateDraft.succDepth p.1) (base p) (cap p)
    (wordEdge p mask n q hc ⟨i.val%n,Nat.mod_lt _ hn⟩)

theorem wordWalk_cycle (p : Input) (mask n q : ℕ) (hn : 0 < n)
    (hc : survivingClosed p mask n q = true) : IsCycle (CGraph p) (wordWalk p mask n q hn hc) := by
  refine ⟨hn, ?_, ?_⟩
  · intro i
    constructor
    · change _ = edgeSource _ _ _ (wordEdge p mask n q hc ⟨i.val%n,_⟩)
      have hi : (⟨i.val%n,Nat.mod_lt _ hn⟩ : Fin n) = i :=
        Fin.ext (Nat.mod_eq_of_lt i.isLt)
      rw [hi]
      rfl
    · change edgeTarget _ _ _ (wordEdge p mask n q hc i) =
        edgeSource _ _ _ (wordEdge p mask n q hc ⟨(i.val+1)%n,_⟩)
      apply (vertexCodeEquiv p).injective
      apply Fin.ext
      rw [← target_encodeNat, ← source_encodeNat]
      erw [wordEdge_code, wordEdge_code]
      exact ((survivingClosed_eq_true p mask n q).mp hc i.val i.isLt).2.2
  · change edgeSource _ _ _ (wordEdge p mask n q hc ⟨n%n,_⟩) =
      edgeSource _ _ _ (wordEdge p mask n q hc ⟨0%n,_⟩)
    apply congrArg
    congr 1
    apply Fin.ext
    simp

theorem wordWalk_halvings (p : Input) (mask n q : ℕ) (hn : 0 < n)
    (hc : survivingClosed p mask n q = true) :
    (∑ i, halvingExponent (ExternalO3RateDraft.succDepth p.1) (base p) (cap p)
      ((wordWalk p mask n q hn hc).edge i)) = wordHalvings p n q := by
  rw [wordHalvings, sumTo_eq_fin_sum]
  apply Finset.sum_congr rfl
  intro i _
  change halvingExponent _ _ _ (wordEdge p mask n q hc i) = halvings p (edgeAt p q i.val)
  rw [← wordEdge_code p mask n q hc i, halvings_encodeNat]

theorem cycleWord_surviving (p : Input) (mask : ℕ) (c : CWalk p)
    (hc : IsCycle (CGraph p) c) (hk : ∀ i, c.edge i ∉ maskSubset p mask) :
    survivingClosed p mask c.length (cycleWord p c).val = true := by
  rw [survivingClosed_eq_true]
  intro i hi
  let j : Fin c.length := ⟨i,hi⟩
  have hcur := cycleWord_at p c j
  change edgeAt p (cycleWord p c).val i = encodeNat p (c.edge j) at hcur
  rw [hcur]
  refine ⟨encodeNat_valid p _, ?_, ?_⟩
  · apply Bool.eq_false_iff.mpr
    intro hd
    exact hk j ((mem_maskSubset p mask (c.edge j)).mpr hd)
  · have hnext := cycleWord_at p c ⟨(i+1)%c.length,Nat.mod_lt _ hc.1⟩
    rw [hnext, target_encodeNat, source_encodeNat]
    exact congrArg (fun v => (vertexCodeEquiv p v).val) (cycle_next_source (CGraph p) c hc j)

theorem wordWalk_kept (p : Input) (mask n q : ℕ) (hn : 0 < n)
    (hc : survivingClosed p mask n q = true) :
    ∀ i, (wordWalk p mask n q hn hc).edge i ∉ maskSubset p mask := by
  intro i hi
  have hd := (mem_maskSubset p mask _).mp hi
  change deleted mask (encodeNat p (wordEdge p mask n q hc i)) = true at hd
  erw [wordEdge_code] at hd
  have hf := ((survivingClosed_eq_true p mask n q).mp hc i.val i.isLt).2.1
  rw [hf] at hd
  exact Bool.false_ne_true hd

/-- Exactly the canonical strictly-negative-cycle condition, for every mask. -/
theorem safe_iff_cycle_safe (p : Input) (mask : ℕ) :
    safe p mask = true ↔ CycleSafe (CGraph p) (maskSubset p mask) := by
  constructor
  · intro hs
    apply ExternalO3OptimizationPaths.elementary_cycle_safety_implies_cycle_safe
    intro c hc hel hk
    have hlen : c.length ≤ vertices p := by
      have hh := ExternalO3OptimizationCycles.elementary_length_le_card c hel
      change c.length ≤ Fintype.card (Fin (depth p) → Fin (base p)) at hh
      simpa only [Fintype.card_fun, Fintype.card_fin, vertices] using hh
    have hpow := (safe_eq_true p mask).mp hs c.length (by have := hc.1; omega)
      hlen (cycleWord p c).val (cycleWord p c).isLt (cycleWord_surviving p mask c hc hk)
    rw [cycleWord_halvings] at hpow
    exact ((ExternalO3OptimizationArithmetic.natural_cycle_signs
      (ExternalO3RateDraft.succDepth p.1) (base p) (cap p)
      (by unfold base; omega) (by unfold cap; omega) c hc).2.2.1).mpr hpow
  · intro hs
    rw [safe_eq_true]
    intro n hn _hnN q _hq hc
    have hn0 : 0 < n := by omega
    have hcycle := wordWalk_cycle p mask n q hn0 hc
    have hneg := hs (wordWalk p mask n q hn0 hc) hcycle (wordWalk_kept p mask n q hn0 hc)
    have hpow := ((ExternalO3OptimizationArithmetic.natural_cycle_signs
      (ExternalO3RateDraft.succDepth p.1) (base p) (cap p)
      (by unfold base; omega) (by unfold cap; omega) _ hcycle).2.2.1).mp hneg
    rwa [wordWalk_halvings] at hpow

end ExternalO3OptimizationCycleCode
