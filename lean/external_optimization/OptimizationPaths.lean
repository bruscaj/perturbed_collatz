import OptimizationCycles
import Mathlib.Data.Fintype.List

/-! Work toward strict finite-graph feasibility. All path data retain literal
edge identities. No challenge module or unproved feasibility premise is used. -/
namespace ExternalO3OptimizationPaths
open ExternalO3OptimizationDraft
open scoped BigOperators

def KeptPath {V E : Type} (g : FiniteGraph V E) (D : Finset E) : V → List E → Prop
  | _, [] => True
  | u, e :: l => g.source e = u ∧ e ∉ D ∧ KeptPath g D (g.target e) l

def pathEnd {V E : Type} (g : FiniteGraph V E) : V → List E → V
  | u, [] => u
  | _, e :: l => pathEnd g (g.target e) l

def pathVertex {V E : Type} (g : FiniteGraph V E) : V → List E → ℕ → V
  | u, _, 0 => u
  | u, [], _ + 1 => u
  | _, e :: l, n + 1 => pathVertex g (g.target e) l n

def pathGain {V E : Type} (g : FiniteGraph V E) (l : List E) : ℝ :=
  (l.map g.baseGain).sum

def pathVertices {V E : Type} (g : FiniteGraph V E) (u : V) (l : List E) : List V :=
  u :: l.map g.target

theorem keptPath_append {V E : Type} (g : FiniteGraph V E) (D : Finset E)
    (u : V) (l m : List E) :
    KeptPath g D u (l ++ m) ↔ KeptPath g D u l ∧ KeptPath g D (pathEnd g u l) m := by
  induction l generalizing u with
  | nil => simp [KeptPath, pathEnd]
  | cons e l ih => simp [KeptPath, pathEnd, ih, and_assoc]

theorem pathEnd_append {V E : Type} (g : FiniteGraph V E) (u : V) (l m : List E) :
    pathEnd g u (l ++ m) = pathEnd g (pathEnd g u l) m := by
  induction l generalizing u with
  | nil => rfl
  | cons e l ih => exact ih (g.target e)

theorem pathGain_append {V E : Type} (g : FiniteGraph V E) (l m : List E) :
    pathGain g (l ++ m) = pathGain g l + pathGain g m := by
  simp [pathGain]

theorem pathVertex_end {V E : Type} (g : FiniteGraph V E) (u : V) (l : List E) :
    pathVertex g u l l.length = pathEnd g u l := by
  induction l generalizing u with
  | nil => rfl
  | cons e l ih => exact ih (g.target e)

theorem path_source_get {V E : Type} (g : FiniteGraph V E) (D : Finset E)
    (u : V) (l : List E) (hl : KeptPath g D u l) (i : Fin l.length) :
    g.source (l.get i) = pathVertex g u l i.val := by
  induction l generalizing u with
  | nil => exact Fin.elim0 i
  | cons e l ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa [pathVertex] using hl.1
      · simpa [pathVertex] using ih (g.target e) hl.2.2 j

theorem path_target_get {V E : Type} (g : FiniteGraph V E)
    (u : V) (l : List E) (i : Fin l.length) :
    g.target (l.get i) = pathVertex g u l (i.val + 1) := by
  induction l generalizing u with
  | nil => exact Fin.elim0 i
  | cons e l ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [pathVertex]
      · simpa [pathVertex] using ih (g.target e) j

theorem keptPath_get_notMem {V E : Type} (g : FiniteGraph V E) (D : Finset E)
    (u : V) (l : List E) (hl : KeptPath g D u l) (i : Fin l.length) : l.get i ∉ D := by
  induction l generalizing u with
  | nil => exact Fin.elim0 i
  | cons e l ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hl.2.1
      · simpa using ih (g.target e) hl.2.2 j

def listWalk {V E : Type} (g : FiniteGraph V E) (u : V) (l : List E) : WalkData V E where
  length := l.length
  vertex i := pathVertex g u l i.val
  edge := l.get

theorem listWalk_cycle {V E : Type} (g : FiniteGraph V E) (D : Finset E)
    (u : V) (l : List E) (hl : KeptPath g D u l) (hne : l ≠ [])
    (hend : pathEnd g u l = u) : IsCycle g (listWalk g u l) := by
  refine ⟨List.length_pos_iff.mpr hne, ?_, ?_⟩
  · intro i
    exact ⟨path_source_get g D u l hl i, path_target_get g u l i⟩
  · change pathVertex g u l l.length = pathVertex g u l 0
    rw [pathVertex_end, hend]
    simp [pathVertex]

theorem listWalk_gain {V E : Type} (g : FiniteGraph V E) (u : V) (l : List E) :
    cycleGain g (listWalk g u l) = pathGain g l := by
  change (∑ i : Fin l.length, g.baseGain (l.get i)) = (l.map g.baseGain).sum
  induction l with
  | nil => simp
  | cons e l _ => simp [Fin.sum_univ_succ]

theorem closed_kept_gain_neg {V E : Type} (g : FiniteGraph V E) (D : Finset E)
    (hsafe : CycleSafe g D) (u : V) (l : List E) (hl : KeptPath g D u l)
    (hne : l ≠ []) (hend : pathEnd g u l = u) : pathGain g l < 0 := by
  have hc := listWalk_cycle g D u l hl hne hend
  have hh := hsafe (listWalk g u l) hc (keptPath_get_notMem g D u l hl)
  rwa [listWalk_gain] at hh

theorem simple_path_dominates {V E : Type} (g : FiniteGraph V E) (D : Finset E)
    (hsafe : CycleSafe g D) (u : V) (l : List E) (hl : KeptPath g D u l) :
    ∃ p : List E, KeptPath g D u p ∧ pathEnd g u p = pathEnd g u l ∧
      p.Sublist l ∧ (pathVertices g u p).Nodup ∧ pathGain g l ≤ pathGain g p := by
  classical
  induction hn : l.length using Nat.strong_induction_on generalizing u l with
  | h n ih =>
    by_cases hreturn : u ∈ l.map g.target
    · obtain ⟨e, he, htarget⟩ := List.mem_map.mp hreturn
      obtain ⟨a, b, hab⟩ := List.mem_iff_append.mp he
      have hsplit : l = (a ++ [e]) ++ b := by simpa only [List.append_assoc, List.singleton_append] using hab
      have hp := (keptPath_append g D u (a ++ [e]) b).mp (hsplit ▸ hl)
      have hend : pathEnd g u (a ++ [e]) = u := by
        simp [pathEnd_append, pathEnd, htarget]
      have hb : KeptPath g D u b := hend ▸ hp.2
      have hlen : b.length < n := by rw [hab] at hn; simp only [List.length_append, List.length_cons] at hn; omega
      obtain ⟨p, hvalid, hpend, hsub, hnodup, hgain⟩ := ih b.length hlen u b hb rfl
      have hnegative : pathGain g (a ++ [e]) < 0 :=
        closed_kept_gain_neg g D hsafe u _ hp.1 (by simp) hend
      refine ⟨p, hvalid, ?_, ?_, hnodup, ?_⟩
      · rw [hsplit, pathEnd_append, hend]
        exact hpend
      · rw [hab]
        exact (hsub.trans (List.sublist_cons_self e b)).trans (List.sublist_append_right a (e :: b))
      · rw [hsplit, pathGain_append]
        linarith
    · cases l with
      | nil => exact ⟨[], hl, rfl, List.Sublist.refl _, by simp [pathVertices], le_rfl⟩
      | cons e l =>
        have hlen : l.length < n := by simp only [List.length_cons] at hn; omega
        obtain ⟨p, hvalid, hpend, hsub, hnodup, hgain⟩ :=
          ih l.length hlen (g.target e) l hl.2.2 rfl
        have hnot : u ∉ pathVertices g (g.target e) p := by
          intro hm
          rcases List.mem_cons.mp hm with heq | hmem
          · apply hreturn
            simp only [List.map_cons, List.mem_cons]
            exact Or.inl heq
          · apply hreturn
            exact List.mem_cons_of_mem _ ((hsub.map g.target).subset hmem)
        refine ⟨e :: p, ⟨hl.1, hl.2.1, hvalid⟩, hpend,
          hsub.cons_cons e, ?_, ?_⟩
        · exact List.nodup_cons.mpr ⟨hnot, hnodup⟩
        · change g.baseGain e + pathGain g l ≤ g.baseGain e + pathGain g p
          linarith

theorem exists_max_simple_path {V E : Type} [Fintype E] (g : FiniteGraph V E)
    (D : Finset E) (u : V) :
    ∃ p : List E, KeptPath g D u p ∧ (pathVertices g u p).Nodup ∧
      ∀ q : List E, KeptPath g D u q → (pathVertices g u q).Nodup → pathGain g q ≤ pathGain g p := by
  classical
  let S := {l : List E // KeptPath g D u l ∧ (pathVertices g u l).Nodup}
  have : Finite S := by
    apply Finite.of_injective
      (fun p : S => (⟨p.val, List.Nodup.of_map g.target (List.nodup_cons.mp p.property.2).2⟩ :
        {l : List E // l.Nodup}))
    intro a b hab
    exact Subtype.ext (congrArg (fun z : {l : List E // l.Nodup} => z.val) hab)
  let : Fintype S := Fintype.ofFinite S
  have hnonempty : (Finset.univ : Finset S).Nonempty :=
    ⟨⟨[], by simp [KeptPath, pathVertices]⟩, Finset.mem_univ _⟩
  obtain ⟨p, _, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset S)
    (fun p => pathGain g p.val) hnonempty
  exact ⟨p.val, p.property.1, p.property.2,
    fun q hq hn => hmax ⟨q, hq, hn⟩ (Finset.mem_univ _)⟩

noncomputable def pathPotential {V E : Type} [Fintype E] (g : FiniteGraph V E)
    (D : Finset E) (u : V) : ℝ :=
  pathGain g (Classical.choose (exists_max_simple_path g D u))

theorem pathPotential_witness {V E : Type} [Fintype E] (g : FiniteGraph V E)
    (D : Finset E) (u : V) : ∃ p, KeptPath g D u p ∧ pathGain g p = pathPotential g D u := by
  exact ⟨_, (Classical.choose_spec (exists_max_simple_path g D u)).1, rfl⟩

theorem path_gain_le_potential {V E : Type} [Fintype E] (g : FiniteGraph V E)
    (D : Finset E) (hsafe : CycleSafe g D) (u : V) (l : List E) (hl : KeptPath g D u l) :
    pathGain g l ≤ pathPotential g D u := by
  obtain ⟨p, hp, _, _, hn, hgain⟩ := simple_path_dominates g D hsafe u l hl
  exact hgain.trans ((Classical.choose_spec (exists_max_simple_path g D u)).2.2 p hp hn)

theorem nonstrict_path_potential {V E : Type} [Fintype E] (g : FiniteGraph V E)
    (D : Finset E) (hsafe : CycleSafe g D) (e : E) (he : e ∉ D) :
    edgeGain g (pathPotential g D) e ≤ 0 := by
  obtain ⟨p, hp, hgain⟩ := pathPotential_witness g D (g.target e)
  have hh := path_gain_le_potential g D hsafe (g.source e) (e :: p) ⟨rfl, he, hp⟩
  change g.baseGain e + pathGain g p ≤ pathPotential g D (g.source e) at hh
  rw [hgain] at hh
  unfold edgeGain
  linarith

noncomputable def tightDeleted {V E : Type} [Fintype E] (g : FiniteGraph V E)
    (D : Finset E) (ψ : V → ℝ) : Finset E := by
  classical
  exact Finset.univ.filter (fun e => e ∈ D ∨ edgeGain g ψ e ≠ 0)

def unitGraph {V E : Type} (g : FiniteGraph V E) : FiniteGraph V E :=
  { g with baseGain := fun _ => 1 }

theorem tight_unit_cycle_safe {V E : Type} [Fintype E] (g : FiniteGraph V E)
    (D : Finset E) (ψ : V → ℝ) (hsafe : CycleSafe g D) :
    CycleSafe (unitGraph g) (tightDeleted g D ψ) := by
  classical
  intro c hc hkept
  have hc' : IsCycle g c := hc
  have hnot (i : Fin c.length) : ¬ (c.edge i ∈ D ∨ edgeGain g ψ (c.edge i) ≠ 0) := by
    simpa [tightDeleted] using hkept i
  have hk : ∀ i, c.edge i ∉ D := fun i hi => hnot i (Or.inl hi)
  have hz : ∀ i, edgeGain g ψ (c.edge i) = 0 := by
    intro i
    by_contra hn
    exact hnot i (Or.inr hn)
  have hsum : (∑ i, edgeGain g ψ (c.edge i)) = 0 := Finset.sum_eq_zero (fun i _ => hz i)
  rw [ExternalO3OptimizationCycles.cycle_correction_telescope g ψ c hc'] at hsum
  have hneg := hsafe c hc' hk
  exact False.elim ((ne_of_lt hneg) hsum)

theorem small_scale_for_strict_or_tight (x y : ℝ) (h : x < 0 ∨ x = 0 ∧ y < 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ δ → x + ε * y < 0 := by
  rcases h with hx | ⟨hx, hy⟩
  · have hden : 0 < |y| + 1 := by positivity
    refine ⟨-x / (|y| + 1), div_pos (by linarith) hden, ?_⟩
    intro ε hε hbound
    have hb := (le_div_iff₀ hden).mp hbound
    have hy : y < |y| + 1 := by linarith [le_abs_self y]
    have hh := mul_lt_mul_of_pos_left hy hε
    linarith
  · refine ⟨1, by norm_num, ?_⟩
    intro ε hε _
    rw [hx, zero_add]
    exact mul_neg_of_pos_of_neg hε hy

theorem finite_small_scale {E : Type} (s : Finset E) (x y : E → ℝ)
    (h : ∀ e ∈ s, x e < 0 ∨ x e = 0 ∧ y e < 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ e ∈ s, ∀ ε : ℝ, 0 < ε → ε ≤ δ → x e + ε * y e < 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert e s _ ih =>
      obtain ⟨δs, hδs, hs⟩ := ih (fun f hf => h f (Finset.mem_insert_of_mem hf))
      obtain ⟨δe, hδe, he⟩ := small_scale_for_strict_or_tight (x e) (y e)
        (h e (Finset.mem_insert_self _ _))
      refine ⟨min δs δe, lt_min hδs hδe, ?_⟩
      intro f hf ε hε hbound
      rcases Finset.mem_insert.mp hf with rfl | hf
      · exact he ε hε (hbound.trans (min_le_right _ _))
      · exact hs f hf ε hε (hbound.trans (min_le_left _ _))

theorem cycle_safe_implies_strict_feasible {V E : Type} [Fintype E]
    (g : FiniteGraph V E) (D : Finset E) (hsafe : CycleSafe g D) : StrictFeasible g D := by
  classical
  let ψ := pathPotential g D
  let ρ := pathPotential (unitGraph g) (tightDeleted g D ψ)
  let x := edgeGain g ψ
  let y := fun e => ρ (g.target e) - ρ (g.source e)
  have hxy : ∀ e ∈ Finset.univ.filter (fun e => e ∉ D), x e < 0 ∨ x e = 0 ∧ y e < 0 := by
    intro e he
    have heD : e ∉ D := (Finset.mem_filter.mp he).2
    have hx : x e ≤ 0 := nonstrict_path_potential g D hsafe e heD
    rcases lt_or_eq_of_le hx with hx | hx
    · exact Or.inl hx
    · refine Or.inr ⟨hx, ?_⟩
      have hz : edgeGain g ψ e = 0 := hx
      have hetight : e ∉ tightDeleted g D ψ := by simp [tightDeleted, heD, hz]
      have hy := nonstrict_path_potential (unitGraph g) (tightDeleted g D ψ)
        (tight_unit_cycle_safe g D ψ hsafe) e hetight
      change 1 + ρ (g.target e) - ρ (g.source e) ≤ 0 at hy
      dsimp [y]
      linarith
  obtain ⟨ε, hε, hsmall⟩ := finite_small_scale (Finset.univ.filter (fun e => e ∉ D)) x y hxy
  refine ⟨fun u => ψ u + ε * ρ u, ?_⟩
  intro e he
  have hh := hsmall e (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩) ε hε le_rfl
  change x e + ε * y e < 0 at hh
  dsimp [x, y, edgeGain] at hh ⊢
  nlinarith

theorem generic_strict_cycle_criterion : GenericStrictCycleCriterion := by
  intro V E _ _ g D
  exact ⟨⟨ExternalO3OptimizationCycles.strict_feasible_implies_cycle_safe g D,
    cycle_safe_implies_strict_feasible g D⟩,
    ExternalO3OptimizationCycles.cycle_safe_iff_hits_nonnegative g D⟩

theorem bounded_simple_path_dominates {V E : Type} (g : FiniteGraph V E) (D : Finset E)
    (N : ℕ)
    (hclosed : ∀ u l, KeptPath g D u l → l ≠ [] → pathEnd g u l = u → l.length ≤ N → pathGain g l < 0)
    (u : V) (l : List E) (hl : KeptPath g D u l) (hN : l.length ≤ N) :
    ∃ p : List E, KeptPath g D u p ∧ pathEnd g u p = pathEnd g u l ∧
      p.Sublist l ∧ (pathVertices g u p).Nodup ∧ pathGain g l ≤ pathGain g p := by
  classical
  induction hn : l.length using Nat.strong_induction_on generalizing u l with
  | h n ih =>
    by_cases hreturn : u ∈ l.map g.target
    · obtain ⟨e, he, htarget⟩ := List.mem_map.mp hreturn
      obtain ⟨a, b, hab⟩ := List.mem_iff_append.mp he
      have hsplit : l = (a ++ [e]) ++ b := by simpa only [List.append_assoc, List.singleton_append] using hab
      have hp := (keptPath_append g D u (a ++ [e]) b).mp (hsplit ▸ hl)
      have hend : pathEnd g u (a ++ [e]) = u := by
        simp [pathEnd_append, pathEnd, htarget]
      have hb : KeptPath g D u b := hend ▸ hp.2
      have hlen : b.length < n := by rw [hab] at hn; simp only [List.length_append, List.length_cons] at hn; omega
      obtain ⟨p, hvalid, hpend, hsub, hnodup, hgain⟩ := ih b.length hlen u b hb (by omega) rfl
      have hnegative : pathGain g (a ++ [e]) < 0 :=
        hclosed u _ hp.1 (by simp) hend (by rw [hsplit] at hN; simp only [List.length_append, List.length_singleton] at hN ⊢; omega)
      refine ⟨p, hvalid, ?_, ?_, hnodup, ?_⟩
      · rw [hsplit, pathEnd_append, hend]
        exact hpend
      · rw [hab]
        exact (hsub.trans (List.sublist_cons_self e b)).trans (List.sublist_append_right a (e :: b))
      · rw [hsplit, pathGain_append]
        linarith
    · cases l with
      | nil => exact ⟨[], hl, rfl, List.Sublist.refl _, by simp [pathVertices], le_rfl⟩
      | cons e l =>
        have hlen : l.length < n := by simp only [List.length_cons] at hn; omega
        obtain ⟨p, hvalid, hpend, hsub, hnodup, hgain⟩ :=
          ih l.length hlen (g.target e) l hl.2.2 (by omega) rfl
        have hnot : u ∉ pathVertices g (g.target e) p := by
          intro hm
          rcases List.mem_cons.mp hm with heq | hmem
          · apply hreturn
            simp only [List.map_cons, List.mem_cons]
            exact Or.inl heq
          · apply hreturn
            exact List.mem_cons_of_mem _ ((hsub.map g.target).subset hmem)
        refine ⟨e :: p, ⟨hl.1, hl.2.1, hvalid⟩, hpend,
          hsub.cons_cons e, ?_, ?_⟩
        · exact List.nodup_cons.mpr ⟨hnot, hnodup⟩
        · change g.baseGain e + pathGain g l ≤ g.baseGain e + pathGain g p
          linarith


theorem pathVertices_get {V E : Type} (g : FiniteGraph V E) (u : V) (l : List E)
    (i : Fin (l.length + 1)) :
    (pathVertices g u l).get ⟨i.val, by simp [pathVertices]; omega⟩ = pathVertex g u l i.val := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [pathVertices, pathVertex]
  · simpa [pathVertices] using path_target_get g u l j

theorem simple_vertices_injective {V E : Type} (g : FiniteGraph V E) (u : V) (l : List E)
    (hn : (pathVertices g u l).Nodup) :
    Function.Injective (fun i : Fin (l.length + 1) => pathVertex g u l i.val) := by
  intro i j hij
  have hi := pathVertices_get g u l i
  have hj := pathVertices_get g u l j
  have heq := hn.injective_get (hi.trans (hij.trans hj.symm))
  exact Fin.ext (congrArg (fun z : Fin (pathVertices g u l).length => z.val) heq)

theorem closed_with_simple_tail_elementary {V E : Type} (g : FiniteGraph V E)
    (u : V) (e : E) (p : List E) (hn : (pathVertices g (g.target e) p).Nodup)
    (hend : pathEnd g (g.target e) p = u) : IsElementary (listWalk g u (e :: p)) := by
  have hinj := simple_vertices_injective g (g.target e) p hn
  change Function.Injective (fun i : Fin (p.length + 1) => pathVertex g u (e :: p) i.val)
  have heq (k : Fin p.length) : pathVertex g (g.target e) p k.val ≠ u := by
    intro hk
    have hlast : pathVertex g (g.target e) p (Fin.last p.length).val = u := by
      rw [Fin.val_last, pathVertex_end, hend]
    have hidx := hinj (show pathVertex g (g.target e) p k.castSucc.val =
      pathVertex g (g.target e) p (Fin.last p.length).val from hk.trans hlast.symm)
    have hv := congrArg Fin.val hidx
    simp only [Fin.val_castSucc, Fin.val_last] at hv
    omega
  intro i
  refine Fin.cases ?_ (fun a => ?_) i
  · intro j
    refine Fin.cases ?_ (fun b => ?_) j
    · intro _; rfl
    · intro hij; exact False.elim (heq b (by simpa [pathVertex] using hij.symm))
  · intro j
    refine Fin.cases ?_ (fun b => ?_) j
    · intro hij; exact False.elim (heq a (by simpa [pathVertex] using hij))
    · intro hij
      apply Fin.ext
      have ht : pathVertex g (g.target e) p a.castSucc.val =
          pathVertex g (g.target e) p b.castSucc.val := by simpa [pathVertex] using hij
      have hv := congrArg Fin.val (hinj ht)
      simp only [Fin.val_castSucc] at hv
      simp only [Fin.val_succ]
      omega

theorem keptPath_of_source_get {V E : Type} (g : FiniteGraph V E) (D : Finset E)
    (u : V) (l : List E)
    (hs : ∀ i : Fin l.length, g.source (l.get i) = pathVertex g u l i.val)
    (hk : ∀ i : Fin l.length, l.get i ∉ D) : KeptPath g D u l := by
  induction l generalizing u with
  | nil => trivial
  | cons e l ih =>
      refine ⟨?_, ?_, ?_⟩
      · simpa [pathVertex] using hs 0
      · simpa using hk 0
      · apply ih (g.target e)
        · intro j
          simpa [pathVertex] using hs j.succ
        · intro j
          simpa using hk j.succ

theorem ofFn_pathVertex {V E : Type} (g : FiniteGraph V E) (c : WalkData V E)
    (hc : IsCycle g c) (i : Fin (c.length + 1)) :
    pathVertex g (c.vertex 0) (List.ofFn c.edge) i.val = c.vertex i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [pathVertex]
  · have ht := path_target_get g (c.vertex 0) (List.ofFn c.edge)
      ⟨j.val, by simp⟩
    have he : g.target ((List.ofFn c.edge).get ⟨j.val, by simp⟩) = c.vertex j.succ := by
      simpa using (hc.2.1 j).2
    exact ht.symm.trans he

theorem cycle_as_edgeList {V E : Type} (g : FiniteGraph V E) (D : Finset E)
    (c : WalkData V E) (hc : IsCycle g c) (hk : ∀ i, c.edge i ∉ D) :
    KeptPath g D (c.vertex 0) (List.ofFn c.edge) ∧
    pathEnd g (c.vertex 0) (List.ofFn c.edge) = c.vertex 0 ∧
    pathGain g (List.ofFn c.edge) = cycleGain g c := by
  refine ⟨?_, ?_, ?_⟩
  · apply keptPath_of_source_get
    · intro i
      let j : Fin c.length := ⟨i.val, by simpa using i.isLt⟩
      simpa [j] using (hc.2.1 j).1.trans (ofFn_pathVertex g c hc j.castSucc).symm
    · intro i
      simpa using hk ⟨i.val, by simpa using i.isLt⟩
  · rw [← pathVertex_end]
    simpa using (ofFn_pathVertex g c hc (Fin.last c.length)).trans hc.2.2
  · simp [pathGain, List.map_ofFn, Fin.sum_ofFn, cycleGain]

theorem closed_gain_negative_of_elementary {V E : Type} (g : FiniteGraph V E)
    (D : Finset E)
    (helem : ∀ c : WalkData V E, IsCycle g c → IsElementary c →
      (∀ i, c.edge i ∉ D) → cycleGain g c < 0)
    (u : V) (l : List E) (hl : KeptPath g D u l) (hne : l ≠ [])
    (hend : pathEnd g u l = u) : pathGain g l < 0 := by
  classical
  induction hn : l.length using Nat.strong_induction_on generalizing u l with
  | h n ih =>
    cases l with
    | nil => exact False.elim (hne rfl)
    | cons e l =>
      have hshort : ∀ v q, KeptPath g D v q → q ≠ [] → pathEnd g v q = v →
          q.length ≤ l.length → pathGain g q < 0 := by
        intro v q hq hqne hqend hqbound
        apply ih q.length (by simp only [List.length_cons] at hn; omega) v q hq hqne hqend rfl
      obtain ⟨p, hp, hpEnd, _, hpNodup, hgain⟩ :=
        bounded_simple_path_dominates g D l.length hshort (g.target e) l hl.2.2 le_rfl
      have hpEndU : pathEnd g (g.target e) p = u := hpEnd.trans hend
      have hvalid : KeptPath g D u (e :: p) := ⟨hl.1, hl.2.1, hp⟩
      have hc := listWalk_cycle g D u (e :: p) hvalid (by simp) hpEndU
      have hElementary := closed_with_simple_tail_elementary g u e p hpNodup hpEndU
      have hnegative := helem (listWalk g u (e :: p)) hc hElementary
        (keptPath_get_notMem g D u (e :: p) hvalid)
      rw [listWalk_gain] at hnegative
      change g.baseGain e + pathGain g p < 0 at hnegative
      change g.baseGain e + pathGain g l < 0
      linarith

theorem elementary_cycle_safety_implies_cycle_safe {V E : Type} (g : FiniteGraph V E)
    (D : Finset E)
    (helem : ∀ c : WalkData V E, IsCycle g c → IsElementary c →
      (∀ i, c.edge i ∉ D) → cycleGain g c < 0) : CycleSafe g D := by
  intro c hc hk
  obtain ⟨hl, hend, hgain⟩ := cycle_as_edgeList g D c hc hk
  have hne : List.ofFn c.edge ≠ [] := by
    intro h
    have hh := congrArg List.length h
    simp only [List.length_ofFn, List.length_nil] at hh
    have hpos := hc.1
    omega
  have hh := closed_gain_negative_of_elementary g D helem (c.vertex 0) (List.ofFn c.edge) hl hne hend
  rwa [hgain] at hh

theorem generic_elementary_reduction : GenericElementaryReduction := by
  intro V E _ _ g D
  constructor
  · constructor
    · intro hsafe c hc _ hk
      exact hsafe c hc hk
    · exact elementary_cycle_safety_implies_cycle_safe g D
  · intro c _ hc
    exact ExternalO3OptimizationCycles.elementary_length_le_card c hc

end ExternalO3OptimizationPaths
