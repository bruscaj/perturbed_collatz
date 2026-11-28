import OptimizationExpectedTypes

/-! Necessary cycle foundations only. Strict sufficiency and elementary-cycle
decomposition are not established by this module. -/
namespace ExternalO3OptimizationCycles
open ExternalO3OptimizationDraft
open scoped BigOperators

theorem cycle_correction_telescope {V E : Type} (g : FiniteGraph V E)
    (ψ : V → ℝ) (c : WalkData V E) (hc : IsCycle g c) :
    (∑ i, edgeGain g ψ (c.edge i)) = cycleGain g c := by
  have hs : (∑ i, ψ (g.source (c.edge i))) =
      ∑ i : Fin c.length, ψ (c.vertex i.castSucc) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [(hc.2.1 i).1]
  have ht : (∑ i, ψ (g.target (c.edge i))) =
      ∑ i : Fin c.length, ψ (c.vertex i.succ) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [(hc.2.1 i).2]
  have hfirst := Fin.sum_univ_succ (fun i : Fin (c.length + 1) => ψ (c.vertex i))
  have hlast := Fin.sum_univ_castSucc (fun i : Fin (c.length + 1) => ψ (c.vertex i))
  have hclose : ψ (c.vertex (Fin.last c.length)) = ψ (c.vertex 0) := congrArg ψ hc.2.2
  simp only [edgeGain, cycleGain, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hs, ht]
  linarith

theorem strict_feasible_implies_cycle_safe {V E : Type} (g : FiniteGraph V E)
    (D : Finset E) (h : StrictFeasible g D) : CycleSafe g D := by
  classical
  obtain ⟨ψ, hψ⟩ := h
  intro c hc hkept
  have hnonempty : (Finset.univ : Finset (Fin c.length)).Nonempty :=
    ⟨⟨0, hc.1⟩, Finset.mem_univ _⟩
  have hnegative : (∑ i, edgeGain g ψ (c.edge i)) <
      ∑ _i : Fin c.length, (0 : ℝ) :=
    Finset.sum_lt_sum_of_nonempty hnonempty (fun i _ => hψ (c.edge i) (hkept i))
  simpa only [cycle_correction_telescope g ψ c hc, Finset.sum_const_zero] using hnegative

theorem cycle_safe_iff_hits_nonnegative {V E : Type} (g : FiniteGraph V E)
    (D : Finset E) : CycleSafe g D ↔ HitsNonnegativeCycles g D := by
  classical
  constructor
  · intro hsafe c hc hgain
    by_contra hnot
    push Not at hnot
    have hnegative := hsafe c hc hnot
    exact (not_lt_of_ge hgain) hnegative
  · intro hhit c hc hkept
    by_contra hnot
    obtain ⟨i, hi⟩ := hhit c hc (le_of_not_gt hnot)
    exact hkept i hi

theorem elementary_length_le_card {V E : Type} [Fintype V] (c : WalkData V E)
    (hc : IsElementary c) : c.length ≤ Fintype.card V := by
  simpa only [Fintype.card_fin] using
    Fintype.card_le_of_injective (fun i : Fin c.length => c.vertex i.castSucc) hc

end ExternalO3OptimizationCycles
