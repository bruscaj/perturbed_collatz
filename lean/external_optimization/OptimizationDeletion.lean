import OptimizationPaths
import OptimizationEncoding
import OptimizationArithmetic

/-! Exact finite deletion/potential optima, followed by the dyadic numerator
identification. No full-density or algorithm conclusion is assumed. -/
namespace ExternalO3OptimizationDeletion
open ExternalO3OptimizationDraft ExternalO3GeneralDraft
open ExternalO3OptimizationArithmetic
open scoped BigOperators

noncomputable def badEdges {V E : Type} [Fintype E] (g : FiniteGraph V E)
    (ψ : V → ℝ) : Finset E := by
  classical
  exact Finset.univ.filter (fun e => 0 ≤ edgeGain g ψ e)

theorem failureCost_eq_bad_deletion {V E : Type} [Fintype E] (g : FiniteGraph V E)
    (ψ : V → ℝ) : failureCost g ψ = deletionCost g (badEdges g ψ) := by
  classical
  simp [failureCost, deletionCost, badEdges, Finset.sum_filter]

theorem badEdges_safe {V E : Type} [Fintype E] (g : FiniteGraph V E)
    (ψ : V → ℝ) : CycleSafe g (badEdges g ψ) := by
  classical
  apply ExternalO3OptimizationCycles.strict_feasible_implies_cycle_safe
  refine ⟨ψ, ?_⟩
  intro e he
  have hh : ¬ 0 ≤ edgeGain g ψ e := by simpa [badEdges] using he
  exact lt_of_not_ge hh

theorem deletionCost_nonneg {V E : Type} (g : FiniteGraph V E) (D : Finset E)
    (hw : ∀ e, 0 ≤ g.weight e) : 0 ≤ deletionCost g D := by
  exact Finset.sum_nonneg (fun e _ => hw e)

theorem failureCost_nonneg {V E : Type} [Fintype E] (g : FiniteGraph V E)
    (ψ : V → ℝ) (hw : ∀ e, 0 ≤ g.weight e) : 0 ≤ failureCost g ψ := by
  rw [failureCost_eq_bad_deletion]
  exact deletionCost_nonneg g _ hw

theorem feasible_badEdges_subset {V E : Type} [Fintype E] (g : FiniteGraph V E)
    (D : Finset E) (ψ : V → ℝ)
    (hψ : ∀ e, e ∉ D → edgeGain g ψ e < 0) : badEdges g ψ ⊆ D := by
  classical
  intro e he
  by_contra heD
  have hnonneg : 0 ≤ edgeGain g ψ e := (Finset.mem_filter.mp he).2
  exact (not_lt_of_ge hnonneg) (hψ e heD)

theorem feasible_failureCost_le {V E : Type} [Fintype E] (g : FiniteGraph V E)
    (D : Finset E) (ψ : V → ℝ) (hw : ∀ e, 0 ≤ g.weight e)
    (hψ : ∀ e, e ∉ D → edgeGain g ψ e < 0) : failureCost g ψ ≤ deletionCost g D := by
  rw [failureCost_eq_bad_deletion]
  exact Finset.sum_le_sum_of_subset_of_nonneg (feasible_badEdges_subset g D ψ hψ)
    (fun e _ _ => hw e)

theorem exists_min_safe_deletion {V E : Type} [Fintype E] (g : FiniteGraph V E) :
    ∃ D : Finset E, CycleSafe g D ∧
      ∀ A : Finset E, CycleSafe g A → deletionCost g D ≤ deletionCost g A := by
  classical
  let S : Finset (Finset E) := Finset.univ.filter (CycleSafe g)
  have hnonempty : S.Nonempty := ⟨Finset.univ, by simp [S, delete_all_safe g]⟩
  obtain ⟨D, hD, hmin⟩ := Finset.exists_min_image S (deletionCost g) hnonempty
  exact ⟨D, (Finset.mem_filter.mp hD).2,
    fun A hA => hmin A (by simp [S, hA])⟩

theorem generic_deletion_optimum : GenericDeletionOptimum := by
  classical
  intro V E _ _ g hw
  obtain ⟨D, hD, hmin⟩ := exists_min_safe_deletion g
  obtain ⟨ψ, hψ⟩ := ExternalO3OptimizationPaths.cycle_safe_implies_strict_feasible g D hD
  have hbound (φ : V → ℝ) : deletionCost g D ≤ failureCost g φ := by
    rw [failureCost_eq_bad_deletion]
    exact hmin _ (badEdges_safe g φ)
  have hcost : failureCost g ψ = deletionCost g D :=
    le_antisymm (feasible_failureCost_le g D ψ hw hψ) (hbound ψ)
  have hpleast : IsLeast {r | ∃ φ : V → ℝ, r = failureCost g φ} (deletionCost g D) := by
    refine ⟨⟨ψ, hcost.symm⟩, ?_⟩
    rintro r ⟨φ, rfl⟩
    exact hbound φ
  have hdleast : IsLeast {r | ∃ A : Finset E, CycleSafe g A ∧ r = deletionCost g A}
      (deletionCost g D) := by
    refine ⟨⟨D, hD, rfl⟩, ?_⟩
    rintro r ⟨A, hA, rfl⟩
    exact hmin A hA
  have hpinf : finitePotentialInfimum g = deletionCost g D := hpleast.csInf_eq
  have hdinf : deletionInfimum g = deletionCost g D := hdleast.csInf_eq
  refine ⟨⟨failureCost g ψ, ψ, rfl⟩, ⟨0, ?_⟩,
    ⟨deletionCost g D, D, hD, rfl⟩, ⟨0, ?_⟩,
    hpinf.trans hdinf.symm, D, ψ, hD, hdinf.symm, hcost.trans hpinf.symm⟩
  · rintro r ⟨φ, rfl⟩
    exact failureCost_nonneg g φ hw
  · rintro r ⟨A, _, rfl⟩
    exact deletionCost_nonneg g A hw

theorem finiteOptimum_real (h : Depth) (M J : ℕ) :
    (finiteOptimum h M J : ℝ) =
      (optimalNumerator h M J : ℝ) / ((2 : ℕ) ^ commonExponent h M J : ℝ) := by
  simp [finiteOptimum]

theorem finiteOptimum_eq_deletionInfimum (h : Depth) (M J : ℕ) (hM : 2 ≤ M) (hJ : 2 ≤ J) :
    (finiteOptimum h M J : ℝ) = deletionInfimum (truncatedGraph h M J) := by
  obtain ⟨_, ⟨D, hD, hunits⟩, hmin⟩ := numerator_minimum_well_posed h M J hM hJ
  have hden : (0 : ℝ) < ((2 : ℕ) ^ commonExponent h M J : ℝ) := by positivity
  have hcost : (finiteOptimum h M J : ℝ) = deletionCost (truncatedGraph h M J) D := by
    rw [finiteOptimum_real, deletion_dyadic_denominator h M J hJ, hunits]
  have hleast : IsLeast
      {r | ∃ A : Finset (TruncatedEdge h M J), CycleSafe (truncatedGraph h M J) A ∧
        r = deletionCost (truncatedGraph h M J) A} (finiteOptimum h M J : ℝ) := by
    refine ⟨⟨D, hD, hcost⟩, ?_⟩
    rintro r ⟨A, hA, rfl⟩
    rw [finiteOptimum_real, deletion_dyadic_denominator h M J hJ]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hmin A hA) (le_of_lt hden)
  exact hleast.csInf_eq.symm

theorem finite_optimization_exact : FiniteOptimizationExact := by
  intro h M J hM hJ
  have hw : ∀ e : TruncatedEdge h M J, 0 ≤ (truncatedGraph h M J).weight e := by
    intro e
    change 0 ≤ (rationalWeight h M J e : ℝ)
    simp only [rationalWeight]
    positivity
  obtain ⟨_, hbdd, _, _, heq, _, ψ, _, _, hψ⟩ :=
    generic_deletion_optimum (Vertex h M) (TruncatedEdge h M J) (truncatedGraph h M J) hw
  have hq : (finiteOptimum h M J : ℝ) = finitePotentialInfimum (truncatedGraph h M J) :=
    (finiteOptimum_eq_deletionInfimum h M J hM hJ).trans heq.symm
  refine ⟨hq, ?_, ψ, hψ.trans hq.symm⟩
  intro φ
  rw [hq]
  exact csInf_le hbdd ⟨φ, rfl⟩

end ExternalO3OptimizationDeletion
