import PressureAnalyticExpectedTypes
import AnalyticFekete
import WordConcatenation

/-! Actual phase infimum, candidate supremum and their Fekete limit.
No uniform phase limit or selected pressure law is assumed. -/
namespace ExternalBridgePressureAnalyticPhaseInfimum
open ExternalFiniteBridgeDraft ExternalBridgePressureDraft ExternalBridgePressureWordDraft
open ExternalBridgePressureAnalyticDraft ExternalBridgePressureAnalyticFekete
open ExternalBridgePressureWordArithmetic ExternalBridgePressureWordFiniteComparison
open ExternalBridgePressureWordConcatenation ExternalBridgePressurePhase
open Set Filter
open scoped Topology

 theorem phase_values_nonempty (n : ℕ) (lam : ℝ) : (phaseValues n lam).Nonempty := by
  exact ⟨auxLogPartition 0 n lam,0,by constructor <;> norm_num,rfl⟩

theorem phase_values_lower (n : ℕ) (lam : ℝ) (hl : 0≤lam) : BddBelow (phaseValues n lam) := by
  refine ⟨0,?_⟩
  rintro v ⟨x,hx,rfl⟩
  exact ((finite_partition_bounds x n lam ⟨hx.1,le_of_lt hx.2⟩).2 hl).1

theorem phase_values_upper (n : ℕ) (lam : ℝ) (hl : 0≤lam) : BddAbove (phaseValues n lam) := by
  refine ⟨(n : ℝ)*(Real.log 4+lam),?_⟩
  rintro v ⟨x,hx,rfl⟩
  exact ((finite_partition_bounds x n lam ⟨hx.1,le_of_lt hx.2⟩).2 hl).2

theorem phase_infimum_zero (lam : ℝ) : phaseInfimum 0 lam=0 := by
  have he : phaseValues 0 lam = {0} := by
    ext v
    constructor
    · rintro ⟨x,_,hv⟩
      rw [(zero_volume_convention x lam).2.2.2.1] at hv
      exact hv
    · intro hv
      refine ⟨0,by constructor <;> norm_num,?_⟩
      rw [(zero_volume_convention 0 lam).2.2.2.1]
      exact hv
  simp only [phaseInfimum,he,csInf_singleton]

theorem phase_infimum_nonneg (n : ℕ) (lam : ℝ) (hl : 0≤lam) : 0≤phaseInfimum n lam := by
  apply le_csInf (phase_values_nonempty n lam)
  rintro v ⟨x,hx,rfl⟩
  exact ((finite_partition_bounds x n lam ⟨hx.1,le_of_lt hx.2⟩).2 hl).1

theorem phase_infimum_le_phase (n : ℕ) (lam : ℝ) (hl : 0≤lam)
    (x : ℝ) (hx : ActualPhase x) : phaseInfimum n lam≤auxLogPartition x n lam :=
  csInf_le (phase_values_lower n lam hl) ⟨x,hx,rfl⟩

theorem phase_infimum_roof (n : ℕ) (lam : ℝ) (hl : 0≤lam) :
    phaseInfimum n lam≤(n : ℝ)*(Real.log 4+lam) := by
  exact (phase_infimum_le_phase n lam hl 0 (by constructor <;> norm_num)).trans
    (((finite_partition_bounds 0 n lam (by constructor <;> norm_num)).2 hl).2)

theorem le_phase_infimum (n : ℕ) (lam a : ℝ)
    (ha : ∀ x : ℝ,ActualPhase x → a≤auxLogPartition x n lam) : a≤phaseInfimum n lam := by
  apply le_csInf (phase_values_nonempty n lam)
  rintro v ⟨x,hx,rfl⟩
  exact ha x hx

theorem phase_infimum_well_posed : PhaseInfimumWellPosed := by
  refine ⟨phase_infimum_zero,fun lam hl n => ?_⟩
  exact ⟨phase_values_nonempty n lam,phase_values_lower n lam hl,phase_values_upper n lam hl,
    phase_infimum_nonneg n lam hl,phase_infimum_roof n lam hl,
    phase_infimum_le_phase n lam hl,fun a ha => le_phase_infimum n lam a ha⟩

theorem phase_infimum_superadditivity : PhaseInfimumSuperadditivity := by
  intro lam hl m n
  apply le_phase_infimum (m+n) lam
  intro x hx
  have hy : ActualPhase (phaseShift x m) := phase_shift_bounds x m
  have hm := phase_infimum_le_phase m lam hl x hx
  have hn := phase_infimum_le_phase n lam hl (phaseShift x m) hy
  have hc := partition_cocycle x m n lam hx hl
  linarith

theorem pressure_values_nonempty (lam : ℝ) : (pressureValues lam).Nonempty :=
  ⟨phaseInfimum 1 lam/(1 : ℝ),1,by norm_num,by norm_num⟩

theorem pressure_ratio_nonneg (lam : ℝ) (hl : 0≤lam) (L : ℕ) :
    0≤phaseInfimum L lam/(L : ℝ) :=
  div_nonneg (phase_infimum_nonneg L lam hl) (Nat.cast_nonneg _)

theorem pressure_ratio_roof (lam : ℝ) (hl : 0≤lam) (L : ℕ) (hL : 1≤L) :
    phaseInfimum L lam/(L : ℝ)≤Real.log 4+lam := by
  have hp : (0 : ℝ)<L := by exact_mod_cast hL
  apply (div_le_iff₀ hp).mpr
  simpa only [mul_comm] using phase_infimum_roof L lam hl

theorem pressure_values_lower (lam : ℝ) (hl : 0≤lam) : BddBelow (pressureValues lam) := by
  refine ⟨0,?_⟩
  rintro v ⟨L,_,rfl⟩
  exact pressure_ratio_nonneg lam hl L

theorem pressure_values_upper (lam : ℝ) (hl : 0≤lam) : BddAbove (pressureValues lam) := by
  refine ⟨Real.log 4+lam,?_⟩
  rintro v ⟨L,hL,rfl⟩
  exact pressure_ratio_roof lam hl L hL

theorem candidate_pressure_well_posed : CandidatePressureWellPosed := by
  intro lam hl
  have hne := pressure_values_nonempty lam
  have hu := pressure_values_upper lam hl
  have hlo := pressure_values_lower lam hl
  have hratio (L : ℕ) (hL : 1≤L) : phaseInfimum L lam/(L : ℝ)≤candidatePressure lam := by
    simp only [candidatePressure,hl,ite_true]
    exact le_csSup hu ⟨L,hL,rfl⟩
  refine ⟨hne,hu,hlo,?_,?_,hratio⟩
  · exact (pressure_ratio_nonneg lam hl 1).trans (hratio 1 (by norm_num))
  · simp only [candidatePressure,hl,ite_true]
    apply csSup_le hne
    rintro v ⟨L,hL,rfl⟩
    exact pressure_ratio_roof lam hl L hL

theorem fekete_candidate_limit : FeketeCandidateLimit :=
  fekete_candidate_limit_of_phase_infimum_facts phase_infimum_well_posed phase_infimum_superadditivity

end ExternalBridgePressureAnalyticPhaseInfimum
