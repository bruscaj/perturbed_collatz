import Collatz.SevenStepCertificate.A3TwoStage
import Collatz.SevenStepCertificate.N03TwoStage

/-! Exact complement obligations after certified B1, A3 and N03 exclusions.
This theorem keeps every missing case as an explicit hypothesis. -/
namespace Collatz.SevenStepCertificate

def B1Certified (t : Nat) : Prop :=
  (∃ k q, t = 2^k*q ∧ B1ElementaryGuard (k%14) (q%4)) ∨
  ∃ v, t = 16777216*v+1

def A3DirectGuard (t : Nat) : Prop :=
  t % 8 = 0 ∨ t % 8 = 2 ∨ t % 8 = 6 ∨ t % 32 = 20

def A3Certified (t : Nat) : Prop :=
  A3DirectGuard t ∨
  (∃ u, t = 16*u+12 ∧ A3EvenRatioGuard u) ∨
  (∃ u, t = 16*u+4 ∧ A3DifferenceGuard u) ∨
  ∃ u, t = 16*u+4 ∧ A3TwoStageGuard u

def N03Certified (t : Nat) : Prop :=
  (∃ v, t = 262144*v) ∨
  (∃ v, t = 512*v+145 ∧ N03DifferenceGuard v) ∨
  ∃ v, t = 512*v+145 ∧ N03TwoStageGuard v

theorem b1_certified_progress (t : Nat) (ht : 0 < t) (guard : B1Certified t) :
    Progress .p1 (2*t) := by
  rcases guard with ⟨k,q,eq,hg⟩ | ⟨v,eq⟩
  · subst t
    right
    refine ⟨.p2,2^k*q,k+3,k+2,?_,ht,?_,?_⟩
    · simp [SectionPhase]
    · exact b1_guarded_binary_run_rank_reduction k q hg
    · have source : 3*(2*(2^k*q)) = 6*(2^k*q) := by omega
      rw [source]
      exact b1_guarded_binary_run_merger k q hg
  · subst t
    by_cases hv : v = 0
    · subst v
      left
      exact ⟨18,by rfl⟩
    · right
      refine ⟨.p1,2359296*v+2,25,18,?_,?_,?_,?_⟩
      · simp [SectionPhase]
      · omega
      · simp only [rank,weight]; omega
      · have source : 2*(16777216*v+1) = 33554432*v+2 := by omega
        rw [source]
        exact b1_shadow_merger v

theorem a3_direct_progress (t : Nat) (guard : A3DirectGuard t) :
    Progress .p3 (4*t+3) := by
  rcases guard with h0 | h2 | h6 | h20
  · by_cases hz : t = 0
    · subst t
      left
      exact ⟨9,by rfl⟩
    · have eq : t = 8*(t/8)+0 := by omega
      have positive : 1 ≤ t/8 := by omega
      rw [eq]
      exact a3_direct_progress_0 (t/8) positive
  · by_cases h16 : t % 16 = 2
    · have eq : t = 16*(t/16)+2 := by omega
      rw [eq]
      exact a3_direct_progress_2 (t/16) (by omega)
    · by_cases h32 : t % 32 = 26
      · have eq : t = 32*(t/32)+26 := by omega
        rw [eq]
        exact a3_direct_progress_3 (t/32) (by omega)
      · have cases : t % 128 = 10 ∨ t % 128 = 74 ∨ t % 128 = 42 ∨ t % 128 = 106 := by omega
        rcases cases with h | h | h | h
        · have eq : t = 128*(t/128)+10 := by omega
          rw [eq]
          exact a3_direct_progress_4 (t/128) (by omega)
        · have eq : t = 128*(t/128)+74 := by omega
          rw [eq]
          exact a3_direct_progress_5 (t/128) (by omega)
        · have eq : t = 128*(t/128)+42 := by omega
          rw [eq]
          exact a3_direct_progress_6 (t/128) (by omega)
        · have eq : t = 128*(t/128)+106 := by omega
          rw [eq]
          exact a3_direct_progress_7 (t/128) (by omega)
  · have eq : t = 8*(t/8)+6 := by omega
    rw [eq]
    exact a3_direct_progress_1 (t/8) (by omega)
  · have eq : t = 32*(t/32)+20 := by omega
    rw [eq]
    exact a3_direct_progress_8 (t/32) (by omega)

theorem a3_certified_progress (t : Nat) (guard : A3Certified t) :
    Progress .p3 (4*t+3) := by
  rcases guard with direct | ⟨u,eq,ratio⟩ | ⟨u,eq,difference⟩ | ⟨u,eq,two_stage⟩
  · exact a3_direct_progress t direct
  · subst t
    exact a3_even_ratio_progress u ratio
  · subst t
    exact a3_difference_progress u difference
  · subst t
    exact a3_two_stage_progress u two_stage

theorem n03_certified_progress (t : Nat) (guard : N03Certified t) :
    Progress .p5 (8*t+2) := by
  rcases guard with ⟨v,eq⟩ | ⟨v,eq,difference⟩ | ⟨v,eq,two_stage⟩
  · subst t
    by_cases hv : v = 0
    · subst v
      left
      exact ⟨14,by rfl⟩
    · right
      refine ⟨.p5,147456*v+2,21,14,?_,?_,?_,?_⟩
      · simp [SectionPhase]
      · omega
      · simp only [rank,weight]; omega
      · have source : 8*(262144*v)+2 = 2097152*v+2 := by omega
        rw [source]
        exact n03_shadow_merger v
  · subst t
    exact n03_difference_progress v difference
  · subst t
    exact n03_two_stage_progress v two_stage

def B1ComplementObligation : Prop :=
  ∀ t, 0 < t → ¬ B1Certified t → Captured (.p1,3*(2*t))

def A3ComplementObligation : Prop :=
  ∀ t, ¬ A3Certified t → Captured (.p3,3*(4*t+3))

def N03ComplementObligation : Prop :=
  ∀ t, ¬ N03Certified t → Captured (.p5,3*(8*t+2))

theorem refined_residual_progress
    (hB1 : B1ComplementObligation) (hA3 : A3ComplementObligation)
    (hN03 : N03ComplementObligation) :
    ∀ p m, SectionPhase p → 0 < m → Residual p m → Progress p m := by
  classical
  apply residual_progress_of_rows
  · intro t ht
    by_cases guard : B1Certified t
    · exact b1_certified_progress t ht guard
    · exact Or.inl (hB1 t ht guard)
  · intro t
    by_cases guard : A3Certified t
    · exact a3_certified_progress t guard
    · exact Or.inl (hA3 t guard)
  · intro t
    by_cases guard : N03Certified t
    · exact n03_certified_progress t guard
    · exact Or.inl (hN03 t guard)

/-- Only the explicitly defined complementary parameter sets remain assumptions. -/
theorem global_capture_of_refined_frontier
    (hB1 : B1ComplementObligation) (hA3 : A3ComplementObligation)
    (hN03 : N03ComplementObligation) (p : Phase) (z : Nat) (hz : 0 < z) :
    Captured (p,z) :=
  global_capture_of_residual_progress (refined_residual_progress hB1 hA3 hN03) p z hz

theorem global_capture_iff_refined_frontier :
    (∀ p z, 0 < z → Captured (p,z)) ↔
      B1ComplementObligation ∧ A3ComplementObligation ∧ N03ComplementObligation := by
  constructor
  · intro h
    refine ⟨?_,?_,?_⟩
    · intro t ht _; exact h .p1 (3*(2*t)) (by omega)
    · intro t _; exact h .p3 (3*(4*t+3)) (by omega)
    · intro t _; exact h .p5 (3*(8*t+2)) (by omega)
  · rintro ⟨hB1,hA3,hN03⟩
    exact global_capture_of_refined_frontier hB1 hA3 hN03

theorem global_safe_physical_capture_of_refined_frontier
    (hB1 : B1ComplementObligation) (hA3 : A3ComplementObligation)
    (hN03 : N03ComplementObligation) (p : Phase) (n : Nat) (hs : PhysicalSafe p n) :
    ∃ k q, physicalRun (p,(n : Int)) k = (q,physical q (cycleValue q)) := by
  have all := global_capture_of_refined_frontier hB1 hA3 hN03
  have obligations := global_capture_iff_three.mp all
  exact global_safe_physical_capture_of_three obligations.1 obligations.2.1 obligations.2.2 p n hs

end Collatz.SevenStepCertificate
