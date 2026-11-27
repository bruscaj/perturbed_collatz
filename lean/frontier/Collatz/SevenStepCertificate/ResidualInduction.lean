import Collatz.SevenStepCertificate

/-! A general strong-induction interface for certified reductions inside the
three residual rows. A merger may use different clocks; its alternate launch
must have strictly smaller W at the original section, including its phase. -/
namespace Collatz.SevenStepCertificate

def SmallerMerger (p : Phase) (m : Nat) : Prop :=
  ∃ q n a b, SectionPhase q ∧ 0 < n ∧ rank q n < rank p m ∧
    run (p,3*m) a = run (q,3*n) b

def Progress (p : Phase) (m : Nat) : Prop := Captured (p,3*m) ∨ SmallerMerger p m

theorem progress_of_direct (p q : Phase) (m n k : Nat)
    (hq : SectionPhase q) (hn : 0 < n) (hless : rank q n < rank p m)
    (meet : run (p,3*m) k = (q,3*n)) : Progress p m := by
  right
  exact ⟨q,n,k,0,hq,hn,hless,meet⟩

/-- Every residual launch must either capture or meet a strictly smaller launch.
This is a universal quantified premise, not merely coverage of selected edges. -/
theorem section_capture_of_residual_progress
    (hprogress : ∀ p m, SectionPhase p → 0 < m → Residual p m → Progress p m)
    (p : Phase) (m : Nat) (hp : SectionPhase p) (hm : 0 < m) :
    Captured (p,3*m) := by
  have main : ∀ r : Nat, ∀ q n, rank q n = r → SectionPhase q → 0 < n →
      Captured (q,3*n) := by
    intro r
    induction r using Nat.strongRecOn with
    | ind r ih =>
      intro q n heq hq hn
      have step : Progress q n := by
        rcases complete_classifier q n hq hn with residual | captured | reduced
        · exact hprogress q n hq hn residual
        · exact Or.inl captured
        · obtain ⟨q',n',k,hq',hn',hless,meet⟩ := reduced
          exact progress_of_direct q q' n n' k hq' hn' hless meet
      rcases step with captured | reduced
      · exact captured
      · obtain ⟨q',n',a,b,hq',hn',hless,meet⟩ := reduced
        exact captured_of_coalescence (q,3*n) (q',3*n') a b meet
          (ih (rank q' n') (by omega) q' n' rfl hq' hn')
  exact main (rank p m) p m rfl hp hm

theorem global_capture_of_residual_progress
    (hprogress : ∀ p m, SectionPhase p → 0 < m → Residual p m → Progress p m)
    (p : Phase) (z : Nat) (hz : 0 < z) : Captured (p,z) := by
  obtain ⟨k,_,q,m,hq,hm,meet⟩ := section_entry p z hz
  apply captured_of_run (p,z) k
  rw [meet]
  exact section_capture_of_residual_progress hprogress q m hq hm

theorem residual_progress_of_rows
    (hB1 : ∀ t, 0 < t → Progress .p1 (2*t))
    (hA3 : ∀ t, Progress .p3 (4*t+3))
    (hN03 : ∀ t, Progress .p5 (8*t+2)) :
    ∀ p m, SectionPhase p → 0 < m → Residual p m → Progress p m := by
  intro p m _ hm hr
  cases p with
  | p0 => exact False.elim hr
  | p1 =>
    change m % 2 = 0 at hr
    have heq : m = 2*(m/2) := by omega
    rw [heq]
    exact hB1 (m/2) (by omega)
  | p2 => exact False.elim hr
  | p3 =>
    change m % 4 = 3 at hr
    have heq : m = 4*(m/4)+3 := by omega
    rw [heq]
    exact hA3 (m/4)
  | p4 => exact False.elim hr
  | p5 =>
    change m % 8 = 2 at hr
    have heq : m = 8*(m/8)+2 := by omega
    rw [heq]
    exact hN03 (m/8)
  | p6 => exact False.elim hr

end Collatz.SevenStepCertificate
