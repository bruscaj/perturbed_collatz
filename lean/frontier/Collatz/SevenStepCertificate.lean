import Collatz.SevenStepCertificate.Certificates
import Collatz.SevenStepCertificate.Relational

/-! A complete conditional theorem for the fixed seven-step word.
The only mathematical assumptions are the three explicitly named universal
capture obligations. The entrance cover, return cover, finite bases, rank
comparisons and signed-coordinate bridge are all proved in this project. -/
namespace Collatz.SevenStepCertificate

def alignment : Phase → Nat
  | .p0 => 0 | .p1 => 6 | .p2 => 5 | .p3 => 4
  | .p4 => 3 | .p5 => 2 | .p6 => 1

theorem alignment_bound (p : Phase) : alignment p ≤ 6 := by
  cases p <;> decide

theorem alignment_phase (p : Phase) (z : Nat) :
    (run (p,z) (alignment p)).1 = .p0 := by
  cases p <;> rfl

/-- Every positive seed at every phase reaches the section in at most eleven updates. -/
theorem section_entry (p : Phase) (z : Nat) (hz : 0 < z) :
    ∃ k, k ≤ 11 ∧ ∃ q m, SectionPhase q ∧ 0 < m ∧ run (p,z) k = (q,3*m) := by
  have pos := run_pos (p,z) hz (alignment p)
  obtain ⟨k,hk,q,m,hq,hm,meet⟩ := entry_phase_zero (run (p,z) (alignment p)).2 pos
  have aligned : run (p,z) (alignment p) = (.p0,(run (p,z) (alignment p)).2) := by
    apply Prod.ext
    · exact alignment_phase p z
    · rfl
  refine ⟨alignment p+k, ?_, q,m,hq,hm, ?_⟩
  · have ha := alignment_bound p
    omega
  · rw [run_add,aligned]
    exact meet

/-- Unresolved B1: every positive even section parameter at phase one is captured. -/
def B1Obligation : Prop := ∀ t : Nat, 0 < t → Captured (.p1,3*(2*t))
/-- Unresolved A3: every parameter 3 modulo 4 at phase three is captured. -/
def A3Obligation : Prop := ∀ t : Nat, Captured (.p3,3*(4*t+3))
/-- Unresolved N03: every parameter 2 modulo 8 at phase five is captured. -/
def N03Obligation : Prop := ∀ t : Nat, Captured (.p5,3*(8*t+2))

theorem residual_capture (hB1 : B1Obligation) (hA3 : A3Obligation)
    (hN03 : N03Obligation) (p : Phase) (m : Nat) (hm : 0 < m)
    (hr : Residual p m) : Captured (p,3*m) := by
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

/-- Simultaneous well-founded induction over every phase in the complete section. -/
theorem section_capture_of_three (hB1 : B1Obligation) (hA3 : A3Obligation)
    (hN03 : N03Obligation) (p : Phase) (m : Nat) (hp : SectionPhase p)
    (hm : 0 < m) : Captured (p,3*m) := by
  have main : ∀ r : Nat, ∀ q n, rank q n = r → SectionPhase q → 0 < n →
      Captured (q,3*n) := by
    intro r
    induction r using Nat.strongRecOn with
    | ind r ih =>
      intro q n heq hq hn
      rcases complete_classifier q n hq hn with residual | captured | reduced
      · exact residual_capture hB1 hA3 hN03 q n hn residual
      · exact captured
      · obtain ⟨q',n',k,hq',hn',hless,meet⟩ := reduced
        apply captured_of_run (q,3*n) k
        rw [meet]
        exact ih (rank q' n') (by omega) q' n' rfl hq' hn'
  exact main (rank p m) p m rfl hp hm

/-- The complete all-positive-seed theorem, conditional only on B1, A3 and N03. -/
theorem global_capture_of_three (hB1 : B1Obligation) (hA3 : A3Obligation)
    (hN03 : N03Obligation) (p : Phase) (z : Nat) (hz : 0 < z) :
    Captured (p,z) := by
  obtain ⟨k,_,q,m,hq,hm,meet⟩ := section_entry p z hz
  apply captured_of_run (p,z) k
  rw [meet]
  exact section_capture_of_three hB1 hA3 hN03 q m hq hm

/-- The three named universal obligations are exactly equivalent to global capture. -/
theorem global_capture_iff_three :
    (∀ p z, 0 < z → Captured (p,z)) ↔ B1Obligation ∧ A3Obligation ∧ N03Obligation := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro t ht; exact h .p1 (3*(2*t)) (by omega)
    · intro t; exact h .p3 (3*(4*t+3)) (by omega)
    · intro t; exact h .p5 (3*(8*t+2)) (by omega)
  · rintro ⟨hB1,hA3,hN03⟩
    exact global_capture_of_three hB1 hA3 hN03

/-- Encode a natural physical seed into positive coordinates. -/
def encodeValue : Phase → Nat → Nat
  | .p3, n => n
  | .p6, n => n
  | _, n => n+1

theorem encode_pos (p : Phase) (n : Nat) (hn : 0 < n) : 0 < encodeValue p n := by
  cases p <;> simp only [encodeValue] <;> omega

theorem decode_encode (p : Phase) (n : Nat) :
    decode (p,encodeValue p n) = (p,(n : Int)) := by
  apply Prod.ext
  · rfl
  · cases p <;> simp only [decode,physical,height,encodeValue] <;> omega

/-- Safe nonnegative physical inputs: zero is excluded only before a negative impulse. -/
def PhysicalSafe : Phase → Nat → Prop
  | .p3, n => 0 < n
  | .p6, n => 0 < n
  | _, _ => True

theorem encode_pos_of_safe (p : Phase) (n : Nat) (hs : PhysicalSafe p n) :
    0 < encodeValue p n := by
  cases p <;> simp only [PhysicalSafe,encodeValue] at * <;> omega

/-- The signed physical conclusion also covers every safe zero seed. -/
theorem global_safe_physical_capture_of_three (hB1 : B1Obligation) (hA3 : A3Obligation)
    (hN03 : N03Obligation) (p : Phase) (n : Nat) (hs : PhysicalSafe p n) :
    ∃ k q, physicalRun (p,(n : Int)) k = (q,physical q (cycleValue q)) := by
  have hz := encode_pos_of_safe p n hs
  obtain ⟨k,hk⟩ := global_capture_of_three hB1 hA3 hN03 p (encodeValue p n) hz
  let endpoint := run (p,encodeValue p n) k
  have endpoint_cycle : endpoint.2 = cycleValue endpoint.1 := hk
  refine ⟨k,endpoint.1, ?_⟩
  have faithful := run_faithful (p,encodeValue p n) hz k
  rw [decode_encode] at faithful
  rw [← faithful]
  apply Prod.ext
  · rfl
  · change physical endpoint.1 endpoint.2 = physical endpoint.1 (cycleValue endpoint.1)
    rw [endpoint_cycle]

/-- In particular, every positive physical seed at every phase is captured conditionally. -/
theorem global_physical_capture_of_three (hB1 : B1Obligation) (hA3 : A3Obligation)
    (hN03 : N03Obligation) (p : Phase) (n : Nat) (hn : 0 < n) :
    ∃ k q, physicalRun (p,(n : Int)) k = (q,physical q (cycleValue q)) := by
  apply global_safe_physical_capture_of_three hB1 hA3 hN03 p n
  cases p <;> simp only [PhysicalSafe] <;> trivial

end Collatz.SevenStepCertificate
