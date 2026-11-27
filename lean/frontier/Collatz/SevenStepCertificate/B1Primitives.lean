import Collatz.SevenStepCertificate.Certificates

/-! Exact primitive identities for the new elementary B1 binary-run rule.
The full unbounded accepted-guard induction is supplied in B1AllGuards.lean.
These primitives and that induction do not assert capture of the full B1 family. -/
namespace Collatz.SevenStepCertificate

theorem even_pump_phase_two (t : Nat) :
    run (.p2, 16384*t+0) 14 = (.p2, 59049*t+0) := by
  have h0 : next (.p2, 16384*t+0) = (.p3, 24576*t+0) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p3, 24576*t+0) = (.p4, 12288*t+0) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h2 : next (.p4, 12288*t+0) = (.p5, 18432*t+0) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h3 : next (.p5, 18432*t+0) = (.p6, 27648*t+0) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p6, 27648*t+0) = (.p0, 13824*t+0) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h5 : next (.p0, 13824*t+0) = (.p1, 20736*t+0) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h6 : next (.p1, 20736*t+0) = (.p2, 31104*t+0) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h7 : next (.p2, 31104*t+0) = (.p3, 46656*t+0) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h8 : next (.p3, 46656*t+0) = (.p4, 23328*t+0) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h9 : next (.p4, 23328*t+0) = (.p5, 34992*t+0) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h10 : next (.p5, 34992*t+0) = (.p6, 52488*t+0) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h11 : next (.p6, 52488*t+0) = (.p0, 26244*t+0) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h12 : next (.p0, 26244*t+0) = (.p1, 39366*t+0) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h13 : next (.p1, 39366*t+0) = (.p2, 59049*t+0) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]

theorem b1_initial_step (t : Nat) : run (.p1,6*t) 1 = (.p2,9*t) := by
  change next (.p1,6*t) = (.p2,9*t)
  apply Prod.ext
  · rfl
  · simp only [next,update,U]; split <;> omega

theorem b1_smaller_rank_gap (t : Nat) : rank .p1 (2*t) = rank .p2 t + t := by
  simp only [rank,weight]
  omega

theorem b1_smaller_rank (t : Nat) (ht : 0 < t) : rank .p2 t < rank .p1 (2*t) := by
  rw [b1_smaller_rank_gap]
  omega

theorem ratio_three_TU (v : Nat) :
    U (T (4*v+1)) = 9*v+3 ∧ U (T (3*(4*v+1))) = 9*v+3 := by
  have a : T (4*v+1) = 6*v+2 := by unfold T; split <;> omega
  have b : T (3*(4*v+1)) = 18*v+5 := by unfold T; split <;> omega
  rw [a,b]
  constructor <;> unfold U <;> split <;> omega

theorem ratio_three_UU (v : Nat) :
    U (U (4*v+3)) = 3*v+3 ∧ U (U (3*(4*v+3))) = 3*v+3 := by
  have a : U (4*v+3) = 2*v+2 := by unfold U; split <;> omega
  have b : U (3*(4*v+3)) = 6*v+5 := by unfold U; split <;> omega
  rw [a,b]
  constructor <;> unfold U <;> split <;> omega

/-- The same-phase TU terminal applies at phases three and six. -/
theorem ratio_three_TU_merger (p : Phase) (v : Nat) (hp : p = .p3 ∨ p = .p6) :
    run (p,4*v+1) 2 = run (p,3*(4*v+1)) 2 := by
  have a := (ratio_three_TU v).1
  have b := (ratio_three_TU v).2
  rcases hp with rfl | rfl <;> simp only [run,next,Phase.next,update,a,b]

/-- The same-phase UU terminal applies at phases zero, one and four. -/
theorem ratio_three_UU_merger (p : Phase) (v : Nat)
    (hp : p = .p0 ∨ p = .p1 ∨ p = .p4) :
    run (p,4*v+3) 2 = run (p,3*(4*v+3)) 2 := by
  have a := (ratio_three_UU v).1
  have b := (ratio_three_UU v).2
  rcases hp with rfl | rfl | rfl <;> simp only [run,next,Phase.next,update,a,b]

/-- Any proved ratio-three meeting transfers capture from the smaller B1 witness. -/
theorem b1_capture_of_ratio_three_meeting (t k : Nat)
    (hmeet : run (.p2,9*t) k = run (.p2,3*t) k)
    (hsmall : Captured (.p2,3*t)) : Captured (.p1,6*t) := by
  apply captured_of_coalescence (.p1,6*t) (.p2,3*t) (1+k) k _ hsmall
  rw [run_add,b1_initial_step]
  exact hmeet

end Collatz.SevenStepCertificate
