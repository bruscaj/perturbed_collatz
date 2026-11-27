import Collatz.SevenStepCertificate.B1Entry
import Collatz.SevenStepCertificate.A3Recursive
import Collatz.SevenStepCertificate.B1SelfReturns
import Collatz.SevenStepCertificate.B1Repayment

/-! A single explicit complementary B1 obligation sufficient for the final proof.
Every excluded input reduces to a strictly smaller B1 parameter. This extra
condition is essential: a smaller W partner at another phase alone does not
justify induction restricted to B1. -/
namespace Collatz.SevenStepCertificate

def B1SelfCertified (t : Nat) : Prop :=
  (t % 3 = 0 ∧ ∃ k q, t = 2^k*q ∧ B1ElementaryGuard (k%14) (q%4)) ∨
  (t % 3 = 0 ∧ ∃ h q, t = 2^(14*h+6)*q ∧ (59049^h*q) % 32 = 15) ∨
  (∃ v, t = 16777216*v+1) ∨ B1DirectGuard t ∨ B1RepaymentGuard t

theorem b1_div_three_self_merger (t k q : Nat) (ht : t % 3 = 0)
    (eq : t = 2^k*q) (guard : B1ElementaryGuard (k%14) (q%4)) :
    run (.p1,6*t) (k+3) = run (.p1,6*(t/3)) (k+3) := by
  have meet : run (.p1,6*t) (k+3) = run (.p2,3*t) (k+2) := by
    rw [eq]
    exact b1_guarded_binary_run_merger k q guard
  have factor : 9*(t/3) = 3*t := by omega
  calc
    run (.p1,6*t) (k+3) = run (.p2,3*t) (k+2) := meet
    _ = run (.p1,6*(t/3)) (k+3) := by
      rw [show k+3 = 1+(k+2) by omega,
          run_add (.p1,6*(t/3)) 1 (k+2),b1_initial_step,factor]

theorem b1_div_nine_self_merger (t h q : Nat) (ht : t % 9 = 0)
    (eq : t = 2^(14*h+6)*q)
    (guard : (59049^h*q) % 32 = 13 ∨ (59049^h*q) % 32 = 15) :
    run (.p1,6*t) (14*h+12) = run (.p1,6*(t/9)) (14*h+12) := by
  have factor : 9*(t/9) = t := by omega
  have meet : run (.p2,9*t) (14*h+11) = run (.p2,t) (14*h+11) := by
    rw [eq]
    exact ratio_nine_phase_two_pumped h q guard
  rw [show 14*h+12 = 1+(14*h+11) by omega,
      run_add (.p1,6*t) 1 (14*h+11),
      run_add (.p1,6*(t/9)) 1 (14*h+11),b1_initial_step,b1_initial_step,factor]
  exact meet

/-- Use the larger B1 parameter 3*t only as a meeting bridge, without any
capture assumption on it. Two proved mergers yield the smaller parameter t/3. -/
theorem b1_tripling_bridge (t h q : Nat) (ht : t % 3 = 0)
    (eq : t = 2^(14*h+6)*q) (terminal : (59049^h*q) % 32 = 15) :
    run (.p1,6*t) (14*h+12) = run (.p1,6*(t/3)) (14*h+12) := by
  have mod_four : (59049^h*q) % 4 = q % 4 := by
    rw [Nat.mul_mod,pump_multiplier_mod_four,Nat.one_mul,Nat.mod_mod]
  have q_four : q % 4 = 3 := by omega
  have guard : B1ElementaryGuard ((14*h+6)%14) ((3*q)%4) := by
    unfold B1ElementaryGuard
    omega
  have scaled : 3*t = 2^(14*h+6)*(3*q) := by rw [eq]; ac_rfl
  have small : 3*(3*t) = 9*t := by omega
  have first : run (.p1,6*(3*t)) (14*h+9) = run (.p1,6*t) (14*h+9) := by
    have meet := b1_guarded_binary_run_merger (14*h+6) (3*q) guard
    rw [← scaled,small] at meet
    have mt : 14*h+6+3 = 14*h+9 := by omega
    have st : 14*h+6+2 = 14*h+8 := by omega
    rw [mt,st] at meet
    calc
      run (.p1,6*(3*t)) (14*h+9) = run (.p2,9*t) (14*h+8) := meet
      _ = run (.p1,6*t) (14*h+9) := by
        rw [show 14*h+9 = 1+(14*h+8) by omega,
            run_add (.p1,6*t) 1 (14*h+8),b1_initial_step]
  have advanced : run (.p1,6*(3*t)) (14*h+12) = run (.p1,6*t) (14*h+12) := by
    rw [show 14*h+12 = (14*h+9)+3 by omega,
        run_add (.p1,6*(3*t)) (14*h+9) 3,
        run_add (.p1,6*t) (14*h+9) 3,first]
  have scaled_terminal : (59049^h*(3*q)) % 32 = 13 ∨ (59049^h*(3*q)) % 32 = 15 := by
    left
    have rearrange : 59049^h*(3*q) = 3*(59049^h*q) := by ac_rfl
    rw [rearrange,Nat.mul_mod,terminal]
  have second := b1_div_nine_self_merger (3*t) h (3*q) (by omega) scaled scaled_terminal
  have quotient : (3*t)/9 = t/3 := by omega
  rw [quotient] at second
  exact advanced.symm.trans second

theorem b1_self_certified_progress (t : Nat) (ht : 0 < t) (guard : B1SelfCertified t) :
    B1SelfProgress t := by
  rcases guard with ⟨div, k,q,eq,hg⟩ | ⟨div,h,q,eq,hg⟩ | ⟨v,eq⟩ | direct | repayment
  · right
    exact ⟨t/3,k+3,k+3,by omega,by omega,b1_div_three_self_merger t k q div eq hg⟩
  · right
    exact ⟨t/3,14*h+12,14*h+12,by omega,by omega,b1_tripling_bridge t h q div eq hg⟩
  · subst t
    by_cases hz : v = 0
    · subst v
      left
      exact ⟨18,by rfl⟩
    · right
      refine ⟨1179648*v+1,25,18,by omega,by omega,?_⟩
      have source : 6*(16777216*v+1) = 3*(33554432*v+2) := by omega
      have alternate : 6*(1179648*v+1) = 3*(2359296*v+2) := by omega
      rw [source,alternate]
      exact b1_shadow_merger v
  · exact b1_direct_self_progress t direct
  · exact b1_repayment_self_progress t repayment

/-- This single universal complementary proposition remains unproved. -/
def B1FinalObligation : Prop :=
  ∀ t, 0 < t → ¬ B1SelfCertified t → Captured (.p1,6*t)

theorem full_b1_of_final_obligation (remaining : B1FinalObligation) : B1Obligation := by
  have all : ∀ t, 0 < t → Captured (.p1,6*t) := by
    intro t
    induction t using Nat.strongRecOn with
    | ind t ih =>
      intro ht
      classical
      by_cases guard : B1SelfCertified t
      · rcases b1_self_certified_progress t ht guard with captured | reduced
        · exact captured
        · obtain ⟨s,a,b,hs,hless,meet⟩ := reduced
          exact captured_of_coalescence (.p1,6*t) (.p1,6*s) a b meet (ih s hless hs)
      · exact remaining t ht guard
  intro t ht
  have source : 3*(2*t) = 6*t := by omega
  rw [source]
  exact all t ht

theorem global_capture_of_final_obligation (remaining : B1FinalObligation)
    (p : Phase) (z : Nat) (hz : 0 < z) : Captured (p,z) :=
  global_capture_of_b1_alone (full_b1_of_final_obligation remaining) p z hz

theorem global_capture_iff_final_obligation :
    (∀ p z, 0 < z → Captured (p,z)) ↔ B1FinalObligation := by
  constructor
  · intro all t ht _
    exact all .p1 (6*t) (by omega)
  · exact global_capture_of_final_obligation

theorem global_safe_physical_capture_of_final_obligation (remaining : B1FinalObligation)
    (p : Phase) (n : Nat) (hs : PhysicalSafe p n) :
    ∃ k q, physicalRun (p,(n : Int)) k = (q,physical q (cycleValue q)) :=
  global_safe_physical_capture_of_b1_alone (full_b1_of_final_obligation remaining) p n hs

end Collatz.SevenStepCertificate
