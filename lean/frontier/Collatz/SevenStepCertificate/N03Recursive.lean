import Collatz.SevenStepCertificate.FrontierIdentities

/-! A new unbounded difference-three merger in the live N03 family.
The progress coordinate is 115*x+702, not trajectory height. -/
namespace Collatz.SevenStepCertificate

theorem n03_difference_terminal (x : Nat) (hx : x % 32 = 27) :
    run (.p3,x) 5 = run (.p3,x+3) 5 := by
  have eq : x = 32*(x/32)+27 := by omega
  have upper : x+3 = 32*(x/32)+30 := by omega
  have small := n03_difference_terminal_small (x/32)
  have large := n03_difference_terminal_large (x/32)
  rw [← eq] at small
  rw [← upper] at large
  exact small.trans large.symm

theorem n03_difference_repeated (h x q : Nat)
    (eq : 115*x+702 = 128^h*q) (terminal : (243^h*q) % 32 = 31) :
    run (.p3,x) (7*h+5) = run (.p3,x+3) (7*h+5) := by
  induction h generalizing x q with
  | zero =>
    simp only [Nat.pow_zero,Nat.one_mul] at eq terminal
    have hx : x % 32 = 27 := by omega
    exact n03_difference_terminal x hx
  | succ h ih =>
    have eq' : 115*x+702 = 128*(128^h*q) := by
      rw [Nat.pow_succ] at eq
      simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using eq
    have residue : x % 128 = 54 := by omega
    have expand : x = 128*(x/128)+54 := by omega
    have upper : x+3 = 128*(x/128)+57 := by omega
    let v := x/128
    let nextX := 243*v+108
    have lower : 128^h*q = 115*v+54 := by dsimp [v]; omega
    have next_eq : 115*nextX+702 = 128^h*(243*q) := by
      have rearrange : 128^h*(243*q) = 243*(128^h*q) := by ac_rfl
      rw [rearrange,lower]
      dsimp [nextX]
      omega
    have next_terminal : (243^h*(243*q)) % 32 = 31 := by
      rw [Nat.pow_succ] at terminal
      simpa only [Nat.mul_assoc] using terminal
    have small : run (.p3,x) 7 = (.p3,nextX) := by
      rw [expand]
      exact n03_difference_pump_small v
    have large : run (.p3,x+3) 7 = (.p3,nextX+3) := by
      rw [upper]
      exact n03_difference_pump_large v
    rw [show 7*(h+1)+5 = 7+(7*h+5) by omega,
        run_add (.p3,x) 7 (7*h+5),run_add (.p3,x+3) 7 (7*h+5),small,large]
    exact ih nextX (243*q) next_eq next_terminal

def N03DifferenceGuard (v : Nat) : Prop :=
  ∃ h q, 115*(19683*v+5586)+702 = 128^h*q ∧ (243^h*q) % 32 = 31

theorem n03_difference_merger (v h q : Nat)
    (eq : 115*(19683*v+5586)+702 = 128^h*q)
    (terminal : (243^h*q) % 32 = 31) :
    run (.p5,3*(8*(512*v+145)+2)) (7*h+17) =
      run (.p1,3*(3*(512*v+145)+1)) (7*h+14) := by
  rw [show 7*h+17 = 12+(7*h+5) by omega,
      show 7*h+14 = 9+(7*h+5) by omega,
      run_add (.p5,3*(8*(512*v+145)+2)) 12 (7*h+5),n03_difference_source_initialization,
      run_add (.p1,3*(3*(512*v+145)+1)) 9 (7*h+5),n03_difference_alternate_initialization]
  have upper : 19683*v+5589 = (19683*v+5586)+3 := by omega
  rw [upper]
  exact n03_difference_repeated h (19683*v+5586) q eq terminal

theorem n03_difference_progress (v : Nat) (guard : N03DifferenceGuard v) :
    Progress .p5 (8*(512*v+145)+2) := by
  obtain ⟨h,q,eq,terminal⟩ := guard
  right
  refine ⟨.p1,3*(512*v+145)+1,7*h+17,7*h+14,?_,?_,?_,n03_difference_merger v h q eq terminal⟩
  · simp [SectionPhase]
  · omega
  · simp only [rank,weight]; omega

end Collatz.SevenStepCertificate
