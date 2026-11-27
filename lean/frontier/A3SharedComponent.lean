import Collatz.SevenStepCertificate.Basic

/-!
Unbounded partial A3 merger obtained by exiting a shared-counter component.
Uses only the pinned, committed fixed-word model in Basic.lean. Every finite
path is proved arithmetically and the number of seven-step pumps is arbitrary.
The displayed guard is sufficient, not an exhaustive description of A3.
-/
namespace Collatz.SevenStepCertificate.SharedA3
theorem entry_upper (r : Nat) :
    run (.p3,192*r+57) 6 = (.p2,243*r+74) := by
  have h0 : next (.p3,192*r+57) = (.p4,288*r+86) := by
    apply Prod.ext
    · rfl
    · simp only [next,update,T]; split <;> omega
  have h1 : next (.p4,288*r+86) = (.p5,432*r+129) := by
    apply Prod.ext
    · rfl
    · simp only [next,update,U]; split <;> omega
  have h2 : next (.p5,432*r+129) = (.p6,216*r+65) := by
    apply Prod.ext
    · rfl
    · simp only [next,update,U]; split <;> omega
  have h3 : next (.p6,216*r+65) = (.p0,324*r+98) := by
    apply Prod.ext
    · rfl
    · simp only [next,update,T]; split <;> omega
  have h4 : next (.p0,324*r+98) = (.p1,486*r+147) := by
    apply Prod.ext
    · rfl
    · simp only [next,update,U]; split <;> omega
  have h5 : next (.p1,486*r+147) = (.p2,243*r+74) := by
    apply Prod.ext
    · rfl
    · simp only [next,update,U]; split <;> omega
  simp only [run,h0,h1,h2,h3,h4,h5]
theorem entry_lower (r : Nat) :
    run (.p5,144*r+42) 4 = (.p2,243*r+72) := by
  have h0 : next (.p5,144*r+42) = (.p6,216*r+63) := by
    apply Prod.ext
    · rfl
    · simp only [next,update,U]; split <;> omega
  have h1 : next (.p6,216*r+63) = (.p0,324*r+95) := by
    apply Prod.ext
    · rfl
    · simp only [next,update,T]; split <;> omega
  have h2 : next (.p0,324*r+95) = (.p1,162*r+48) := by
    apply Prod.ext
    · rfl
    · simp only [next,update,U]; split <;> omega
  have h3 : next (.p1,162*r+48) = (.p2,243*r+72) := by
    apply Prod.ext
    · rfl
    · simp only [next,update,U]; split <;> omega
  simp only [run,h0,h1,h2,h3]
theorem pump_lower (r : Nat) :
    run (.p2,31104*r+12708) 7 = (.p2,59049*r+24129) := by
  have h0 : next (.p2,31104*r+12708) = (.p3,46656*r+19062) := by
    apply Prod.ext
    · rfl
    · simp only [next,update,U]; split <;> omega
  have h1 : next (.p3,46656*r+19062) = (.p4,23328*r+9531) := by
    apply Prod.ext
    · rfl
    · simp only [next,update,T]; split <;> omega
  have h2 : next (.p4,23328*r+9531) = (.p5,11664*r+4766) := by
    apply Prod.ext
    · rfl
    · simp only [next,update,U]; split <;> omega
  have h3 : next (.p5,11664*r+4766) = (.p6,17496*r+7149) := by
    apply Prod.ext
    · rfl
    · simp only [next,update,U]; split <;> omega
  have h4 : next (.p6,17496*r+7149) = (.p0,26244*r+10724) := by
    apply Prod.ext
    · rfl
    · simp only [next,update,T]; split <;> omega
  have h5 : next (.p0,26244*r+10724) = (.p1,39366*r+16086) := by
    apply Prod.ext
    · rfl
    · simp only [next,update,U]; split <;> omega
  have h6 : next (.p1,39366*r+16086) = (.p2,59049*r+24129) := by
    apply Prod.ext
    · rfl
    · simp only [next,update,U]; split <;> omega
  simp only [run,h0,h1,h2,h3,h4,h5,h6]
theorem pump_upper (r : Nat) :
    run (.p2,31104*r+12710) 7 = (.p2,59049*r+24131) := by
  have h0 : next (.p2,31104*r+12710) = (.p3,46656*r+19065) := by
    apply Prod.ext
    · rfl
    · simp only [next,update,U]; split <;> omega
  have h1 : next (.p3,46656*r+19065) = (.p4,69984*r+28598) := by
    apply Prod.ext
    · rfl
    · simp only [next,update,T]; split <;> omega
  have h2 : next (.p4,69984*r+28598) = (.p5,104976*r+42897) := by
    apply Prod.ext
    · rfl
    · simp only [next,update,U]; split <;> omega
  have h3 : next (.p5,104976*r+42897) = (.p6,52488*r+21449) := by
    apply Prod.ext
    · rfl
    · simp only [next,update,U]; split <;> omega
  have h4 : next (.p6,52488*r+21449) = (.p0,78732*r+32174) := by
    apply Prod.ext
    · rfl
    · simp only [next,update,T]; split <;> omega
  have h5 : next (.p0,78732*r+32174) = (.p1,118098*r+48261) := by
    apply Prod.ext
    · rfl
    · simp only [next,update,U]; split <;> omega
  have h6 : next (.p1,118098*r+48261) = (.p2,59049*r+24131) := by
    apply Prod.ext
    · rfl
    · simp only [next,update,U]; split <;> omega
  simp only [run,h0,h1,h2,h3,h4,h5,h6]
theorem terminal_lower (r : Nat) :
    run (.p2,62208*r+20484) 8 = (.p3,19683*r+6483) := by
  have h0 : next (.p2,62208*r+20484) = (.p3,93312*r+30726) := by
    apply Prod.ext
    · rfl
    · simp only [next,update,U]; split <;> omega
  have h1 : next (.p3,93312*r+30726) = (.p4,46656*r+15363) := by
    apply Prod.ext
    · rfl
    · simp only [next,update,T]; split <;> omega
  have h2 : next (.p4,46656*r+15363) = (.p5,23328*r+7682) := by
    apply Prod.ext
    · rfl
    · simp only [next,update,U]; split <;> omega
  have h3 : next (.p5,23328*r+7682) = (.p6,34992*r+11523) := by
    apply Prod.ext
    · rfl
    · simp only [next,update,U]; split <;> omega
  have h4 : next (.p6,34992*r+11523) = (.p0,52488*r+17285) := by
    apply Prod.ext
    · rfl
    · simp only [next,update,T]; split <;> omega
  have h5 : next (.p0,52488*r+17285) = (.p1,26244*r+8643) := by
    apply Prod.ext
    · rfl
    · simp only [next,update,U]; split <;> omega
  have h6 : next (.p1,26244*r+8643) = (.p2,13122*r+4322) := by
    apply Prod.ext
    · rfl
    · simp only [next,update,U]; split <;> omega
  have h7 : next (.p2,13122*r+4322) = (.p3,19683*r+6483) := by
    apply Prod.ext
    · rfl
    · simp only [next,update,U]; split <;> omega
  simp only [run,h0,h1,h2,h3,h4,h5,h6,h7]
theorem terminal_upper (r : Nat) :
    run (.p2,62208*r+20486) 8 = (.p3,19683*r+6483) := by
  have h0 : next (.p2,62208*r+20486) = (.p3,93312*r+30729) := by
    apply Prod.ext
    · rfl
    · simp only [next,update,U]; split <;> omega
  have h1 : next (.p3,93312*r+30729) = (.p4,139968*r+46094) := by
    apply Prod.ext
    · rfl
    · simp only [next,update,T]; split <;> omega
  have h2 : next (.p4,139968*r+46094) = (.p5,209952*r+69141) := by
    apply Prod.ext
    · rfl
    · simp only [next,update,U]; split <;> omega
  have h3 : next (.p5,209952*r+69141) = (.p6,104976*r+34571) := by
    apply Prod.ext
    · rfl
    · simp only [next,update,U]; split <;> omega
  have h4 : next (.p6,104976*r+34571) = (.p0,157464*r+51857) := by
    apply Prod.ext
    · rfl
    · simp only [next,update,T]; split <;> omega
  have h5 : next (.p0,157464*r+51857) = (.p1,78732*r+25929) := by
    apply Prod.ext
    · rfl
    · simp only [next,update,U]; split <;> omega
  have h6 : next (.p1,78732*r+25929) = (.p2,39366*r+12965) := by
    apply Prod.ext
    · rfl
    · simp only [next,update,U]; split <;> omega
  have h7 : next (.p2,39366*r+12965) = (.p3,19683*r+6483) := by
    apply Prod.ext
    · rfl
    · simp only [next,update,U]; split <;> omega
  simp only [run,h0,h1,h2,h3,h4,h5,h6,h7]

theorem multiplier_mod_eight (h q : Nat) :
    (243^h*q)%8 = (3^h*q)%8 := by
  simp [Nat.mul_mod,Nat.pow_mod]

/-- Arbitrarily many seven-tick pumps, followed by an eight-tick merger.
The parameter u, not a bounded seed list, is universally quantified. -/
theorem paired_pumped_merger (h u q : Nat)
    (equation : 115*u+36 = 2^(7*h+5)*q)
    (terminal : (243^h*q)%8 = 7) :
    run (.p2,243*u+72) (7*h+8) = run (.p2,243*u+74) (7*h+8) := by
  induction h generalizing u q with
  | zero =>
    change 115*u+36 = 32*q at equation
    simp only [Nat.pow_zero,Nat.one_mul] at terminal
    have hu : u = 256*(u/256)+84 := by omega
    have low : 243*u+72 = 62208*(u/256)+20484 := by omega
    have high : 243*u+74 = 62208*(u/256)+20486 := by omega
    change run (.p2,243*u+72) 8 = run (.p2,243*u+74) 8
    rw [low,high,terminal_lower,terminal_upper]
  | succ h ih =>
    have power : 2^(7*(h+1)+5) = 128*2^(7*h+5) := by
      rw [show 7*(h+1)+5 = (7*h+5)+7 by omega,Nat.pow_add]
      change 2^(7*h+5)*128 = 128*2^(7*h+5)
      omega
    rw [power] at equation
    simp only [Nat.mul_assoc] at equation
    let r := u/128
    have hu : u = 128*r+52 := by dsimp [r]; omega
    have reduced : 115*r+47 = 2^(7*h+5)*q := by omega
    have nextEquation : 115*(243*r+99)+36 = 2^(7*h+5)*(243*q) := by
      calc
        _ = 243*(115*r+47) := by omega
        _ = 243*(2^(7*h+5)*q) := by rw [reduced]
        _ = _ := by ac_rfl
    have nextTerminal : (243^h*(243*q))%8 = 7 := by
      simpa only [Nat.pow_succ,Nat.mul_assoc] using terminal
    have low : run (.p2,243*u+72) 7 = (.p2,243*(243*r+99)+72) := by
      have hs : 243*u+72 = 31104*r+12708 := by omega
      have ht : 243*(243*r+99)+72 = 59049*r+24129 := by omega
      rw [hs,ht]
      exact pump_lower r
    have high : run (.p2,243*u+74) 7 = (.p2,243*(243*r+99)+74) := by
      have hs : 243*u+74 = 31104*r+12710 := by omega
      have ht : 243*(243*r+99)+74 = 59049*r+24131 := by omega
      rw [hs,ht]
      exact pump_upper r
    rw [show 7*(h+1)+8 = 7+(7*h+8) by omega,
        run_add (.p2,243*u+72) 7 (7*h+8),
        run_add (.p2,243*u+74) 7 (7*h+8),low,high]
    exact ih (243*r+99) (243*q) nextEquation nextTerminal

/-- New guarded A3 reduction: t=16*u+4. The alternate has section parameter
3*t+2 at phase five, and is smaller under the committed common W rank. -/
theorem a3_unbounded_merger (u h q : Nat)
    (equation : 115*u+36 = 2^(7*h+5)*q)
    (terminal : (3^h*q)%8 = 7) :
    run (.p3,192*u+57) (7*h+14) = run (.p5,144*u+42) (7*h+12) := by
  have meet := paired_pumped_merger h u q equation
    (by simpa only [multiplier_mod_eight] using terminal)
  rw [show 7*h+14 = 6+(7*h+8) by omega,
      show 7*h+12 = 4+(7*h+8) by omega,
      run_add (.p3,192*u+57) 6 (7*h+8),
      run_add (.p5,144*u+42) 4 (7*h+8),entry_upper,entry_lower]
  exact meet.symm

theorem original_W_gap (u : Nat) :
    4*(64*u+19) = 5*(48*u+14)+(16*u+6) := by omega

theorem alternate_original_W_smaller (u : Nat) :
    5*(48*u+14) < 4*(64*u+19) := by omega

theorem guarded_capture_transfer (u h q : Nat)
    (equation : 115*u+36 = 2^(7*h+5)*q)
    (terminal : (3^h*q)%8 = 7)
    (smallerCaptured : Captured (.p5,144*u+42)) :
    Captured (.p3,192*u+57) :=
  captured_of_coalescence _ _ (7*h+14) (7*h+12)
    (a3_unbounded_merger u h q equation terminal) smallerCaptured

/-- Exact signed-physical merger, with the independent clock phases retained.
Physical launches are n=192*u+57 at phase3 and n=144*u+41 at phase5. -/
theorem signed_physical_merger (u h q : Nat)
    (equation : 115*u+36 = 2^(7*h+5)*q)
    (terminal : (3^h*q)%8 = 7) :
    physicalRun (decode (.p3,192*u+57)) (7*h+14) =
      physicalRun (decode (.p5,144*u+42)) (7*h+12) := by
  rw [← run_faithful (.p3,192*u+57) (by dsimp; omega),
      ← run_faithful (.p5,144*u+42) (by dsimp; omega),
      a3_unbounded_merger u h q equation terminal]

end Collatz.SevenStepCertificate.SharedA3

#print axioms Collatz.SevenStepCertificate.SharedA3.paired_pumped_merger
#print axioms Collatz.SevenStepCertificate.SharedA3.a3_unbounded_merger
#print axioms Collatz.SevenStepCertificate.SharedA3.alternate_original_W_smaller
#print axioms Collatz.SevenStepCertificate.SharedA3.guarded_capture_transfer
#print axioms Collatz.SevenStepCertificate.SharedA3.signed_physical_merger
