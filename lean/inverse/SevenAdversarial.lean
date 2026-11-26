import Collatz.SevenRows
import Collatz.CycleMultiplier

open Collatz.SevenStep
set_option maxRecDepth 10000

/- Kernel-evaluated negative fixtures for the physical row verifier.
   These include a sign error too large for fixed-width integer arithmetic. -/
private def valid : Row := ⟨5,3,2,1,27,7⟩

example : valid.check = true := by decide +kernel
example : ({valid with slope := 26}).check = false := by decide +kernel
example : ({valid with offset := 8}).check = false := by decide +kernel
example : ({valid with source := 3}).check = false := by decide +kernel
example : ({valid with target := 2}).check = false := by decide +kernel
example : ({valid with ticks := 2}).check = false := by decide +kernel
example : ({valid with base := 3}).check = false := by decide +kernel
example : ({valid with base := 0}).check = false := by decide +kernel
example : ({valid with base := 10}).check = false := by decide +kernel
example : ({valid with offset := 2^96+7}).check = false := by decide +kernel

/- A sound individual row still needs its domain-coverage check. -/
example : ((rows.erase valid).filter (Row.applies 5 2)).length = 0 := by decide +kernel
example : ((valid::rows).filter (Row.applies 5 2)).length = 2 := by decide +kernel
example : (([valid] : List Row).filter (Row.applies 1 2)).length = 0 := by decide +kernel
example : (([] : List Row).filter (Row.applies 5 2)).length = 0 := by decide +kernel

/- A same-height hit at the wrong phase cannot satisfy the cycle predicate. -/
example : OnCycle (5,2) ∧ ¬OnCycle (4,2) := by unfold OnCycle; decide


namespace AdmissibilityFixtures
open Collatz.Physical

private def wide : Word := ⟨1, fun i => if i = 0 then 2 else -1⟩
private def level (i : Clock wide) : Int := if i = 0 then 0 else 1

example : Admissible wide :=
  admissible_of_floor wide level (by unfold Binary; decide) (by unfold Floor; decide)
example : ¬Conservative wide := by unfold Conservative; decide
example : ¬UnitAlphabet wide := by unfold UnitAlphabet; decide

private def consecutiveNegatives : Word := ⟨3, fun i => if i < 2 then 1 else -1⟩
example : Conservative consecutiveNegatives := by unfold Conservative; decide
example : ¬Admissible consecutiveNegatives := by
  intro a
  have bad : 0 ≤ (run (step consecutiveNegatives) 2 (2,2)).2 := a 2 2 (by decide) 2
  exact (by decide : ¬0 ≤ (run (step consecutiveNegatives) 2 (2,2)).2) bad

example : shortcut (-3) = -4 ∧ shortcut (-2) = -1 := by decide
end AdmissibilityFixtures
