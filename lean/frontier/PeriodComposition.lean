import FamilyCoverTheory

/-! New compositional B1 self-descent. The physical recurrence, safe-domain
and capture definitions are imported unchanged from FamilyCoverTheory.
These are identities and strict endpoint reductions, not global capture.
-/
namespace FamilyCoverComposition
open FamilyCoverTheory

def b1 (t : Int) : State := launch .p1 (2*t)

theorem growing_period (v : Int) :
    run (b1 (128*v+4)) 7 = b1 (243*v+8) := by
  have hs : b1 (128*v+4) = (.p1,768*v+23) := by
    apply Prod.ext
    · rfl
    · simp only [b1,launch,height]; omega
  have he : b1 (243*v+8) = (.p1,1458*v+47) := by
    apply Prod.ext
    · rfl
    · simp only [b1,launch,height]; omega
  rw [hs,he]
  have h0 : step (.p1,768*v+23) = (.p2,1152*v+35) := by
    apply Prod.ext
    · rfl
    · simp only [step,shortcut,impulse]; split <;> omega
  have h1 : step (.p2,1152*v+35) = (.p3,1728*v+54) := by
    apply Prod.ext
    · rfl
    · simp only [step,shortcut,impulse]; split <;> omega
  have h2 : step (.p3,1728*v+54) = (.p4,864*v+26) := by
    apply Prod.ext
    · rfl
    · simp only [step,shortcut,impulse]; split <;> omega
  have h3 : step (.p4,864*v+26) = (.p5,432*v+13) := by
    apply Prod.ext
    · rfl
    · simp only [step,shortcut,impulse]; split <;> omega
  have h4 : step (.p5,432*v+13) = (.p6,648*v+21) := by
    apply Prod.ext
    · rfl
    · simp only [step,shortcut,impulse]; split <;> omega
  have h5 : step (.p6,648*v+21) = (.p0,972*v+31) := by
    apply Prod.ext
    · rfl
    · simp only [step,shortcut,impulse]; split <;> omega
  have h6 : step (.p0,972*v+31) = (.p1,1458*v+47) := by
    apply Prod.ext
    · rfl
    · simp only [step,shortcut,impulse]; split <;> omega
  simp only [run,h0,h1,h2,h3,h4,h5,h6]

theorem contracting_period (v : Int) :
    run (b1 (128*v+11)) 7 = b1 (9*v+1) := by
  have hs : b1 (128*v+11) = (.p1,768*v+65) := by
    apply Prod.ext
    · rfl
    · simp only [b1,launch,height]; omega
  have he : b1 (9*v+1) = (.p1,54*v+5) := by
    apply Prod.ext
    · rfl
    · simp only [b1,launch,height]; omega
  rw [hs,he]
  have h0 : step (.p1,768*v+65) = (.p2,1152*v+98) := by
    apply Prod.ext
    · rfl
    · simp only [step,shortcut,impulse]; split <;> omega
  have h1 : step (.p2,1152*v+98) = (.p3,576*v+50) := by
    apply Prod.ext
    · rfl
    · simp only [step,shortcut,impulse]; split <;> omega
  have h2 : step (.p3,576*v+50) = (.p4,288*v+24) := by
    apply Prod.ext
    · rfl
    · simp only [step,shortcut,impulse]; split <;> omega
  have h3 : step (.p4,288*v+24) = (.p5,144*v+12) := by
    apply Prod.ext
    · rfl
    · simp only [step,shortcut,impulse]; split <;> omega
  have h4 : step (.p5,144*v+12) = (.p6,72*v+7) := by
    apply Prod.ext
    · rfl
    · simp only [step,shortcut,impulse]; split <;> omega
  have h5 : step (.p6,72*v+7) = (.p0,108*v+10) := by
    apply Prod.ext
    · rfl
    · simp only [step,shortcut,impulse]; split <;> omega
  have h6 : step (.p0,108*v+10) = (.p1,54*v+5) := by
    apply Prod.ext
    · rfl
    · simp only [step,shortcut,impulse]; split <;> omega
  simp only [run,h0,h1,h2,h3,h4,h5,h6]

inductive Macro where
  | grow | repay
  deriving DecidableEq

def Macro.apply : Macro → Int → Int
  | .grow, t => (243*t+52)/128
  | .repay, t => (9*t+29)/128

def Macro.guard : Macro → Int → Prop
  | .grow, t => t%128 = 4
  | .repay, t => t%128 = 11

theorem macro_physical (m : Macro) (t : Int) (guard : m.guard t) :
    run (b1 t) 7 = b1 (m.apply t) := by
  cases m with
  | grow =>
    change t%128 = 4 at guard
    have hs : 128*(t/128)+4 = t := by omega
    have ht : 243*(t/128)+8 = (243*t+52)/128 := by omega
    have h := growing_period (t/128)
    simpa only [hs,ht,Macro.apply] using h
  | repay =>
    change t%128 = 11 at guard
    have hs : 128*(t/128)+11 = t := by omega
    have ht : 9*(t/128)+1 = (9*t+29)/128 := by omega
    have h := contracting_period (t/128)
    simpa only [hs,ht,Macro.apply] using h

def applyMacros : List Macro → Int → Int
  | [], t => t
  | m::rest, t => applyMacros rest (m.apply t)

def LegalMacros : List Macro → Int → Prop
  | [], _ => True
  | m::rest, t => m.guard t ∧ LegalMacros rest (m.apply t)

/-- Every legal finite macro word, of arbitrary length, follows the exact
signed physical recurrence. No applicability or rank-drop premise is hidden. -/
theorem macros_physical (word : List Macro) (t : Int) (legal : LegalMacros word t) :
    run (b1 t) (7*word.length) = b1 (applyMacros word t) := by
  induction word generalizing t with
  | nil => rfl
  | cons m rest ih =>
    obtain ⟨guard,tail⟩ := legal
    have clock : 7*(m::rest).length = 7+7*rest.length := by simp; omega
    rw [clock,run_add,macro_physical m t guard]
    exact ih (m.apply t) tail

theorem macros_capture_iff (word : List Macro) (t : Int) (legal : LegalMacros word t) :
    Captured (b1 t) ↔ Captured (b1 (applyMacros word t)) :=
  captured_iff_of_run (macros_physical word t legal)

theorem growing_period_increases (v : Int) (hv : 0 ≤ v) :
    128*v+4 < 243*v+8 := by omega

theorem contracting_period_decreases (v : Int) (hv : 0 ≤ v) :
    9*v+1 < 128*v+11 := by omega

theorem three_growths_one_repayment (v : Int) :
    run (b1 (268435456*v+89557508)) 28 = b1 (129140163*v+43084738) := by
  have h0 := growing_period (2097152*v+699668)
  have s0 : 128*(2097152*v+699668)+4 = 268435456*v+89557508 := by omega
  have t0 : 243*(2097152*v+699668)+8 = 509607936*v+170019332 := by omega
  rw [s0,t0] at h0
  have h1 := growing_period (3981312*v+1328276)
  have s1 : 128*(3981312*v+1328276)+4 = 509607936*v+170019332 := by omega
  have t1 : 243*(3981312*v+1328276)+8 = 967458816*v+322771076 := by omega
  rw [s1,t1] at h1
  have h2 := growing_period (7558272*v+2521649)
  have s2 : 128*(7558272*v+2521649)+4 = 967458816*v+322771076 := by omega
  have t2 : 243*(7558272*v+2521649)+8 = 1836660096*v+612760715 := by omega
  rw [s2,t2] at h2
  have h3 := contracting_period (14348907*v+4787193)
  have s3 : 128*(14348907*v+4787193)+11 = 1836660096*v+612760715 := by omega
  have t3 : 9*(14348907*v+4787193)+1 = 129140163*v+43084738 := by omega
  rw [s3,t3] at h3
  rw [run_add _ 7 21,h0,run_add _ 7 14,h1,run_add _ 7 7,h2,h3]

theorem three_growths_one_repayment_parameter_gap (v : Int) :
    (268435456*v+89557508)-(129140163*v+43084738) = 139295293*v+46472770 := by
  omega

theorem three_growths_one_repayment_smaller (v : Int) (hv : 0 ≤ v) :
    1 ≤ 129140163*v+43084738 ∧
    129140163*v+43084738 < 268435456*v+89557508 := by omega

theorem three_growths_one_repayment_W_gap (v : Int) :
    rank .p1 (2*(268435456*v+89557508)) -
    rank .p1 (2*(129140163*v+43084738)) = 1114362344*v+371782160 := by
  simp only [rank,sectionWeight]
  omega

theorem three_growths_one_repayment_safe (v : Int) (hv : 0 ≤ v) (k : Nat) :
    Safe (run (b1 (268435456*v+89557508)) k) := by
  apply safe_run
  apply section_safe
  omega

theorem three_growths_one_repayment_capture_iff (v : Int) :
    Captured (b1 (268435456*v+89557508)) ↔
    Captured (b1 (129140163*v+43084738)) :=
  captured_iff_of_run (three_growths_one_repayment v)

/-- The CRT restriction used for the separately checked main-screen comparison.
No screen predicate is assumed or certified by this dynamical identity. -/
theorem comparison_ray (w : Int) :
    run (b1 (5283615080448*w+89557508)) 28 =
      b1 (2541865828329*w+43084738) := by
  have h := three_growths_one_repayment (19683*w)
  have hs : 268435456*(19683*w)+89557508 = 5283615080448*w+89557508 := by omega
  have ht : 129140163*(19683*w)+43084738 = 2541865828329*w+43084738 := by omega
  simpa only [hs,ht] using h

theorem comparison_ray_smaller (w : Int) (hw : 0 ≤ w) :
    1 ≤ 2541865828329*w+43084738 ∧
    2541865828329*w+43084738 < 5283615080448*w+89557508 := by omega

/-- These exact residues exclude all clauses of the specified B1SelfCertified
bank: both recursive clauses require3|t, the shadow is odd, and the28
one-period residue list omits4. The list itself is not imported here. -/
theorem comparison_ray_residues (w : Int) :
    (5283615080448*w+89557508)%3 = 2 ∧
    (5283615080448*w+89557508)%128 = 4 ∧
    (5283615080448*w+89557508)%2 = 0 := by omega

end FamilyCoverComposition

#print axioms FamilyCoverComposition.growing_period
#print axioms FamilyCoverComposition.macros_physical
#print axioms FamilyCoverComposition.macros_capture_iff
#print axioms FamilyCoverComposition.contracting_period
#print axioms FamilyCoverComposition.three_growths_one_repayment
#print axioms FamilyCoverComposition.three_growths_one_repayment_smaller
#print axioms FamilyCoverComposition.three_growths_one_repayment_W_gap
#print axioms FamilyCoverComposition.three_growths_one_repayment_safe
#print axioms FamilyCoverComposition.three_growths_one_repayment_capture_iff
#print axioms FamilyCoverComposition.comparison_ray
#print axioms FamilyCoverComposition.comparison_ray_residues
