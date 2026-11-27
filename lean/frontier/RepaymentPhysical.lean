import RepaymentBound

/-! Link the universal rational bound to the already verified physical macros. -/
namespace FamilyCoverRepayment
open FamilyCoverTheory FamilyCoverComposition

theorem grow_cast (t : Int) (guard : Macro.grow.guard t) :
    (Macro.grow.apply t : Rat) = g*((t:Rat)+c)-c := by
  have heInt : 128*Macro.grow.apply t = 243*t+52 := by
    simp only [Macro.apply,Macro.guard] at *
    omega
  have he := congrArg (fun z : Int => (z : Rat)) heInt
  simp only [Rat.intCast_add,Rat.intCast_mul,Rat.intCast_ofNat] at he
  have gv : 128*g=243 := by decide +kernel
  have cv : 115*c=52 := by decide +kernel
  grind

theorem repay_cast (t : Int) (guard : Macro.repay.guard t) :
    (Macro.repay.apply t : Rat) = h*((t:Rat)-d)+d := by
  have heInt : 128*Macro.repay.apply t = 9*t+29 := by
    simp only [Macro.apply,Macro.guard] at *
    omega
  have he := congrArg (fun z : Int => (z : Rat)) heInt
  simp only [Rat.intCast_add,Rat.intCast_mul,Rat.intCast_ofNat] at he
  have hv : 128*h=9 := by decide +kernel
  have dv : 119*d=29 := by decide +kernel
  grind

theorem apply_append (first second : List Macro) (t : Int) :
    applyMacros (first++second) t = applyMacros second (applyMacros first t) := by
  induction first generalizing t with
  | nil => rfl
  | cons m rest ih => simpa only [List.cons_append,applyMacros] using ih (m.apply t)

theorem legal_append (first second : List Macro) (t : Int) :
    LegalMacros (first++second) t ↔
      LegalMacros first t ∧ LegalMacros second (applyMacros first t) := by
  induction first generalizing t with
  | nil => simp only [List.nil_append,LegalMacros,applyMacros,true_and]
  | cons m rest ih =>
    simp only [List.cons_append,LegalMacros,applyMacros,ih,and_assoc]

theorem growth_closed (k : Nat) (t : Int)
    (legal : LegalMacros (List.replicate k Macro.grow) t) :
    (applyMacros (List.replicate k Macro.grow) t : Rat) = g^k*((t:Rat)+c)-c := by
  induction k generalizing t with
  | zero => simp only [List.replicate_zero,applyMacros,Rat.pow_zero,Rat.one_mul]; grind
  | succ k ih =>
    simp only [List.replicate_succ,LegalMacros,applyMacros] at *
    rw [ih (Macro.grow.apply t) legal.2,grow_cast t legal.1,Rat.pow_succ]
    grind

theorem repayment_closed (ell : Nat) (t : Int)
    (legal : LegalMacros (List.replicate ell Macro.repay) t) :
    (applyMacros (List.replicate ell Macro.repay) t : Rat) = h^ell*((t:Rat)-d)+d := by
  induction ell generalizing t with
  | zero => simp only [List.replicate_zero,applyMacros,Rat.pow_zero,Rat.one_mul]; grind
  | succ ell ih =>
    simp only [List.replicate_succ,LegalMacros,applyMacros] at *
    rw [ih (Macro.repay.apply t) legal.2,repay_cast t legal.1,Rat.pow_succ]
    grind

def repaymentWord (k ell : Nat) : List Macro :=
  List.replicate k Macro.grow ++ List.replicate ell Macro.repay

/-- The closed rational endpoint equals the exact integer macro endpoint. -/
theorem repayment_word_closed (k ell : Nat) (t : Int)
    (legal : LegalMacros (repaymentWord k ell) t) :
    (applyMacros (repaymentWord k ell) t : Rat) = endpoint k ell (t:Rat) := by
  have legal' := (legal_append (List.replicate k Macro.grow)
    (List.replicate ell Macro.repay) t).mp legal
  unfold repaymentWord
  rw [apply_append,repayment_closed ell _ legal'.2,growth_closed k t legal'.1]
  unfold endpoint
  grind

/-- Every legal growth block followed by enough repayment macros strictly
reduces the original B1 parameter. Intermediate growth is permitted. -/
theorem repayment_word_decreases (k ell : Nat) (hell : 1 ≤ ell) (hke : k ≤ 4*ell)
    (t : Int) (ht : 8 ≤ t) (legal : LegalMacros (repaymentWord k ell) t) :
    applyMacros (repaymentWord k ell) t < t := by
  have htRat : (8:Rat) ≤ (t:Rat) := (Rat.intCast_le_intCast).mpr ht
  have small := endpoint_decreases k ell hell hke (t:Rat) htRat
  rw [←repayment_word_closed k ell t legal] at small
  exact (Rat.intCast_lt_intCast).mp small

/-- In particular, ceil(k/4) repayments suffice uniformly for every k≥1. -/
theorem ceil_repayment_word_decreases (k : Nat) (hk : 1 ≤ k)
    (t : Int) (ht : 8 ≤ t) (legal : LegalMacros (repaymentWord k ((k+3)/4)) t) :
    applyMacros (repaymentWord k ((k+3)/4)) t < t := by
  exact repayment_word_decreases k ((k+3)/4) (by omega) (by omega) t ht legal

theorem macro_positive (m : Macro) (t : Int) (ht : 1 ≤ t) (guard : m.guard t) :
    1 ≤ m.apply t := by
  cases m <;> simp only [Macro.guard,Macro.apply] at * <;> omega

theorem macros_positive (word : List Macro) (t : Int) (ht : 1 ≤ t)
    (legal : LegalMacros word t) : 1 ≤ applyMacros word t := by
  induction word generalizing t with
  | nil => exact ht
  | cons m rest ih =>
    exact ih (m.apply t) (macro_positive m t ht legal.1) legal.2

/-- The small-input restriction in the rational estimate is automatic on every
positive legal nonempty growth-and-repayment word. -/
theorem legal_repayment_input_ge_eight (k ell : Nat) (hk : 1 ≤ k) (hell : 1 ≤ ell)
    (t : Int) (ht : 1 ≤ t) (legal : LegalMacros (repaymentWord k ell) t) : 8 ≤ t := by
  cases k with
  | zero => omega
  | succ k =>
    simp only [repaymentWord,List.replicate_succ,List.cons_append,LegalMacros] at legal
    have first : t%128=4 := legal.1
    by_cases good : 8 ≤ t
    · exact good
    · have t4 : t=4 := by omega
      subst t
      have tail := legal.2
      have value : Macro.grow.apply 4=8 := rfl
      rw [value] at tail
      cases k with
      | zero =>
        cases ell with
        | zero => omega
        | succ ell =>
          simp only [List.replicate_zero,List.nil_append,List.replicate_succ,LegalMacros] at tail
          have bad : (8:Int)%128=11 := tail.1
          omega
      | succ k =>
        simp only [List.replicate_succ,List.cons_append,LegalMacros] at tail
        have bad : (8:Int)%128=4 := tail.1
        omega

/-- Complete uniform certificate: exact physical return, positive smaller B1
parameter, strict original W-rank decrease, safety, and capture equivalence.
The sole family-specific premise is that the finite macro word is legal. -/
theorem certified_ceil_repayment (k : Nat) (hk : 1 ≤ k)
    (t : Int) (ht : 1 ≤ t) (legal : LegalMacros (repaymentWord k ((k+3)/4)) t) :
    let s := applyMacros (repaymentWord k ((k+3)/4)) t
    run (b1 t) (7*(k+(k+3)/4)) = b1 s ∧
    1 ≤ s ∧ s<t ∧ rank .p1 (2*s)<rank .p1 (2*t) ∧
    (∀ j, Safe (run (b1 t) j)) ∧ (Captured (b1 t) ↔ Captured (b1 s)) := by
  dsimp only
  have gt8 := legal_repayment_input_ge_eight k ((k+3)/4) hk (by omega) t ht legal
  have smaller := ceil_repayment_word_decreases k hk t gt8 legal
  have physical := macros_physical (repaymentWord k ((k+3)/4)) t legal
  have lengths : (repaymentWord k ((k+3)/4)).length=k+(k+3)/4 := by
    simp [repaymentWord]
  rw [lengths] at physical
  refine ⟨physical,macros_positive _ t ht legal,smaller,?_,?_,macros_capture_iff _ t legal⟩
  · simp only [rank,sectionWeight]
    omega
  · intro j
    apply safe_run
    apply section_safe
    omega

end FamilyCoverRepayment

#print axioms FamilyCoverRepayment.repayment_word_closed
#print axioms FamilyCoverRepayment.ceil_repayment_word_decreases

#print axioms FamilyCoverRepayment.certified_ceil_repayment
