import PeriodComposition
import Init.Grind.Ordered.Rat

/-! Uniform rational debt repayment for the G/H macro family. -/
namespace FamilyCoverRepayment

open FamilyCoverTheory FamilyCoverComposition

def g : Rat := 243/128
def h : Rat := 9/128
def c : Rat := 52/115
def d : Rat := 29/119
def alpha : Rat := 31381059609/34359738368

theorem pow_add (a : Rat) (m n : Nat) : a^(m+n)=a^m*a^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ex : m+(n+1)=m+n+1 := by omega
    change a^(m+(n+1))=a^m*a^(n+1)
    rw [ex,Rat.pow_succ a (m+n),ih,Rat.pow_succ a n,Rat.mul_assoc]

theorem pow_mono (a : Rat) (ha : 1 ≤ a) {k l : Nat} (hkl : k ≤ l) : a^k ≤ a^l := by
  have ha0 : 0 ≤ a := by grind
  have step : ∀ n, a^n ≤ a^(n+1) := by
    intro n
    rw [Rat.pow_succ]
    have nn : 0 ≤ a^n := Rat.pow_nonneg ha0
    have m := Rat.mul_le_mul_of_nonneg_left ha nn
    simpa using m
  induction l with
  | zero =>
    have hk : k=0 := by omega
    subst k
    exact Rat.le_refl
  | succ l ih =>
    by_cases eq : k=l+1
    · subst k; exact Rat.le_refl
    · exact Rat.le_trans (ih (by omega)) (step l)

theorem pow_le_one (a : Rat) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (n : Nat) : a^n ≤ 1 := by
  induction n with
  | zero => exact Rat.le_refl
  | succ n ih =>
    rw [Rat.pow_succ]
    have hh := Rat.mul_le_mul_of_nonneg_right ih ha0
    have hh' : a^n*a ≤ a := by simpa using hh
    exact Rat.le_trans hh' ha1

theorem pow_le_self (a : Rat) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (n : Nat)
    (hn : 1 ≤ n) : a^n ≤ a := by
  cases n with
  | zero => omega
  | succ n =>
    rw [Rat.pow_succ]
    have hh := Rat.mul_le_mul_of_nonneg_right (pow_le_one a ha0 ha1 n) ha0
    simpa using hh

theorem packet_power (ell : Nat) : g^(4*ell)*h^ell=alpha^ell := by
  have constant : g^4*h=alpha := by decide +kernel
  induction ell with
  | zero => simp
  | succ ell ih =>
    have ex : 4*(ell+1)=4*ell+4 := by omega
    calc
      g^(4*(ell+1))*h^(ell+1) = g^(4*ell)*g^4*(h^ell*h) := by
        rw [ex,pow_add,Rat.pow_succ h ell]
      _ = (g^(4*ell)*h^ell)*(g^4*h) := by grind
      _ = alpha^ell*alpha := by rw [ih,constant]
      _ = alpha^(ell+1) := (Rat.pow_succ alpha ell).symm

/-- All nonempty repayment packets with k≤4ell have one uniform coefficient bound. -/
theorem coefficient_bound (k ell : Nat) (hell : 1 ≤ ell) (hke : k ≤ 4*ell) :
    g^k*h^ell ≤ alpha := by
  have hm := pow_mono g (by decide +kernel) hke
  have hh : 0 ≤ h^ell := Rat.pow_nonneg (by decide +kernel)
  have hp := Rat.mul_le_mul_of_nonneg_right hm hh
  rw [packet_power] at hp
  exact Rat.le_trans hp (pow_le_self alpha (by decide +kernel) (by decide +kernel) ell hell)

def endpoint (k ell : Nat) (t : Rat) : Rat :=
  (g^k*h^ell)*(t+c)-h^ell*(c+d)+d

/-- Exact uniform endpoint decrease; k and ell are arbitrary naturals. -/
theorem endpoint_decreases (k ell : Nat) (hell : 1 ≤ ell) (hke : k ≤ 4*ell)
    (t : Rat) (ht : 8 ≤ t) : endpoint k ell t < t := by
  have coefficient := coefficient_bound k ell hell hke
  have input_nonneg : 0 ≤ t+c := by grind [c]
  have upper := Rat.mul_le_mul_of_nonneg_right coefficient input_nonneg
  have subtract_nonneg : 0 ≤ h^ell*(c+d) :=
    Rat.mul_nonneg (Rat.pow_nonneg (by decide +kernel)) (by decide +kernel)
  have endpoint_upper : endpoint k ell t ≤ alpha*(t+c)+d := by
    unfold endpoint
    grind
  have av : 0 ≤ 1-alpha := by decide +kernel
  have offset : 0 ≤ t-8 := by grind
  have margin : 0 < 8-alpha*(8+c)-d := by decide +kernel
  have product : 0 ≤ (1-alpha)*(t-8) := Rat.mul_nonneg av offset
  have identity : t-(alpha*(t+c)+d) =
      (1-alpha)*(t-8)+(8-alpha*(8+c)-d) := by grind
  have strictly : alpha*(t+c)+d < t := by grind
  grind

end FamilyCoverRepayment

#print axioms FamilyCoverRepayment.coefficient_bound
#print axioms FamilyCoverRepayment.endpoint_decreases
