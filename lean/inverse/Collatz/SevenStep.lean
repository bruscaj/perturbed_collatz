import Collatz.Physical

namespace Collatz.SevenStep
open Physical

abbrev Phase := Fin 7

def impulse (i : Phase) : Int :=
  if i = 2 ∨ i = 5 then 1 else if i = 3 ∨ i = 6 then -1 else 0

def word : Word := ⟨6, impulse⟩
abbrev State := Physical.State word
abbrev tick := step word
abbrev orbit := run tick

def height (i : Phase) : Int := if i = 3 ∨ i = 6 then 1 else 0
def z (i : Phase) (n : Int) := n+1-height i
def active (i : Phase) : Bool := i == 1 || i == 2 || i == 3 || i == 5
def weight (i : Phase) : Int := if i = 2 then 7 else if i = 5 then 5 else 4

def root (i : Phase) : Int := if i < 3 then 0 else if i < 5 then 1 else 2
def OnCycle (s : State) := s.2 = root s.1
def Captured := Reaches tick OnCycle

theorem root_cycle : ∀ i : Phase, tick (i,root i) = (i+1,root (i+1)) := by decide

theorem binary_height : ∀ i : Phase, height i = 0 ∨ height i = 1 := by decide
theorem height_difference : ∀ i : Phase, impulse i = height (i+1)-height i := by decide
theorem zero_sum : Conservative word := by unfold Conservative; decide
theorem impulse_primitive : Primitive word := by
  unfold Primitive; decide

theorem physical_conjugacy (i : Phase) (n : Int) :
    z (i+1) (tick (i,n)).2 =
    (if height i = 1 then shortcut (z i n) else shortcut (z i n-1)+1) := by
  change shortcut n + impulse i + 1 - height (i+1) = _
  rw [height_difference]
  rcases binary_height i with hi | hi <;> simp [z,hi] <;> omega

theorem safe_invariant (s : State) (hs : height s.1 ≤ s.2) :
    height (tick s).1 ≤ (tick s).2 := by
  let i : Phase := s.1
  change height (i+1) ≤ shortcut s.2 + impulse i
  change height i ≤ s.2 at hs
  rw [height_difference]
  have hb := binary_height i
  unfold shortcut; split <;> omega

theorem admissible_word : Admissible word := by
  intro i n hn k
  have invariant (s : State) (hs : height s.1 ≤ s.2) (d : Nat) :
      height (orbit d s).1 ≤ (orbit d s).2 := by
    induction d generalizing s with
    | zero => exact hs
    | succ d ih => exact ih (tick s) (safe_invariant s hs)
  have hs : height i ≤ n := by have := binary_height i; omega
  have h := invariant (i,n) hs k
  have := binary_height (orbit k (i,n)).1
  change 0 ≤ (orbit k (i,n)).2
  omega

def site (i : Phase) (m : Nat) : State := (i, 3*(m : Int)-1+height i)
def Marked (s : State) : Prop :=
  active s.1 = true ∧ z s.1 s.2 % 3 = 0 ∧ 0 < z s.1 s.2

theorem marked_site {s : State} (h : Marked s) :
    ∃ m : Nat, 0 < m ∧ s = site s.1 m := by
  obtain ⟨_,hd,hp⟩ := h
  refine ⟨(z s.1 s.2 / 3).toNat, by omega, ?_⟩
  refine Prod.ext ?_ ?_
  · rfl
  simp only [site]
  unfold z at *
  omega

/-- An affine expression in an arbitrary natural parameter, evaluated in signed arithmetic. -/
structure Affine where
  a : Int
  b : Int
  deriving Repr

def Affine.val (x : Affine) (q : Nat) : Int := x.a*(q : Int)+x.b

def Affine.advance (i : Phase) (x : Affine) : Affine :=
  if x.b % 2 = 0 then ⟨x.a/2, x.b/2+impulse i⟩
  else ⟨3*(x.a/2), (3*x.b+1)/2+impulse i⟩

theorem advance_sound (i : Phase) (x : Affine) (q : Nat) (even : x.a % 2 = 0) :
    tick (i,x.val q) = (i+1,(x.advance i).val q) := by
  have e : x.a = 2*(x.a/2) := by omega
  have ev : x.val q = 2*((x.a/2)*(q:Int))+x.b := by
    unfold Affine.val
    conv => lhs; rw [e, Int.mul_assoc]
  refine Prod.ext ?_ ?_
  · rfl
  change shortcut (x.val q) + impulse i = _
  rw [ev]
  unfold shortcut Affine.advance
  split <;> split <;> simp only [Affine.val, Int.mul_assoc] <;> omega

/-- A success certifies the first marked endpoint, including its phase and the earlier misses. -/
def checkHit (accept : Phase → Affine → Bool) (fuel : Nat) (i : Phase) (x : Affine) : Bool :=
  if active i && x.a % 3 == 0 && z i x.b % 3 == 0 then
    x.a ≥ 0 && z i x.b > 0 && accept i x
  else
    match fuel with
    | 0 => false
    | k+1 =>
      (!active i || x.a % 3 == 0) && x.a % 2 == 0 &&
        checkHit accept k (i+1) (x.advance i)

def FirstHit (P : State → Prop) (s : State) (fuel : Nat) : Prop :=
  ∃ k ≤ fuel, Marked (orbit k s) ∧ P (orbit k s) ∧ ∀ j < k, ¬Marked (orbit j s)

theorem affine_z (i : Phase) (x : Affine) (q : Nat) :
    z i (x.val q) = x.a*(q:Int)+z i x.b := by simp [z, Affine.val]; omega

theorem affine_mod3 (i : Phase) (x : Affine) (q : Nat) (h : x.a % 3 = 0) :
    z i (x.val q) % 3 = z i x.b % 3 := by
  rw [affine_z, Int.add_emod, Int.mul_emod, h]; simp

theorem checkHit_sound (accept : Phase → Affine → Bool) (q : Nat) (P : State → Prop)
    (valid : ∀ i x, accept i x = true → P (i,x.val q))
    (fuel : Nat) (i : Phase) (x : Affine) (ok : checkHit accept fuel i x = true) :
    FirstHit P (i,x.val q) fuel := by
  induction fuel generalizing i x with
  | zero =>
    unfold checkHit at ok
    split at ok
    · rename_i guard
      simp only [Bool.and_eq_true, beq_iff_eq] at guard
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ok
      exact ⟨0, by omega, ⟨guard.1.1,(affine_mod3 i x q guard.1.2).trans guard.2, by
        change 0 < z i (x.val q); rw [affine_z]; have := Int.mul_nonneg ok.1.1 (Int.natCast_nonneg q); omega⟩,
        valid i x ok.2, by intro j hj; omega⟩
    · contradiction
  | succ k ih =>
    unfold checkHit at ok
    split at ok
    · rename_i guard
      simp only [Bool.and_eq_true, beq_iff_eq] at guard
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ok
      exact ⟨0, by omega, ⟨guard.1.1,(affine_mod3 i x q guard.1.2).trans guard.2, by
        change 0 < z i (x.val q); rw [affine_z]; have := Int.mul_nonneg ok.1.1 (Int.natCast_nonneg q); omega⟩,
        valid i x ok.2, by intro j hj; omega⟩
    · rename_i guard
      simp only [Bool.and_eq_true, beq_iff_eq] at ok
      obtain ⟨j,hj,marked,accepted,first⟩ := ih _ _ ok.2
      have replay := advance_sound i x q ok.1.2
      refine ⟨j+1, by omega, ?_, ?_, ?_⟩
      · change Marked (orbit j (tick _)); rwa [replay]
      · change P (orbit j (tick _)); rwa [replay]
      · intro d hd
        cases d with
        | zero =>
          intro hm
          obtain ⟨ha,hm,_⟩ := hm
          change active i = true at ha
          change z i (x.val q) % 3 = 0 at hm
          simp only [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at ok
          have h3 : x.a % 3 = 0 := ok.1.1.resolve_left (by simp [ha])
          apply guard
          simp [ha,h3,← affine_mod3 i x q h3, hm]
        | succ d =>
          change ¬Marked (orbit d (tick _))
          rw [replay]
          exact first d (by omega)

end Collatz.SevenStep
