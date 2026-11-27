import Std

/-! The fixed seven-step forcing, in positive coordinates and signed physical coordinates. -/
namespace Collatz.SevenStepCertificate

inductive Phase where
  | p0 | p1 | p2 | p3 | p4 | p5 | p6
  deriving DecidableEq, Repr

def Phase.next : Phase → Phase
  | .p0 => .p1 | .p1 => .p2 | .p2 => .p3 | .p3 => .p4
  | .p4 => .p5 | .p5 => .p6 | .p6 => .p0

def height : Phase → Int
  | .p3 | .p6 => 1
  | _ => 0

def impulse : Phase → Int
  | .p2 | .p5 => 1
  | .p3 | .p6 => -1
  | _ => 0

def T (z : Nat) : Nat := if z % 2 = 0 then z / 2 else (3*z+1)/2
def U (z : Nat) : Nat := if z % 2 = 0 then 3*z/2 else (z+1)/2

def update : Phase → Nat → Nat
  | .p3 | .p6 => T
  | _ => U

abbrev State := Phase × Nat

def next (s : State) : State := (s.1.next, update s.1 s.2)

def run (s : State) : Nat → State
  | 0 => s
  | k+1 => run (next s) k

/-- Decode the physical state without any natural-number subtraction. -/
def physical (p : Phase) (z : Nat) : Int := (z : Int) - 1 + height p

def signedT (n : Int) : Int := if n % 2 = 0 then n / 2 else (3*n+1)/2

def physicalNext (s : Phase × Int) : Phase × Int :=
  (s.1.next, signedT s.2 + impulse s.1)

def physicalRun (s : Phase × Int) : Nat → Phase × Int
  | 0 => s
  | k+1 => physicalRun (physicalNext s) k

def decode (s : State) : Phase × Int := (s.1, physical s.1 s.2)

theorem update_pos (p : Phase) {z : Nat} (hz : 0 < z) : 0 < update p z := by
  cases p <;> simp only [update, T, U] <;> split <;> omega

theorem physical_nonneg (p : Phase) {z : Nat} (hz : 0 < z) : 0 ≤ physical p z := by
  cases p <;> simp only [physical, height] <;> omega

/-- Exact agreement with signed forcing for every positive transformed state. -/
theorem update_faithful (p : Phase) {z : Nat} (hz : 0 < z) :
    physical p.next (update p z) = signedT (physical p z) + impulse p := by
  cases p <;> simp only [physical, Phase.next, height, update, T, U, signedT, impulse]
  all_goals split <;> split <;> omega

theorem run_pos (s : State) (hs : 0 < s.2) (k : Nat) : 0 < (run s k).2 := by
  induction k generalizing s with
  | zero => exact hs
  | succ k ih => exact ih (next s) (update_pos s.1 hs)

theorem run_add (s : State) (a b : Nat) : run s (a+b) = run (run s a) b := by
  induction a generalizing s with
  | zero => simp only [Nat.zero_add, run]
  | succ a ih => simpa only [Nat.succ_add, run] using ih (next s)

theorem run_faithful (s : State) (hs : 0 < s.2) (k : Nat) :
    decode (run s k) = physicalRun (decode s) k := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    have one : decode (next s) = physicalNext (decode s) := by
      apply Prod.ext
      · rfl
      · exact update_faithful s.1 hs
    simpa only [run, physicalRun, one] using ih (next s) (update_pos s.1 hs)

/-- The known transformed cycle, indexed by phase. Zero continues evolving physically. -/
def cycleValue : Phase → Nat
  | .p0 | .p1 | .p2 | .p3 => 1
  | .p4 => 2 | .p5 => 3 | .p6 => 2

def OnCycle (s : State) : Prop := s.2 = cycleValue s.1

theorem cycle_next (s : State) (hs : OnCycle s) : OnCycle (next s) := by
  rcases s with ⟨p,z⟩
  change z = cycleValue p at hs
  subst z
  cases p <;> rfl

theorem cycle_run (s : State) (hs : OnCycle s) (k : Nat) : OnCycle (run s k) := by
  induction k generalizing s with
  | zero => exact hs
  | succ k ih => exact ih (next s) (cycle_next s hs)

/-- Capture means reaching this exact phase-indexed cycle. -/
def Captured (s : State) : Prop := ∃ k, OnCycle (run s k)

theorem captured_of_run (s : State) (a : Nat) (h : Captured (run s a)) : Captured s := by
  obtain ⟨b,hb⟩ := h
  exact ⟨a+b, by simpa only [run_add] using hb⟩

theorem captured_run (s : State) (h : Captured s) (a : Nat) : Captured (run s a) := by
  obtain ⟨b,hb⟩ := h
  refine ⟨b, ?_⟩
  have hc := cycle_run (run s b) hb a
  rw [← run_add] at hc ⊢
  simpa only [Nat.add_comm] using hc

/-- Meeting at the same value and phase preserves capture in both directions. -/
theorem captured_of_coalescence (s t : State) (a b : Nat)
    (meet : run s a = run t b) (ht : Captured t) : Captured s := by
  apply captured_of_run s a
  rw [meet]
  exact captured_run t ht b

end Collatz.SevenStepCertificate
