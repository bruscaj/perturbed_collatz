import Std

/-!
Independent signed-physical verification of exact family-cover identities.
The deterministic forcing is (0,0,1,-1,0,1,-1). Safe zeros continue.
No project imports, custom axioms, placeholders, or global-capture hypotheses.
These identities organize existing reduction domains; no novelty of those
source domains or closure of B1/A3/N03 is claimed.
-/
namespace FamilyCoverTheory

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

abbrev State := Phase × Int

def shortcut (n : Int) : Int :=
  if n % 2 = 0 then n / 2 else (3*n+1)/2

def step (s : State) : State :=
  (s.1.next, shortcut s.2 + impulse s.1)

def run (s : State) : Nat → State
  | 0 => s
  | k+1 => run (step s) k

def launch (p : Phase) (m : Int) : State := (p, 3*m-1+height p)

def Safe (s : State) : Prop := height s.1 ≤ s.2

def sectionWeight : Phase → Int
  | .p1 => 4 | .p2 => 7 | .p3 => 4 | .p5 => 5
  | _ => 0

def rank (p : Phase) (m : Int) : Int := sectionWeight p * m

def InSection (p : Phase) : Prop :=
  p = .p1 ∨ p = .p2 ∨ p = .p3 ∨ p = .p5

theorem section_safe (p : Phase) {m : Int} (hm : 1 ≤ m) :
    Safe (launch p m) := by
  simp only [Safe, launch]
  omega

theorem safe_step (s : State) (hs : Safe s) : Safe (step s) := by
  rcases s with ⟨p,n⟩
  cases p <;> simp only [Safe, step, shortcut, height, Phase.next, impulse] at *
  all_goals split <;> omega

theorem safe_run (s : State) (hs : Safe s) (k : Nat) : Safe (run s k) := by
  induction k generalizing s with
  | zero => exact hs
  | succ k ih => exact ih (step s) (safe_step s hs)

theorem run_add (s : State) (a b : Nat) :
    run s (a+b) = run (run s a) b := by
  induction a generalizing s with
  | zero => simp only [Nat.zero_add, run]
  | succ a ih => simpa only [Nat.succ_add, run] using ih (step s)

def cycleValue : Phase → Int
  | .p0 | .p1 | .p2 => 0
  | .p3 | .p4 => 1
  | .p5 | .p6 => 2

def OnCycle (s : State) : Prop := s.2 = cycleValue s.1

def Captured (s : State) : Prop := ∃ k, OnCycle (run s k)

theorem cycle_step (s : State) (hs : OnCycle s) : OnCycle (step s) := by
  rcases s with ⟨p,n⟩
  change n = cycleValue p at hs
  subst n
  cases p <;> rfl

theorem cycle_run (s : State) (hs : OnCycle s) (k : Nat) :
    OnCycle (run s k) := by
  induction k generalizing s with
  | zero => exact hs
  | succ k ih => exact ih (step s) (cycle_step s hs)

theorem captured_run (s : State) (h : Captured s) (a : Nat) :
    Captured (run s a) := by
  obtain ⟨b,hb⟩ := h
  refine ⟨b, ?_⟩
  have hc := cycle_run (run s b) hb a
  rw [← run_add] at hc ⊢
  simpa only [Nat.add_comm] using hc

theorem captured_of_run (s : State) (a : Nat) (h : Captured (run s a)) :
    Captured s := by
  obtain ⟨b,hb⟩ := h
  exact ⟨a+b, by simpa only [run_add] using hb⟩

theorem captured_iff_of_run {s t : State} {a : Nat} (meet : run s a = t) :
    Captured s ↔ Captured t := by
  constructor
  · intro h
    rw [← meet]
    exact captured_run s h a
  · intro h
    apply captured_of_run s a
    simpa only [meet] using h

private theorem pump_p0 (v : Int) :
    run (launch .p0 (128*v + (0))) 7 =
      launch .p0 (243*v + (0)) := by
  have hstart : launch .p0 (128*v + (0)) = (.p0, (384*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [launch, height]; omega
  have hend : launch .p0 (243*v + (0)) = (.p0, (729*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [launch, height]; omega
  rw [hstart, hend]
  have h0 : step (.p0, (384*v + (-1))) = (.p1, (576*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h1 : step (.p1, (576*v + (-1))) = (.p2, (864*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h2 : step (.p2, (864*v + (-1))) = (.p3, (1296*v + (0))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h3 : step (.p3, (1296*v + (0))) = (.p4, (648*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h4 : step (.p4, (648*v + (-1))) = (.p5, (972*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h5 : step (.p5, (972*v + (-1))) = (.p6, (1458*v + (0))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h6 : step (.p6, (1458*v + (0))) = (.p0, (729*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6]
private theorem pump_p1 (v : Int) :
    run (launch .p1 (128*v + (0))) 7 =
      launch .p1 (243*v + (0)) := by
  have hstart : launch .p1 (128*v + (0)) = (.p1, (384*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [launch, height]; omega
  have hend : launch .p1 (243*v + (0)) = (.p1, (729*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [launch, height]; omega
  rw [hstart, hend]
  have h0 : step (.p1, (384*v + (-1))) = (.p2, (576*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h1 : step (.p2, (576*v + (-1))) = (.p3, (864*v + (0))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h2 : step (.p3, (864*v + (0))) = (.p4, (432*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h3 : step (.p4, (432*v + (-1))) = (.p5, (648*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h4 : step (.p5, (648*v + (-1))) = (.p6, (972*v + (0))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h5 : step (.p6, (972*v + (0))) = (.p0, (486*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h6 : step (.p0, (486*v + (-1))) = (.p1, (729*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6]
private theorem pump_p2 (v : Int) :
    run (launch .p2 (128*v + (0))) 7 =
      launch .p2 (243*v + (0)) := by
  have hstart : launch .p2 (128*v + (0)) = (.p2, (384*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [launch, height]; omega
  have hend : launch .p2 (243*v + (0)) = (.p2, (729*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [launch, height]; omega
  rw [hstart, hend]
  have h0 : step (.p2, (384*v + (-1))) = (.p3, (576*v + (0))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h1 : step (.p3, (576*v + (0))) = (.p4, (288*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h2 : step (.p4, (288*v + (-1))) = (.p5, (432*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h3 : step (.p5, (432*v + (-1))) = (.p6, (648*v + (0))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h4 : step (.p6, (648*v + (0))) = (.p0, (324*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h5 : step (.p0, (324*v + (-1))) = (.p1, (486*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h6 : step (.p1, (486*v + (-1))) = (.p2, (729*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6]
private theorem pump_p3 (v : Int) :
    run (launch .p3 (128*v + (0))) 7 =
      launch .p3 (243*v + (0)) := by
  have hstart : launch .p3 (128*v + (0)) = (.p3, (384*v + (0))) := by
    apply Prod.ext
    · rfl
    · simp only [launch, height]; omega
  have hend : launch .p3 (243*v + (0)) = (.p3, (729*v + (0))) := by
    apply Prod.ext
    · rfl
    · simp only [launch, height]; omega
  rw [hstart, hend]
  have h0 : step (.p3, (384*v + (0))) = (.p4, (192*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h1 : step (.p4, (192*v + (-1))) = (.p5, (288*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h2 : step (.p5, (288*v + (-1))) = (.p6, (432*v + (0))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h3 : step (.p6, (432*v + (0))) = (.p0, (216*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h4 : step (.p0, (216*v + (-1))) = (.p1, (324*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h5 : step (.p1, (324*v + (-1))) = (.p2, (486*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h6 : step (.p2, (486*v + (-1))) = (.p3, (729*v + (0))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6]
private theorem pump_p4 (v : Int) :
    run (launch .p4 (128*v + (0))) 7 =
      launch .p4 (243*v + (0)) := by
  have hstart : launch .p4 (128*v + (0)) = (.p4, (384*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [launch, height]; omega
  have hend : launch .p4 (243*v + (0)) = (.p4, (729*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [launch, height]; omega
  rw [hstart, hend]
  have h0 : step (.p4, (384*v + (-1))) = (.p5, (576*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h1 : step (.p5, (576*v + (-1))) = (.p6, (864*v + (0))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h2 : step (.p6, (864*v + (0))) = (.p0, (432*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h3 : step (.p0, (432*v + (-1))) = (.p1, (648*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h4 : step (.p1, (648*v + (-1))) = (.p2, (972*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h5 : step (.p2, (972*v + (-1))) = (.p3, (1458*v + (0))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h6 : step (.p3, (1458*v + (0))) = (.p4, (729*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6]
private theorem pump_p5 (v : Int) :
    run (launch .p5 (128*v + (0))) 7 =
      launch .p5 (243*v + (0)) := by
  have hstart : launch .p5 (128*v + (0)) = (.p5, (384*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [launch, height]; omega
  have hend : launch .p5 (243*v + (0)) = (.p5, (729*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [launch, height]; omega
  rw [hstart, hend]
  have h0 : step (.p5, (384*v + (-1))) = (.p6, (576*v + (0))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h1 : step (.p6, (576*v + (0))) = (.p0, (288*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h2 : step (.p0, (288*v + (-1))) = (.p1, (432*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h3 : step (.p1, (432*v + (-1))) = (.p2, (648*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h4 : step (.p2, (648*v + (-1))) = (.p3, (972*v + (0))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h5 : step (.p3, (972*v + (0))) = (.p4, (486*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h6 : step (.p4, (486*v + (-1))) = (.p5, (729*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6]
private theorem pump_p6 (v : Int) :
    run (launch .p6 (128*v + (0))) 7 =
      launch .p6 (243*v + (0)) := by
  have hstart : launch .p6 (128*v + (0)) = (.p6, (384*v + (0))) := by
    apply Prod.ext
    · rfl
    · simp only [launch, height]; omega
  have hend : launch .p6 (243*v + (0)) = (.p6, (729*v + (0))) := by
    apply Prod.ext
    · rfl
    · simp only [launch, height]; omega
  rw [hstart, hend]
  have h0 : step (.p6, (384*v + (0))) = (.p0, (192*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h1 : step (.p0, (192*v + (-1))) = (.p1, (288*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h2 : step (.p1, (288*v + (-1))) = (.p2, (432*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h3 : step (.p2, (432*v + (-1))) = (.p3, (648*v + (0))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h4 : step (.p3, (648*v + (0))) = (.p4, (324*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h5 : step (.p4, (324*v + (-1))) = (.p5, (486*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h6 : step (.p5, (486*v + (-1))) = (.p6, (729*v + (0))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6]

/-- The exact all-even normalized period, proved directly in signed physical coordinates. -/
theorem seven_step_pump (p : Phase) (v : Int) :
    run (launch p (128*v)) 7 = launch p (243*v) := by
  cases p with
  | p0 => simpa only [Int.add_zero] using pump_p0 v
  | p1 => simpa only [Int.add_zero] using pump_p1 v
  | p2 => simpa only [Int.add_zero] using pump_p2 v
  | p3 => simpa only [Int.add_zero] using pump_p3 v
  | p4 => simpa only [Int.add_zero] using pump_p4 v
  | p5 => simpa only [Int.add_zero] using pump_p5 v
  | p6 => simpa only [Int.add_zero] using pump_p6 v

/-- Every positive physical realization of this pump is safe throughout. -/
theorem seven_step_pump_safe (p : Phase) (v : Int) (hv : 1 ≤ v) (k : Nat) :
    Safe (run (launch p (128*v)) k) := by
  apply safe_run
  apply section_safe
  omega

theorem seven_step_rank_gap (p : Phase) (hp : InSection p) (v : Int) :
    rank p (243*v) - rank p (128*v) = 115 * sectionWeight p * v := by
  rcases hp with rfl | rfl | rfl | rfl
  all_goals simp only [rank, sectionWeight]; omega

theorem seven_step_smaller_rank (p : Phase) (hp : InSection p)
    (v : Int) (hv : 1 ≤ v) : rank p (128*v) < rank p (243*v) := by
  rcases hp with rfl | rfl | rfl | rfl
  all_goals simp only [rank, sectionWeight]; omega

/-- A reduction/capture-transfer rule; it does not assume all smaller starts capture. -/
theorem seven_step_capture_iff (p : Phase) (v : Int) :
    Captured (launch p (128*v)) ↔ Captured (launch p (243*v)) :=
  captured_iff_of_run (seven_step_pump p v)

theorem zero_precursor_p1 (v : Int) :
    run (launch .p5 (131072*v + (-1))) 17 =
      launch .p1 (177147*v + (0)) := by
  have hstart : launch .p5 (131072*v + (-1)) = (.p5, (393216*v + (-4))) := by
    apply Prod.ext
    · rfl
    · simp only [launch, height]; omega
  have hend : launch .p1 (177147*v + (0)) = (.p1, (531441*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [launch, height]; omega
  rw [hstart, hend]
  have h0 : step (.p5, (393216*v + (-4))) = (.p6, (196608*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h1 : step (.p6, (196608*v + (-1))) = (.p0, (294912*v + (-2))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h2 : step (.p0, (294912*v + (-2))) = (.p1, (147456*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h3 : step (.p1, (147456*v + (-1))) = (.p2, (221184*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h4 : step (.p2, (221184*v + (-1))) = (.p3, (331776*v + (0))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h5 : step (.p3, (331776*v + (0))) = (.p4, (165888*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h6 : step (.p4, (165888*v + (-1))) = (.p5, (248832*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h7 : step (.p5, (248832*v + (-1))) = (.p6, (373248*v + (0))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h8 : step (.p6, (373248*v + (0))) = (.p0, (186624*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h9 : step (.p0, (186624*v + (-1))) = (.p1, (279936*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h10 : step (.p1, (279936*v + (-1))) = (.p2, (419904*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h11 : step (.p2, (419904*v + (-1))) = (.p3, (629856*v + (0))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h12 : step (.p3, (629856*v + (0))) = (.p4, (314928*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h13 : step (.p4, (314928*v + (-1))) = (.p5, (472392*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h14 : step (.p5, (472392*v + (-1))) = (.p6, (708588*v + (0))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h15 : step (.p6, (708588*v + (0))) = (.p0, (354294*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h16 : step (.p0, (354294*v + (-1))) = (.p1, (531441*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]

theorem zero_precursor_p1_rank_gap (v : Int) :
    rank .p1 (177147*v) - rank .p5 (131072*v-1) = 53228*v+5 := by
  simp only [rank, sectionWeight]
  omega

theorem zero_precursor_p1_smaller_rank (v : Int) (hv : 1 ≤ v) :
    rank .p5 (131072*v-1) < rank .p1 (177147*v) := by
  simp only [rank, sectionWeight]
  omega

theorem zero_precursor_p1_safe (v : Int) (hv : 1 ≤ v) (k : Nat) :
    Safe (run (launch .p5 (131072*v-1)) k) := by
  apply safe_run
  apply section_safe
  omega

theorem zero_precursor_p1_capture_iff (v : Int) :
    Captured (launch .p5 (131072*v-1)) ↔
    Captured (launch .p1 (177147*v)) := by
  apply captured_iff_of_run
  simpa only [Int.add_zero, Int.sub_eq_add_neg] using zero_precursor_p1 v

theorem zero_precursor_p2 (v : Int) :
    run (launch .p5 (2048*v + (-1))) 11 =
      launch .p2 (2187*v + (0)) := by
  have hstart : launch .p5 (2048*v + (-1)) = (.p5, (6144*v + (-4))) := by
    apply Prod.ext
    · rfl
    · simp only [launch, height]; omega
  have hend : launch .p2 (2187*v + (0)) = (.p2, (6561*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [launch, height]; omega
  rw [hstart, hend]
  have h0 : step (.p5, (6144*v + (-4))) = (.p6, (3072*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h1 : step (.p6, (3072*v + (-1))) = (.p0, (4608*v + (-2))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h2 : step (.p0, (4608*v + (-2))) = (.p1, (2304*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h3 : step (.p1, (2304*v + (-1))) = (.p2, (3456*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h4 : step (.p2, (3456*v + (-1))) = (.p3, (5184*v + (0))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h5 : step (.p3, (5184*v + (0))) = (.p4, (2592*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h6 : step (.p4, (2592*v + (-1))) = (.p5, (3888*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h7 : step (.p5, (3888*v + (-1))) = (.p6, (5832*v + (0))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h8 : step (.p6, (5832*v + (0))) = (.p0, (2916*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h9 : step (.p0, (2916*v + (-1))) = (.p1, (4374*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h10 : step (.p1, (4374*v + (-1))) = (.p2, (6561*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]

theorem zero_precursor_p2_rank_gap (v : Int) :
    rank .p2 (2187*v) - rank .p5 (2048*v-1) = 5069*v+5 := by
  simp only [rank, sectionWeight]
  omega

theorem zero_precursor_p2_smaller_rank (v : Int) (hv : 1 ≤ v) :
    rank .p5 (2048*v-1) < rank .p2 (2187*v) := by
  simp only [rank, sectionWeight]
  omega

theorem zero_precursor_p2_safe (v : Int) (hv : 1 ≤ v) (k : Nat) :
    Safe (run (launch .p5 (2048*v-1)) k) := by
  apply safe_run
  apply section_safe
  omega

theorem zero_precursor_p2_capture_iff (v : Int) :
    Captured (launch .p5 (2048*v-1)) ↔
    Captured (launch .p2 (2187*v)) := by
  apply captured_iff_of_run
  simpa only [Int.add_zero, Int.sub_eq_add_neg] using zero_precursor_p2 v

theorem zero_precursor_p3 (v : Int) :
    run (launch .p5 (4096*v + (-1))) 12 =
      launch .p3 (6561*v + (0)) := by
  have hstart : launch .p5 (4096*v + (-1)) = (.p5, (12288*v + (-4))) := by
    apply Prod.ext
    · rfl
    · simp only [launch, height]; omega
  have hend : launch .p3 (6561*v + (0)) = (.p3, (19683*v + (0))) := by
    apply Prod.ext
    · rfl
    · simp only [launch, height]; omega
  rw [hstart, hend]
  have h0 : step (.p5, (12288*v + (-4))) = (.p6, (6144*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h1 : step (.p6, (6144*v + (-1))) = (.p0, (9216*v + (-2))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h2 : step (.p0, (9216*v + (-2))) = (.p1, (4608*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h3 : step (.p1, (4608*v + (-1))) = (.p2, (6912*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h4 : step (.p2, (6912*v + (-1))) = (.p3, (10368*v + (0))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h5 : step (.p3, (10368*v + (0))) = (.p4, (5184*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h6 : step (.p4, (5184*v + (-1))) = (.p5, (7776*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h7 : step (.p5, (7776*v + (-1))) = (.p6, (11664*v + (0))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h8 : step (.p6, (11664*v + (0))) = (.p0, (5832*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h9 : step (.p0, (5832*v + (-1))) = (.p1, (8748*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h10 : step (.p1, (8748*v + (-1))) = (.p2, (13122*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h11 : step (.p2, (13122*v + (-1))) = (.p3, (19683*v + (0))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]

theorem zero_precursor_p3_rank_gap (v : Int) :
    rank .p3 (6561*v) - rank .p5 (4096*v-1) = 5764*v+5 := by
  simp only [rank, sectionWeight]
  omega

theorem zero_precursor_p3_smaller_rank (v : Int) (hv : 1 ≤ v) :
    rank .p5 (4096*v-1) < rank .p3 (6561*v) := by
  simp only [rank, sectionWeight]
  omega

theorem zero_precursor_p3_safe (v : Int) (hv : 1 ≤ v) (k : Nat) :
    Safe (run (launch .p5 (4096*v-1)) k) := by
  apply safe_run
  apply section_safe
  omega

theorem zero_precursor_p3_capture_iff (v : Int) :
    Captured (launch .p5 (4096*v-1)) ↔
    Captured (launch .p3 (6561*v)) := by
  apply captured_iff_of_run
  simpa only [Int.add_zero, Int.sub_eq_add_neg] using zero_precursor_p3 v

theorem zero_precursor_p5 (v : Int) :
    run (launch .p5 (16384*v + (-1))) 14 =
      launch .p5 (19683*v + (0)) := by
  have hstart : launch .p5 (16384*v + (-1)) = (.p5, (49152*v + (-4))) := by
    apply Prod.ext
    · rfl
    · simp only [launch, height]; omega
  have hend : launch .p5 (19683*v + (0)) = (.p5, (59049*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [launch, height]; omega
  rw [hstart, hend]
  have h0 : step (.p5, (49152*v + (-4))) = (.p6, (24576*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h1 : step (.p6, (24576*v + (-1))) = (.p0, (36864*v + (-2))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h2 : step (.p0, (36864*v + (-2))) = (.p1, (18432*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h3 : step (.p1, (18432*v + (-1))) = (.p2, (27648*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h4 : step (.p2, (27648*v + (-1))) = (.p3, (41472*v + (0))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h5 : step (.p3, (41472*v + (0))) = (.p4, (20736*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h6 : step (.p4, (20736*v + (-1))) = (.p5, (31104*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h7 : step (.p5, (31104*v + (-1))) = (.p6, (46656*v + (0))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h8 : step (.p6, (46656*v + (0))) = (.p0, (23328*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h9 : step (.p0, (23328*v + (-1))) = (.p1, (34992*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h10 : step (.p1, (34992*v + (-1))) = (.p2, (52488*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h11 : step (.p2, (52488*v + (-1))) = (.p3, (78732*v + (0))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h12 : step (.p3, (78732*v + (0))) = (.p4, (39366*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  have h13 : step (.p4, (39366*v + (-1))) = (.p5, (59049*v + (-1))) := by
    apply Prod.ext
    · rfl
    · simp only [step, shortcut, impulse]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]

theorem zero_precursor_p5_rank_gap (v : Int) :
    rank .p5 (19683*v) - rank .p5 (16384*v-1) = 16495*v+5 := by
  simp only [rank, sectionWeight]
  omega

theorem zero_precursor_p5_smaller_rank (v : Int) (hv : 1 ≤ v) :
    rank .p5 (16384*v-1) < rank .p5 (19683*v) := by
  simp only [rank, sectionWeight]
  omega

theorem zero_precursor_p5_safe (v : Int) (hv : 1 ≤ v) (k : Nat) :
    Safe (run (launch .p5 (16384*v-1)) k) := by
  apply safe_run
  apply section_safe
  omega

theorem zero_precursor_p5_capture_iff (v : Int) :
    Captured (launch .p5 (16384*v-1)) ↔
    Captured (launch .p5 (19683*v)) := by
  apply captured_iff_of_run
  simpa only [Int.add_zero, Int.sub_eq_add_neg] using zero_precursor_p5 v


/-- Ternary guards in the three current residual parameters. -/
theorem b1_ternary_guard (t : Int) :
    (2*t)%243 = 0 ↔ t%243 = 0 := by omega

theorem a3_ternary_guard (t : Int) :
    (4*t+3)%243 = 0 ↔ t%243 = 60 := by omega

theorem n03_ternary_guard (t : Int) :
    (8*t+2)%243 = 0 ↔ t%243 = 182 := by omega

/-- B1 parameter t=243v: the alternative reaches the source after one period. -/
theorem b1_ternary_reduction (v : Int) :
    run (launch .p1 (256*v)) 7 = launch .p1 (2*(243*v)) := by
  have h := seven_step_pump .p1 (2*v)
  have a : 128*(2*v) = 256*v := by omega
  have b : 243*(2*v) = 2*(243*v) := by omega
  simpa only [a,b] using h

theorem b1_ternary_rank (v : Int) (hv : 1 ≤ v) :
    rank .p1 (256*v) < rank .p1 (2*(243*v)) := by
  simp only [rank, sectionWeight]
  omega

/-- A3 parameter t=243v+60, v>=0, is in the same-phase pump image. -/
theorem a3_ternary_reduction (v : Int) :
    run (launch .p3 (512*v+128)) 7 = launch .p3 (4*(243*v+60)+3) := by
  have h := seven_step_pump .p3 (4*v+1)
  have a : 128*(4*v+1) = 512*v+128 := by omega
  have b : 243*(4*v+1) = 4*(243*v+60)+3 := by omega
  simpa only [a,b] using h

theorem a3_ternary_rank (v : Int) (hv : 0 ≤ v) :
    rank .p3 (512*v+128) < rank .p3 (4*(243*v+60)+3) := by
  simp only [rank, sectionWeight]
  omega

/-- N03 parameter t=243v+182, v>=0, is in the same-phase pump image. -/
theorem n03_ternary_reduction (v : Int) :
    run (launch .p5 (1024*v+768)) 7 = launch .p5 (8*(243*v+182)+2) := by
  have h := seven_step_pump .p5 (8*v+6)
  have a : 128*(8*v+6) = 1024*v+768 := by omega
  have b : 243*(8*v+6) = 8*(243*v+182)+2 := by omega
  simpa only [a,b] using h

theorem n03_ternary_rank (v : Int) (hv : 0 ≤ v) :
    rank .p5 (1024*v+768) < rank .p5 (8*(243*v+182)+2) := by
  simp only [rank, sectionWeight]
  omega

end FamilyCoverTheory

#print axioms FamilyCoverTheory.seven_step_pump
#print axioms FamilyCoverTheory.seven_step_pump_safe
#print axioms FamilyCoverTheory.seven_step_rank_gap
#print axioms FamilyCoverTheory.seven_step_smaller_rank
#print axioms FamilyCoverTheory.seven_step_capture_iff
#print axioms FamilyCoverTheory.zero_precursor_p1
#print axioms FamilyCoverTheory.zero_precursor_p1_rank_gap
#print axioms FamilyCoverTheory.zero_precursor_p1_smaller_rank
#print axioms FamilyCoverTheory.zero_precursor_p1_safe
#print axioms FamilyCoverTheory.zero_precursor_p1_capture_iff
#print axioms FamilyCoverTheory.zero_precursor_p2
#print axioms FamilyCoverTheory.zero_precursor_p2_rank_gap
#print axioms FamilyCoverTheory.zero_precursor_p2_smaller_rank
#print axioms FamilyCoverTheory.zero_precursor_p2_safe
#print axioms FamilyCoverTheory.zero_precursor_p2_capture_iff
#print axioms FamilyCoverTheory.zero_precursor_p3
#print axioms FamilyCoverTheory.zero_precursor_p3_rank_gap
#print axioms FamilyCoverTheory.zero_precursor_p3_smaller_rank
#print axioms FamilyCoverTheory.zero_precursor_p3_safe
#print axioms FamilyCoverTheory.zero_precursor_p3_capture_iff
#print axioms FamilyCoverTheory.zero_precursor_p5
#print axioms FamilyCoverTheory.zero_precursor_p5_rank_gap
#print axioms FamilyCoverTheory.zero_precursor_p5_smaller_rank
#print axioms FamilyCoverTheory.zero_precursor_p5_safe
#print axioms FamilyCoverTheory.zero_precursor_p5_capture_iff
#print axioms FamilyCoverTheory.b1_ternary_guard
#print axioms FamilyCoverTheory.b1_ternary_reduction
#print axioms FamilyCoverTheory.b1_ternary_rank
#print axioms FamilyCoverTheory.a3_ternary_guard
#print axioms FamilyCoverTheory.a3_ternary_reduction
#print axioms FamilyCoverTheory.a3_ternary_rank
#print axioms FamilyCoverTheory.n03_ternary_guard
#print axioms FamilyCoverTheory.n03_ternary_reduction
#print axioms FamilyCoverTheory.n03_ternary_rank
