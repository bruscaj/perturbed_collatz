import Collatz.Tree

namespace Collatz.Coverage

private theorem even_step (k : Nat) : T (2*k) = k := by
  unfold T
  split <;> omega

private theorem lap_eight (k : Nat) : oneLap (8*k) = 3*k := by
  have h₁ : T (8*k) + 1 = 4*k+1 := by unfold T; split <;> omega
  have h₂ : T (4*k+1) = 6*k+2 := by unfold T; split <;> omega
  simp only [oneLap, h₁, h₂]
  unfold T
  split <;> omega

private theorem lap_eight_plus_six (k : Nat) : oneLap (8*k+6) = k := by
  have h₁ : T (8*k+6) + 1 = 4*k+4 := by unfold T; split <;> omega
  have h₂ : T (4*k+4) = 2*k+2 := by unfold T; split <;> omega
  simp only [oneLap, h₁, h₂]
  unfold T
  split <;> omega

/-- A positive predecessor eligible for repeated splitting, for every phase-zero target. -/
def stem (y : Nat) : Nat :=
  if y % 3 ≠ 0 then A y
  else if (y / 3) % 3 = 0 then 64*(y/3)+16 else 64*(y/3)+6

theorem stem_at_least_two (y : Nat) : 2 ≤ stem y := by
  unfold stem
  split
  · unfold A; omega
  · split <;> omega

theorem stem_spec (y : Nat) : Good (stem y) ∧ twoLaps (stem y) = y := by
  by_cases hn : y % 3 ≠ 0
  · have hy : Good y := ⟨by omega, hn⟩
    simpa [stem, hn] using And.intro (A_good hy) (A_parent y)
  · have hy : 3*(y/3) = y := by omega
    by_cases ht : (y/3) % 3 = 0
    · simp only [stem, hn, ht, if_false, if_true]
      constructor
      · unfold Good
        omega
      · have h₁ : 64*(y/3)+16 = 8*(8*(y/3)+2) := by omega
        have h₂ : 3*(8*(y/3)+2) = 8*y+6 := by omega
        rw [twoLaps, h₁, lap_eight, h₂, lap_eight_plus_six]
    · simp only [stem, hn, ht, if_false]
      constructor
      · unfold Good
        omega
      · have h : 64*(y/3)+6 = 8*(8*(y/3))+6 := by omega
        rw [twoLaps, h, lap_eight_plus_six, lap_eight, hy]

theorem run_add (state : Phase × Nat) (a b : Nat) :
    run state (a+b) = run (run state a) b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    exact congrArg (fun z : Phase × Nat => (z.1.next, step z.1 z.2)) ih

theorem run_blocks (k n : Nat) :
    run (.plus, n) (6*k) = (.plus, Tree.advanceBlocks k n) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    rw [show 6*(k+1) = 6+6*k by omega, run_add, six_steps, ih]
    rfl

/-- Even inverse steps to a given phase-zero state, from each possible launch phase. -/
def startValue : Phase → Nat → Nat
  | .plus, z => z
  | .coast, z => 4*(z+1)
  | .minus, z => 2*(z+1)

def toZero : Phase → Nat
  | .plus => 0 | .coast => 2 | .minus => 1

private theorem start_run (p : Phase) (z : Nat) :
    run (p, startValue p z) (toZero p) = (.plus, z) := by
  cases p with
  | plus => rfl
  | coast =>
    change (.plus, T (T (4*(z+1))) - 1) = (Phase.plus, z)
    rw [show 4*(z+1) = 2*(2*(z+1)) by omega, even_step, even_step]
    simp
  | minus =>
    change (.plus, T (2*(z+1)) - 1) = (Phase.plus, z)
    rw [even_step]
    simp

/-- Lift the target backwards from its phase to phase zero. -/
def targetOrigin : Phase → Nat → Nat
  | .plus, y => y
  | .coast, y => 2*(y-1)
  | .minus, y => 2*(2*y-1)

def fromZero : Phase → Nat
  | .plus => 0 | .coast => 1 | .minus => 2

private theorem target_run (p : Phase) (y : Nat) (h : Safe p y) :
    run (.plus, targetOrigin p y) (fromZero p) = (p,y) := by
  cases p with
  | plus => rfl
  | coast =>
    change (.coast, T (2*(y-1))+1) = (Phase.coast, y)
    rw [even_step, show y-1+1 = y by change 0<y at h; omega]
  | minus =>
    change (.minus, T (T (2*(2*y-1))+1)) = (Phase.minus, y)
    rw [even_step, show 2*y-1+1 = 2*y by change 0<y at h; omega, even_step]

/-- At least 2^k distinct positive starts, at any requested launch phase, hit the same
safe target after the displayed number of individual updates. Earlier visits are allowed. -/
theorem all_phase_preimages (launch target : Phase) (y : Nat) (safe : Safe target y) (k : Nat) :
    ∃ seed : Fin (2^k) → Nat,
      (∀ i j, seed i = seed j → i = j) ∧
      ∀ i, 0 < seed i ∧
        seed i < startValue launch (64^k * (stem (targetOrigin target y) + 1)) ∧
        run (launch, seed i) (toZero launch + 6*k + 6 + fromZero target) = (target,y) := by
  let z := targetOrigin target y
  obtain ⟨eligible, tail⟩ := stem_spec z
  obtain ⟨leaf, injective, hleaf⟩ := Tree.fixed_depth_lower_bound eligible k
  refine ⟨fun i => startValue launch (leaf i), ?_, ?_⟩
  · intro i j h
    apply injective
    cases launch <;> simp [startValue] at h <;> omega
  · intro i
    obtain ⟨⟨hp, _⟩, hb, hr⟩ := hleaf i
    refine ⟨?_, ?_, ?_⟩
    · cases launch <;> simp [startValue] <;> omega
    · change startValue launch (leaf i) < startValue launch (64^k * (stem z + 1))
      cases launch <;> simp only [startValue] <;> omega
    · rw [run_add, run_add (launch, _) _ 6, run_add (launch, _) (toZero launch),
          start_run, run_blocks, hr, six_steps, tail]
      exact target_run target y safe

end Collatz.Coverage
