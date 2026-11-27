import Std

/-!
A common positive counter terminates every internal path, including arbitrary
switching, when 2*C_next = a*C_current with a coprime to 2.

The main theorem avoids a library-specific valuation definition. It proves the
stronger divisibility invariant 2^k | C_initial for every k-edge path, then an
explicit bound k <= log2 C_initial. Concrete affine identities are below.
-/
namespace AffineCounterTermination

theorem counter_path_divisibility
    (counter multiplier : Nat → Nat) (k : Nat)
    (coprime : ∀ j, j < k → Nat.Coprime 2 (multiplier j))
    (edge : ∀ j, j < k → 2*counter (j+1) = multiplier j*counter j) :
    2^k ∣ counter 0 := by
  induction k generalizing counter multiplier with
  | zero => simp
  | succ k ih =>
    have tail : 2^k ∣ counter 1 := by
      apply ih (fun j => counter (j+1)) (fun j => multiplier (j+1))
      · intro j hj
        exact coprime (j+1) (by omega)
      · intro j hj
        exact edge (j+1) (by omega)
    have multiplied : 2^(k+1) ∣ 2*counter 1 := by
      have h := Nat.mul_dvd_mul_left 2 tail
      simpa [Nat.pow_succ,Nat.mul_comm] using h
    rw [edge 0 (by omega)] at multiplied
    exact ((coprime 0 (by omega)).pow_left (k+1)).dvd_of_dvd_mul_left multiplied

theorem counter_path_length_bound
    (counter multiplier : Nat → Nat) (k : Nat)
    (positive : 0 < counter 0)
    (coprime : ∀ j, j < k → Nat.Coprime 2 (multiplier j))
    (edge : ∀ j, j < k → 2*counter (j+1) = multiplier j*counter j) :
    k ≤ Nat.log2 (counter 0) := by
  have divides := counter_path_divisibility counter multiplier k coprime edge
  apply (Nat.le_log2 (by omega)).mpr
  exact Nat.le_of_dvd positive divides

/-- Positivity is needed only at the first counter. Counter=0 would admit an
infinite all-zero sequence and must not be hidden by a valuation convention. -/
theorem no_infinite_positive_counter_path
    (counter multiplier : Nat → Nat)
    (positive : 0 < counter 0)
    (coprime : ∀ j, Nat.Coprime 2 (multiplier j)) :
    ¬ (∀ j, 2*counter (j+1) = multiplier j*counter j) := by
  intro all
  have bound := counter_path_length_bound counter multiplier
    (Nat.log2 (counter 0)+1) positive
    (fun j _ => coprime j) (fun j _ => all j)
  omega

/-- Useful finite certificate: if an internal edge is possible at every prefix
of length B+1, its initial positive counter must be at least 2^(B+1). -/
theorem bounded_counter_forces_exit
    (counter multiplier : Nat → Nat) (bound : Nat)
    (positive : 0 < counter 0) (small : counter 0 < 2^(bound+1))
    (coprime : ∀ j, j < bound+1 → Nat.Coprime 2 (multiplier j)) :
    ¬ (∀ j, j < bound+1 → 2*counter (j+1) = multiplier j*counter j) := by
  intro all
  have divides := counter_path_divisibility counter multiplier (bound+1) coprime all
  have large := Nat.le_of_dvd positive divides
  omega

/-! Concrete seven-mode paired-orbit component, discovered independently by
the switching analysis. Phases are zero-based. The physical model is represented
in its established centered z-coordinate: U at phases 0,1,2,4,5; T at 3,6.
-/

inductive Mode where
  | m0 | m1 | m2 | m3 | m4 | m5 | m6
  deriving DecidableEq, Repr

open Mode

def nextMode : Mode → Mode
  | m0 => m1 | m1 => m2 | m2 => m3 | m3 => m4
  | m4 => m5 | m5 => m6 | m6 => m0

def phase : Mode → Nat
  | m0 => 2 | m1 => 3 | m2 => 4 | m3 => 5
  | m4 => 6 | m5 => 0 | m6 => 1

def alpha : Mode → Nat
  | m0 => 1 | m1 => 1 | m2 => 3 | m3 => 9
  | m4 => 3 | m5 => 3 | m6 => 3

def beta : Mode → Nat
  | m0 => 2 | m1 => 3 | m2 => 5 | m3 => 3
  | m4 => 2 | m5 => 2 | m6 => 3

def offset : Mode → Nat
  | m0 => 468 | m1 => 702 | m2 => 351 | m3 => 118
  | m4 => 177 | m5 => 208 | m6 => 312

def multiplier : Mode → Nat
  | m1 => 1 | m2 => 1 | _ => 3

def increment : Mode → Nat
  | m2 => 1 | m4 => 1 | _ => 0

def parity : Mode → Nat
  | m2 => 1 | m4 => 1 | _ => 0

def counter (m : Mode) (x : Nat) : Nat := 115*x+offset m
def nextX (m : Mode) (x : Nat) : Nat := (multiplier m*x+increment m)/2
def Guard (m : Mode) (x : Nat) : Prop := 0 < x ∧ x%2 = parity m

def centeredTick (s : Nat × Nat) : Nat × Nat :=
  ((s.1+1)%7,
    if s.1 = 3 ∨ s.1 = 6 then
      if s.2%2 = 0 then s.2/2 else (3*s.2+1)/2
    else if s.2%2 = 0 then 3*s.2/2 else (s.2+1)/2)

theorem offset_identities (m : Mode) :
    115*increment m+2*offset (nextMode m) = multiplier m*offset m := by
  cases m <;> decide

theorem multiplier_coprime (m : Mode) : Nat.Coprime 2 (multiplier m) := by
  cases m <;> decide

theorem counter_positive (m : Mode) (x : Nat) : 0 < counter m x := by
  cases m <;> simp [counter,offset] <;> omega

theorem guard_iff_counter_even (m : Mode) (x : Nat) :
    x%2 = parity m ↔ counter m x%2 = 0 := by
  cases m <;> simp [parity,counter,offset] <;> omega

theorem nextX_positive (m : Mode) (x : Nat) (guard : Guard m x) :
    0 < nextX m x := by
  cases m <;> simp_all [Guard,parity,nextX,multiplier,increment] <;> omega

/-- Every internal mode edge is an actual simultaneous centered-system tick of
the ordered pair. Thus the counter is attached to concrete orbit transitions. -/
theorem paired_tick (m : Mode) (x : Nat) (guard : Guard m x) :
    centeredTick (phase m,x) = (phase (nextMode m),nextX m x) ∧
    centeredTick (phase m,alpha m*x+beta m) =
      (phase (nextMode m),alpha (nextMode m)*nextX m x+beta (nextMode m)) := by
  cases m <;>
    simp_all [Guard,parity,phase,nextMode,nextX,multiplier,increment,alpha,beta,
      centeredTick] <;> first | omega | (split <;> omega)

theorem concrete_counter_edge (m : Mode) (x : Nat) (guard : Guard m x) :
    2*counter (nextMode m) (nextX m x) = multiplier m*counter m x := by
  cases m <;>
    simp_all [Guard,parity,counter,offset,nextMode,nextX,multiplier,increment] <;> omega

abbrev ComponentState := Mode × Nat

def InternalEdge (s t : ComponentState) : Prop :=
  Guard s.1 s.2 ∧ t = (nextMode s.1,nextX s.1 s.2)

/-- All legal paths through the component obey the length bound. This covers
every possible initial mode and positive initial integer, not sampled seeds. -/
theorem seven_mode_path_length_bound (s : Nat → ComponentState) (k : Nat)
    (edges : ∀ j, j < k → InternalEdge (s j) (s (j+1))) :
    k ≤ Nat.log2 (counter (s 0).1 (s 0).2) := by
  apply counter_path_length_bound
    (fun j => counter (s j).1 (s j).2) (fun j => multiplier (s j).1) k
  · exact counter_positive _ _
  · intro j _
    exact multiplier_coprime _
  · intro j hj
    obtain ⟨guard,next⟩ := edges j hj
    rw [next]
    exact concrete_counter_edge _ _ guard

theorem seven_mode_no_infinite_internal_path (s : Nat → ComponentState) :
    ¬ (∀ j, InternalEdge (s j) (s (j+1))) := by
  intro edges
  have bound := seven_mode_path_length_bound s
    (Nat.log2 (counter (s 0).1 (s 0).2)+1) (fun j _ => edges j)
  omega

end AffineCounterTermination

#print axioms AffineCounterTermination.counter_path_divisibility
#print axioms AffineCounterTermination.counter_path_length_bound
#print axioms AffineCounterTermination.no_infinite_positive_counter_path
#print axioms AffineCounterTermination.bounded_counter_forces_exit
#print axioms AffineCounterTermination.offset_identities
#print axioms AffineCounterTermination.guard_iff_counter_even
#print axioms AffineCounterTermination.nextX_positive
#print axioms AffineCounterTermination.paired_tick
#print axioms AffineCounterTermination.concrete_counter_edge
#print axioms AffineCounterTermination.seven_mode_path_length_bound
#print axioms AffineCounterTermination.seven_mode_no_infinite_internal_path
