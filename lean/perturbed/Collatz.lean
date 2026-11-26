import Lean

namespace PerturbedCollatz

def collatz (value : Nat) : Nat :=
  if value % 2 = 0 then value / 2 else (3 * value + 1) / 2

def step (offset : Option Bool) (value : Nat) : Nat :=
  if value = 0 then 0 else
    match offset with
    | none => collatz value
    | some true => collatz value + 1
    | some false => collatz value - 1

theorem step_lift (offset : Option Bool) (value shift : Nat) (positive : 0 < value) :
    step offset (value + 2 * shift) =
      step offset value + (if value % 2 = 0 then shift else 3 * shift) := by
  have shiftedPositive : value + 2 * shift ≠ 0 := by omega
  have nonzero : value ≠ 0 := by omega
  have parity : (value + 2 * shift) % 2 = value % 2 := by omega
  unfold step collatz
  simp only [if_neg shiftedPositive, if_neg nonzero, parity]
  by_cases even : value % 2 = 0 <;> simp only [even, if_true, if_false] <;> cases offset with
  | none => dsimp; omega
  | some sign => cases sign <;> dsimp <;> omega

def orbit (offset : Nat → Option Bool) (seed : Nat) : Nat → Nat
  | 0 => seed
  | ticks + 1 => step (offset ticks) (orbit offset seed ticks)

theorem orbit_seed_lift (offset : Nat → Option Bool) (seed ticks shift : Nat)
    (positive : ∀ index, index < ticks → 0 < orbit offset seed index) :
    ∃ scale : Nat, scale % 2 = 1 ∧
      orbit offset (seed + 2 ^ ticks * shift) ticks = orbit offset seed ticks + scale * shift := by
  induction ticks generalizing shift with
  | zero => exact ⟨1, by decide, by simp [orbit]⟩
  | succ ticks ih =>
    obtain ⟨scale, odd, lifted⟩ := ih (2 * shift) (fun index earlier => positive index (by omega))
    have seedEq : seed + 2 ^ (ticks + 1) * shift = seed + 2 ^ ticks * (2 * shift) := by
      rw [Nat.pow_succ, Nat.mul_assoc]
    have stepEq := step_lift (offset ticks) (orbit offset seed ticks) (scale * shift)
      (positive ticks (by omega))
    rw [seedEq, orbit, orbit, lifted]
    rw [show scale * (2 * shift) = 2 * (scale * shift) by ac_rfl, stepEq]
    by_cases even : orbit offset seed ticks % 2 = 0
    · exact ⟨scale, odd, by simp [even]⟩
    · exact ⟨3 * scale, by omega, by simp [even, Nat.mul_assoc]⟩

theorem orbit_shift (offset : Nat → Option Bool) (seed start ticks : Nat) :
    orbit offset seed (start + ticks) =
      orbit (fun phase => offset (start + phase)) (orbit offset seed start) ticks := by
  induction ticks with
  | zero => simp [orbit]
  | succ ticks ih =>
    change step (offset (start + ticks)) (orbit offset seed (start + ticks)) =
      step (offset (start + ticks))
        (orbit (fun phase => offset (start + phase)) (orbit offset seed start) ticks)
    rw [ih]

theorem shrinking_stretch_blocks_bounded_returns (value boundary : Nat → Nat) (cap start : Nat)
    (origin : boundary 0 = 0)
    (advance : ∀ index, boundary index < boundary (index + 1) ∧
      boundary (index + 1) ≤ boundary index + cap ∧
      value (boundary index) < value (boundary (index + 1)))
    (shrink : ∀ left right, start ≤ left → left ≤ right → right ≤ start + 2 * cap →
      value right ≤ value left) : False := by
  have capPositive : 0 < cap := by have first := advance 0; omega
  have near (tick : Nat) : ∃ index, tick ≤ boundary index ∧ boundary index < tick + cap := by
    induction tick with
    | zero => exact ⟨0, by omega, by omega⟩
    | succ tick ih =>
      obtain ⟨index, lower, upper⟩ := ih
      by_cases later : tick + 1 ≤ boundary index
      · exact ⟨index, later, by omega⟩
      · have next := advance index
        exact ⟨index + 1, by omega, by omega⟩
  obtain ⟨index, lower, upper⟩ := near start
  obtain ⟨later, bounded, growth⟩ := advance index
  have notGrowing := shrink (boundary index) (boundary (index + 1)) lower (by omega) (by omega)
  omega

def adaptiveOffset (value : Nat) (owed : Bool) : Option Bool :=
  if value % 4 = 1 then some (!owed) else none

theorem adaptive_growth (value : Nat) (owed : Bool) (odd : value % 2 = 1) (large : 3 ≤ value) :
    let next := step (adaptiveOffset value owed) value
    next % 2 = 1 ∧ value + 1 ≤ next := by
  have nonzero : value ≠ 0 := by omega
  have notEven : value % 2 ≠ 0 := by omega
  by_cases adjust : value % 4 = 1
  · cases owed <;> simp [adaptiveOffset, step, collatz, adjust, nonzero, notEven] <;> omega
  · simp [adaptiveOffset, step, collatz, adjust, nonzero, notEven]
    omega

def block (offsets : List (Option Bool)) (seed : Nat) : Nat :=
  offsets.foldl (fun value offset => step offset value) seed

private def evenInputs : List (Option Bool) → Nat → Prop
  | [], _ => True
  | offset :: rest, seed => 0 < seed ∧ seed % 2 = 0 ∧ evenInputs rest (step offset seed)

private theorem evenBlock_lift (offsets : List (Option Bool)) (seed shift : Nat)
    (inputs : evenInputs offsets seed) :
    block offsets (seed + 2 ^ offsets.length * shift) = block offsets seed + shift := by
  induction offsets generalizing seed with
  | nil => simp [block]
  | cons offset rest ih =>
    obtain ⟨positive, even, remaining⟩ := inputs
    change block rest (step offset (seed + 2 ^ (rest.length + 1) * shift)) =
      block rest (step offset seed) + shift
    rw [Nat.pow_succ, show 2 ^ rest.length * 2 * shift = 2 * (2 ^ rest.length * shift) by ac_rfl,
      step_lift offset seed _ positive, if_pos even]
    exact ih (step offset seed) remaining

def reductionLong : List (Option Bool) :=
  [some false, some false, none, some true, some false, some true, some true, none]

def reductionShort : List (Option Bool) :=
  (List.replicate 4 [some false, some true]).flatten

def reductionSeed : Nat → Nat
  | 0 => 21
  | index + 1 => 5206 + 256 * (reductionSeed index - 21)

private theorem reductionSeed_lower (index : Nat) : 21 ≤ reductionSeed index := by
  cases index <;> simp [reductionSeed] <;> omega

theorem reductionSeed_increases (index : Nat) : reductionSeed index < reductionSeed (index + 1) := by
  have lower := reductionSeed_lower index
  simp only [reductionSeed]
  omega

theorem reduction_cycle : block reductionLong 21 = 21 ∧ block reductionShort 21 = 21 := by
  decide

theorem reduction_return (index : Nat) :
    block reductionLong (reductionSeed (index + 1)) = reductionSeed index ∧
    block reductionShort (reductionSeed (index + 1)) = reductionSeed index := by
  have lower := reductionSeed_lower index
  have longInputs : evenInputs reductionLong 5206 := by
    simp only [reductionLong, evenInputs]
    decide
  have shortInputs : evenInputs reductionShort 5206 := by
    change evenInputs [some false, some true, some false, some true,
      some false, some true, some false, some true] 5206
    simp only [evenInputs]
    decide
  have longLift := evenBlock_lift reductionLong 5206 (reductionSeed index - 21) longInputs
  have shortLift := evenBlock_lift reductionShort 5206 (reductionSeed index - 21) shortInputs
  change block reductionLong (5206 + 256 * (reductionSeed index - 21)) =
    21 + (reductionSeed index - 21) at longLift
  change block reductionShort (5206 + 256 * (reductionSeed index - 21)) =
    21 + (reductionSeed index - 21) at shortLift
  have cancel : 21 + (reductionSeed index - 21) = reductionSeed index := by omega
  exact ⟨longLift.trans cancel, shortLift.trans cancel⟩

private theorem matching_tails {State : Type} (path : Nat → State)
    (deterministic : ∀ left right, path left = path right → path (left + 1) = path (right + 1))
    (early late : Nat) (equal : path early = path late) (offset : Nat) : path (early + offset) = path (late + offset) := by
  induction offset with
  | zero => exact equal
  | succ offset ih => exact deterministic _ _ ih

private theorem boundedAfterRepeat {State : Type} (path : Nat → State) (value : State → Nat)
    (deterministic : ∀ left right, path left = path right → path (left + 1) = path (right + 1))
    (early late : Nat) (before : early < late) (repeatState : path early = path late) :
    ∃ bound, ∀ tick, value (path tick) ≤ bound := by
  have prefixBound : ∀ length : Nat, ∃ bound, ∀ tick < length, value (path tick) ≤ bound := by
    intro length
    induction length with
    | zero => exact ⟨0, by intro tick impossible; omega⟩
    | succ length ih =>
      obtain ⟨bound, covers⟩ := ih
      refine ⟨max bound (value (path length)), ?_⟩
      intro tick inside
      by_cases last : tick = length
      · subst tick; exact Nat.le_max_right _ _
      · exact Nat.le_trans (covers tick (by omega)) (Nat.le_max_left _ _)
  obtain ⟨bound, covers⟩ := prefixBound late
  refine ⟨bound, fun tick => Nat.strongRecOn tick ?_⟩
  intro index ih
  by_cases inside : index < late
  · exact covers _ inside
  · have same := matching_tails path deterministic early late repeatState (index - late)
    rw [show late + (index - late) = index by omega] at same
    rw [← same]
    exact ih _ (by omega)

private theorem eventuallyAvoids {State : Type} (path : Nat → State)
    (distinct : ∀ left right, path left = path right → left = right) (states : List State) :
    ∃ cutoff, ∀ tick ≥ cutoff, path tick ∉ states := by
  induction states with
  | nil => exact ⟨0, by simp⟩
  | cons head rest ih =>
    obtain ⟨cutoff, avoids⟩ := ih
    by_cases visited : ∃ tick, path tick = head
    · obtain ⟨visit, hit⟩ := visited
      refine ⟨max cutoff (visit + 1), ?_⟩
      intro tick later member
      rcases List.mem_cons.mp member with equal | inside
      · have same := distinct tick visit (equal.trans hit.symm); omega
      · exact avoids tick (by omega) inside
    · refine ⟨cutoff, ?_⟩
      intro tick later member
      rcases List.mem_cons.mp member with equal | inside
      · exact visited ⟨tick, equal⟩
      · exact avoids tick later inside

private theorem escape_of_distinct (period : Nat) (path : Nat → Nat × Nat)
    (phaseBound : ∀ tick, (path tick).2 < period) (distinct : ∀ left right, path left = path right → left = right) :
    ∀ bound, ∃ cutoff, ∀ tick ≥ cutoff, bound < (path tick).1 := by
  intro bound
  let small := (List.range (bound + 1)).flatMap fun value => (List.range period).map fun phase => (value, phase)
  obtain ⟨cutoff, avoids⟩ := eventuallyAvoids path distinct small
  refine ⟨cutoff, ?_⟩
  intro tick later
  apply Classical.byContradiction
  intro notAbove
  apply avoids tick later
  exact List.mem_flatMap.mpr ⟨(path tick).1, List.mem_range.mpr (by omega),
    List.mem_map.mpr ⟨(path tick).2, List.mem_range.mpr (phaseBound tick), rfl⟩⟩

theorem unbounded_iff_escape (period : Nat) (path : Nat → Nat × Nat)
    (phaseBound : ∀ tick, (path tick).2 < period)
    (deterministic : ∀ left right, path left = path right → path (left + 1) = path (right + 1)) :
    (∀ bound, ∃ tick, bound < (path tick).1) ↔ (∀ bound, ∃ cutoff, ∀ tick ≥ cutoff, bound < (path tick).1) := by
  constructor
  · intro peaks bound
    have noRepeat (left right : Nat) (before : left < right) (equal : path left = path right) : False := by
      obtain ⟨cap, bounded⟩ := boundedAfterRepeat path Prod.fst deterministic left right before equal
      obtain ⟨tick, above⟩ := peaks cap
      exact (Nat.not_lt.mpr (bounded tick)) above
    have distinct (left right : Nat) (equal : path left = path right) : left = right := by
      apply Classical.byContradiction
      intro different
      by_cases before : left < right
      · exact noRepeat _ _ before equal
      · exact noRepeat _ _ (by omega) equal.symm
    exact escape_of_distinct period path phaseBound distinct bound
  · intro escapes bound
    obtain ⟨cutoff, above⟩ := escapes bound
    exact ⟨cutoff, above cutoff (Nat.le_refl _)⟩

theorem nonperiodic_parity_escapes (period : Nat) (path : Nat → Nat × Nat)
    (phaseBound : ∀ tick, (path tick).2 < period)
    (deterministic : ∀ left right, path left = path right → path (left + 1) = path (right + 1))
    (aperiodic : ∀ start length, 0 < length → ∃ tick ≥ start, (path tick).1 % 2 ≠ (path (tick + length)).1 % 2) :
    ∀ bound, ∃ cutoff, ∀ tick ≥ cutoff, bound < (path tick).1 := by
  apply escape_of_distinct period path phaseBound
  have noRepeat (early late : Nat) (before : early < late) (equal : path early = path late) : False := by
    obtain ⟨tick, afterStart, different⟩ := aperiodic early (late - early) (by omega)
    have same := matching_tails path deterministic early late equal (tick - early)
    rw [show early + (tick - early) = tick by omega, show late + (tick - early) = tick + (late - early) by omega] at same
    exact different (congrArg (fun state : Nat × Nat => state.1 % 2) same)
  intro left right equal
  apply Classical.byContradiction
  intro different
  by_cases before : left < right
  · exact noRepeat _ _ before equal
  · exact noRepeat _ _ (by omega) equal.symm

end PerturbedCollatz