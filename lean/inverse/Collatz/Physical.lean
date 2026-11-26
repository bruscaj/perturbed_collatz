import Std

namespace Collatz.Physical

/-- Chronological periodic forcing, with the nonempty length encoded in the type. -/
structure Word where
  periodPred : Nat
  impulse : Fin (periodPred + 1) → Int

abbrev State (w : Word) := Fin (w.periodPred + 1) × Int

def shortcut (n : Int) : Int :=
  if n % 2 = 0 then n / 2 else (3*n+1)/2

def step (w : Word) (s : State w) : State w :=
  (s.1 + 1, shortcut s.2 + w.impulse s.1)

def run {α : Type} (f : α → α) (n : Nat) (x : α) : α :=
  match n with
  | 0 => x
  | k+1 => run f k (f x)

theorem run_add {α : Type} (f : α → α) (a b : Nat) (x : α) :
    run f (a+b) x = run f b (run f a x) := by
  induction a generalizing x with
  | zero => simp [run]
  | succ a ih => simpa [Nat.succ_add, run] using ih (f x)

def Conservative (w : Word) : Prop := (List.ofFn w.impulse).sum = 0
def Safe (w : Word) (s : State w) : Prop := ∀ k, 0 ≤ (run (step w) k s).2
def Admissible (w : Word) : Prop := ∀ i n, 0 < n → Safe w (i,n)

def Bounded (w : Word) (s : State w) : Prop := ∃ B, ∀ k, (run (step w) k s).2.natAbs ≤ B
def Escapes (w : Word) (s : State w) : Prop :=
  ∀ B, ∃ start, ∀ k ≥ start, B < (run (step w) k s).2.natAbs
def EventuallyPeriodic (w : Word) (s : State w) : Prop :=
  ∃ k p, 0 < p ∧ run (step w) (k+p) s = run (step w) k s

def Primitive (w : Word) : Prop :=
  ∀ r : Fin (w.periodPred+1), (∀ i, w.impulse (i+r) = w.impulse i) → r = 0

def Reaches {α : Type} (f : α → α) (target : α → Prop) (x : α) :=
  ∃ k, target (run f k x)

/-- A single fixed word and cycle graph serve every listed seed and every launch phase. -/
def Synchronizes (w : Word) (cycle : Fin (w.periodPred+1) → Int) (seeds : List Int) : Prop :=
  (∀ i, step w (i,cycle i) = (i+1,cycle (i+1))) ∧
  ∀ n ∈ seeds, ∀ i, Reaches (step w) (fun s => s.2 = cycle s.1) (i,n)

theorem reaches_prepend {α : Type} {f : α → α} {target : α → Prop}
    {x : α} (a : Nat) (h : Reaches f target (run f a x)) : Reaches f target x := by
  obtain ⟨b,h⟩ := h
  exact ⟨a+b, (run_add f a b x).symm ▸ h⟩

theorem target_invariant {α : Type} {f : α → α} {target : α → Prop}
    (closed : ∀ x, target x → target (f x)) (k : Nat) (x : α) (hx : target x) :
    target (run f k x) := by
  induction k generalizing x with
  | zero => exact hx
  | succ k ih => exact ih (f x) (closed x hx)

/-- A capture already in the past remains a capture from a later point on an invariant target. -/
theorem reaches_tail {α : Type} {f : α → α} {target : α → Prop}
    (closed : ∀ x, target x → target (f x)) {x : α} (hx : Reaches f target x) (a : Nat) :
    Reaches f target (run f a x) := by
  obtain ⟨k,hk⟩ := hx
  by_cases h : a ≤ k
  · refine ⟨k-a,?_⟩
    rw [← run_add, Nat.add_sub_cancel' h]
    exact hk
  · refine ⟨0,?_⟩
    change target (run f a x)
    have ha : a = k+(a-k) := by omega
    rw [ha,run_add]
    exact target_invariant closed _ _ hk

theorem coalescence {α : Type} {f : α → α} {target : α → Prop}
    (closed : ∀ x, target x → target (f x)) {x y : α} (a b : Nat)
    (merge : run f a x = run f b y) (hy : Reaches f target y) : Reaches f target x := by
  apply reaches_prepend a
  rw [merge]
  exact reaches_tail closed hy b

theorem reduce_by_rank {α : Type} (capture : α → Prop) (rank : α → Nat)
    (exception : α → Prop)
    (cover : ∀ x, ¬exception x → capture x ∨
      ∃ y, rank y < rank x ∧ (capture y → capture x))
    (remaining : ∀ x, exception x → capture x) (x : α) : capture x := by
  suffices ∀ k y, rank y = k → capture y from this _ x rfl
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro y hy
    by_cases exc : exception y
    · exact remaining y exc
    · rcases cover y exc with done | ⟨z, hz, transfer⟩
      · exact done
      · exact transfer (ih (rank z) (hy ▸ hz) z rfl)

end Collatz.Physical
