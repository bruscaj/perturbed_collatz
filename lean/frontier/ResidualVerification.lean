import Std

/-!
An anchored residual-refinement interface.

This file proves generic verification rules, not a Collatz convergence theorem.
The original launch stays fixed throughout an inner certificate search. An
independent well-founded rank controls retries; the final result must be a
capture proof or a strict reduction of the original launch rank. In particular,
the inner rank is not silently substituted for the final induction rank.

Only `Std` is imported. No `sorry`, `admit`, custom axiom or `native_decide`.
-/
namespace ResidualVerification

universe u v w
variable {S : Type u} {C : Type v} {A : Type w}

/-- A finite path, with its exact number of retry edges. -/
inductive Steps (R : C → C → Prop) : Nat → C → C → Prop
  | nil (c : C) : Steps R 0 c c
  | cons {k : Nat} {c d e : C} : R c d → Steps R k d e → Steps R (k+1) c e

/-- Local, existential progress suffices to produce a finite successful proof
path. It does not assert that every possible choice of `R`-edge terminates. -/
theorem finite_exit_of_local_progress
    (R : C → C → Prop) (Inv Done : C → Prop)
    (mu : C → A) (lt : A → A → Prop) (wf : WellFounded lt)
    (progress : ∀ c, Inv c → Done c ∨
      ∃ d, R c d ∧ Inv d ∧ lt (mu d) (mu c))
    (c : C) (hc : Inv c) :
    ∃ k d, Steps R k c d ∧ Inv d ∧ Done d := by
  have main : ∀ c, Inv c → ∃ k d, Steps R k c d ∧ Inv d ∧ Done d := by
    intro c
    induction c using (InvImage.wf mu wf).induction with
    | h c ih =>
      intro hc
      rcases progress c hc with done | advance
      · exact ⟨0,c,Steps.nil c,hc,done⟩
      · obtain ⟨d,edge,hd,less⟩ := advance
        obtain ⟨k,e,path,he,done⟩ := ih d less hd
        exact ⟨k+1,e,Steps.cons edge path,he,done⟩
  exact main c hc

/-- A global capture theorem assembled from local refinement certificates.

`Valid x c` must preserve the original launch x and the semantics of the
accumulated certificate. The terminal proof is compared with `rank x`, not the
rank of the last restart state. `Transfer` can be a phase-correct common-future
relation; its required capture implication is an explicit hypothesis.

The open mathematical work in an application is the universal `progress`
premise (including total guard coverage), a concrete well-founded retry rank,
and the terminal soundness proof. This theorem supplies none of these for free.
-/
theorem capture_of_anchored_refinement
    (Captured : S → Prop) (rank : S → Nat) (Transfer : S → S → Prop)
    (transfer : ∀ x y, Transfer x y → Captured y → Captured x)
    (initial : S → C) (Valid : S → C → Prop)
    (R : C → C → Prop) (Done : C → Prop)
    (mu : C → A) (lt : A → A → Prop) (wf : WellFounded lt)
    (start : ∀ x, Valid x (initial x))
    (progress : ∀ x c, Valid x c → Done c ∨
      ∃ d, R c d ∧ Valid x d ∧ lt (mu d) (mu c))
    (terminal : ∀ x c, Valid x c → Done c →
      Captured x ∨ ∃ y, Transfer x y ∧ rank y < rank x) :
    ∀ x, Captured x := by
  have all : ∀ n x, rank x = n → Captured x := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro x hx
      obtain ⟨_,c,_,hc,done⟩ := finite_exit_of_local_progress R (Valid x) Done
        mu lt wf (progress x) (initial x) (start x)
      rcases terminal x c hc done with captured | reduced
      · exact captured
      · obtain ⟨y,related,less⟩ := reduced
        exact transfer x y related (ih (rank y) (by omega) y rfl)
  intro x
  exact all (rank x) x rfl

/-- Two natural counters give a concrete retry order. A secondary counter may
reset arbitrarily only when the primary counter strictly decreases. -/
def RetryLess (new old : Nat × Nat) : Prop :=
  new.1 < old.1 ∨ new.1 = old.1 ∧ new.2 < old.2

theorem retryLess_wellFounded : WellFounded RetryLess := by
  have h := (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf
  apply Subrelation.wf (r := Prod.Lex Nat.lt Nat.lt) (h₂ := h)
  intro a b hab
  exact Prod.lex_def.mpr hab

theorem reset_allowed_when_primary_drops
    (newBudget oldBudget newCounter oldCounter : Nat)
    (h : newBudget < oldBudget) :
    RetryLess (newBudget,newCounter) (oldBudget,oldCounter) := Or.inl h

theorem retry_allowed_when_counter_drops
    (budget newCounter oldCounter : Nat) (h : newCounter < oldCounter) :
    RetryLess (budget,newCounter) (budget,oldCounter) := Or.inr ⟨rfl,h⟩

theorem unchanged_budget_forbids_counter_reset
    (budget newCounter oldCounter : Nat) (h : oldCounter ≤ newCounter) :
    ¬ RetryLess (budget,newCounter) (budget,oldCounter) := by
  unfold RetryLess
  simp only [Nat.lt_irrefl, false_or, true_and]
  omega

/-! Negative controls for the quantifiers and switching assumptions. -/

/-- A proof-search relation that permits both useful descent and useless
stuttering. Existentially successful choice does not prove all-choice success. -/
def OptionalStep (x y : Nat) : Prop := y = x ∨ y+1 = x

theorem optional_step_has_finite_exit (x : Nat) :
    ∃ k y, Steps OptionalStep k x y ∧ y = 0 := by
  have progress : ∀ n : Nat, True → n = 0 ∨
      ∃ m, OptionalStep n m ∧ True ∧ m < n := by
    intro n _
    cases n with
    | zero => exact Or.inl rfl
    | succ n => exact Or.inr ⟨n,Or.inr rfl,True.intro,by omega⟩
  obtain ⟨k,y,path,_,done⟩ := finite_exit_of_local_progress OptionalStep
    (fun _ => True) (fun n => n = 0) id Nat.lt Nat.lt_wfRel.wf progress x True.intro
  exact ⟨k,y,path,done⟩

theorem optional_step_has_infinite_avoiding_choice :
    ∃ s : Nat → Nat, (∀ n, OptionalStep (s n) (s (n+1))) ∧ (∀ n, s n ≠ 0) := by
  refine ⟨fun _ => 1,fun _ => Or.inl rfl,?_⟩
  intro n
  change (1 : Nat) ≠ 0
  decide

/-- Each alternating edge decreases one of two local natural counters. -/
def aCounter (b : Bool) : Nat := if b then 1 else 0
def bCounter (b : Bool) : Nat := if b then 0 else 1

theorem every_flip_decreases_a_local_counter (b : Bool) :
    aCounter (!b) < aCounter b ∨ bCounter (!b) < bCounter b := by
  cases b <;> decide

def alternating : Nat → Bool
  | 0 => false
  | n+1 => !(alternating n)

theorem alternating_repeats_forever :
    ∀ n, alternating (n+1) = !(alternating n) := fun _ => rfl

theorem local_counter_union_not_wellFounded :
    ¬ WellFounded (fun new old : Bool => new = !old) := by
  intro wf
  have absurd : ∀ b : Bool, False := by
    intro b
    induction b using wf.induction with
    | h b ih => exact ih (!b) rfl
  exact absurd false

/-- Thus two individually decreasing local mechanisms can compose into a
cycle. No natural rank can decrease on the entire alternating relation. -/
theorem no_common_rank_for_alternation :
    ¬ ∃ rank : Bool → Nat, ∀ b, rank (!b) < rank b := by
  rintro ⟨rank,h⟩
  have left := h false
  have right := h true
  simp only [Bool.not_false,Bool.not_true] at left right
  omega

end ResidualVerification

#print axioms ResidualVerification.finite_exit_of_local_progress
#print axioms ResidualVerification.capture_of_anchored_refinement
#print axioms ResidualVerification.retryLess_wellFounded
#print axioms ResidualVerification.unchanged_budget_forbids_counter_reset
#print axioms ResidualVerification.optional_step_has_finite_exit
#print axioms ResidualVerification.optional_step_has_infinite_avoiding_choice
#print axioms ResidualVerification.every_flip_decreases_a_local_counter
#print axioms ResidualVerification.local_counter_union_not_wellFounded
#print axioms ResidualVerification.no_common_rank_for_alternation
