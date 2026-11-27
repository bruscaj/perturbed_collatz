import Std

/-! Generic algebra for composing guarded common-future certificates.
No Collatz capture or arithmetic coverage hypothesis is proved here.
Every totality/coverage hypothesis appears explicitly in the theorem.
-/
namespace CollatzCoverAlgebra

universe u v w s

variable {S : Type s} {α : Type u} {β : Type v} {γ : Type w}

def run (f : S → S) : Nat → S → S
  | 0, x => x
  | n+1, x => f (run f n x)

theorem run_add (f : S → S) (a b : Nat) (x : S) :
    run f (a+b) x = run f b (run f a x) := by
  induction b with
  | zero => simp [run]
  | succ b ih => simp [run, ih]

/-- With one common clock, meeting by H is exactly equality in the kernel of f^H. -/
def MeetsBy (f : S → S) (H : Nat) (x y : S) : Prop :=
  ∃ k, k ≤ H ∧ run f k x = run f k y

theorem meetsBy_iff_final_equality (f : S → S) (H : Nat) (x y : S) :
    MeetsBy f H x y ↔ run f H x = run f H y := by
  constructor
  · rintro ⟨k,hk,meet⟩
    have split : H = k+(H-k) := by omega
    rw [split,run_add,run_add,meet]
  · intro meet
    exact ⟨H,Nat.le_refl H,meet⟩

/-- Therefore transitive closure of an exhaustive same-clock H classifier
cannot establish a new same-clock pair outside that classifier. -/
theorem meetsBy_trans {f : S → S} {H : Nat} {x y z : S}
    (left : MeetsBy f H x y) (right : MeetsBy f H y z) : MeetsBy f H x z := by
  apply (meetsBy_iff_final_equality f H x z).mpr
  exact ((meetsBy_iff_final_equality f H x y).mp left).trans
    ((meetsBy_iff_final_equality f H y z).mp right)

def Coalesces (f : S → S) (x y : S) : Prop :=
  ∃ a b, run f a x = run f b y

theorem coalesces_refl (f : S → S) (x : S) : Coalesces f x x :=
  ⟨0,0,rfl⟩

theorem coalesces_symm {f : S → S} {x y : S}
    (h : Coalesces f x y) : Coalesces f y x := by
  obtain ⟨a,b,h⟩ := h
  exact ⟨b,a,h.symm⟩

theorem coalesces_trans {f : S → S} {x y z : S}
    (hxy : Coalesces f x y) (hyz : Coalesces f y z) :
    Coalesces f x z := by
  obtain ⟨a,b,hxy⟩ := hxy
  obtain ⟨c,d,hyz⟩ := hyz
  refine ⟨a+c,d+b,?_⟩
  calc
    run f (a+c) x = run f c (run f a x) := run_add f a c x
    _ = run f c (run f b y) := congrArg (run f c) hxy
    _ = run f (b+c) y := (run_add f b c y).symm
    _ = run f (c+b) y := by rw [Nat.add_comm b c]
    _ = run f b (run f c y) := run_add f c b y
    _ = run f b (run f d z) := congrArg (run f b) hyz
    _ = run f (d+b) z := (run_add f d b z).symm

/-- The shared bridge may have any rank; no capture assertion about it is used. -/
theorem coalesces_via_bridge {f : S → S} {x bridge y : S}
    (left : Coalesces f bridge x) (right : Coalesces f bridge y) :
    Coalesces f x y :=
  coalesces_trans (coalesces_symm left) right

structure GuardedRule (α : Type u) (β : Type v) where
  enabled : α → Bool
  target : α → β

def compose (first : GuardedRule α β) (second : GuardedRule β γ) :
    GuardedRule α γ where
  enabled x := first.enabled x && second.enabled (first.target x)
  target x := second.target (first.target x)

theorem compose_domain (first : GuardedRule α β) (second : GuardedRule β γ) (x : α) :
    (compose first second).enabled x = true ↔
    first.enabled x = true ∧ second.enabled (first.target x) = true := by
  simp [compose]

/-- Composition of already decreasing rules cannot add a source outside the
first rule's original source domain. -/
theorem compose_domain_subset_first (first : GuardedRule α β)
    (second : GuardedRule β γ) (x : α)
    (h : (compose first second).enabled x = true) : first.enabled x = true :=
  ((compose_domain first second x).mp h).1

def Realizes (f : S → S) (source : α → S) (destination : β → S)
    (rule : GuardedRule α β) : Prop :=
  ∀ x, rule.enabled x = true → Coalesces f (source x) (destination (rule.target x))

/-- The two middle parameterizations must name the same actual states. -/
theorem realizes_compose {f : S → S} {source : α → S} {middle : β → S}
    {destination : γ → S} {first : GuardedRule α β} {second : GuardedRule β γ}
    (hfirst : Realizes f source middle first)
    (hsecond : Realizes f middle destination second) :
    Realizes f source destination (compose first second) := by
  intro x hx
  obtain ⟨ha,hb⟩ := (compose_domain first second x).mp hx
  exact coalesces_trans (hfirst x ha) (hsecond (first.target x) hb)

/-- A list order supplies a canonical selector for overlapping source guards. -/
def select (rules : List (GuardedRule α β)) (x : α) : Option β :=
  match rules with
  | [] => none
  | rule :: rest => if rule.enabled x then some (rule.target x) else select rest x

theorem select_some_spec (rules : List (GuardedRule α β)) (x : α) (y : β)
    (h : select rules x = some y) :
    ∃ rule ∈ rules, rule.enabled x = true ∧ rule.target x = y := by
  induction rules with
  | nil => simp [select] at h
  | cons rule rest ih =>
    cases hg : rule.enabled x with
    | false =>
      simp only [select, hg, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨r,hr,he,ht⟩ := ih h
      exact ⟨r,by simp [hr],he,ht⟩
    | true =>
      simp only [select, hg, ↓reduceIte, Option.some.injEq] at h
      exact ⟨rule,by simp,hg,h⟩

theorem select_defined_iff (rules : List (GuardedRule α β)) (x : α) :
    (∃ y, select rules x = some y) ↔ ∃ rule ∈ rules, rule.enabled x = true := by
  constructor
  · rintro ⟨y,hy⟩
    obtain ⟨rule,hr,he,_⟩ := select_some_spec rules x y hy
    exact ⟨rule,hr,he⟩
  · intro h
    induction rules with
    | nil => simp at h
    | cons rule rest ih =>
      cases hg : rule.enabled x with
      | true => exact ⟨rule.target x,by simp [select,hg]⟩
      | false =>
        have ht : ∃ r ∈ rest, r.enabled x = true := by
          obtain ⟨r,hr,he⟩ := h
          simp only [List.mem_cons] at hr
          rcases hr with hr | hr
          · subst r; simp [hg] at he
          · exact ⟨r,hr,he⟩
        obtain ⟨y,hy⟩ := ih ht
        exact ⟨y,by simpa [select,hg] using hy⟩

theorem select_realizes {f : S → S} {source : α → S} {destination : β → S}
    (rules : List (GuardedRule α β))
    (sound : ∀ rule ∈ rules, Realizes f source destination rule)
    (x : α) (y : β) (selected : select rules x = some y) :
    Coalesces f (source x) (destination y) := by
  obtain ⟨rule,hr,he,ht⟩ := select_some_spec rules x y selected
  rw [← ht]
  exact sound rule hr x he

/-- Selecting a transport too early can discard the only downstream-applicable
alternative. Compose relational alternatives BEFORE fixing a selector. -/
def toyFirst : GuardedRule Nat Nat := ⟨fun x => x == 0,fun _ => 1⟩
def toySecond : GuardedRule Nat Nat := ⟨fun x => x == 0,fun _ => 2⟩
def toyTail : GuardedRule Nat Nat := ⟨fun x => x == 2,fun _ => 3⟩

theorem early_selection_loses_composite :
    (select [toyFirst,toySecond] 0).bind (fun y => select [toyTail] y) = none ∧
    select [compose toyFirst toyTail,compose toySecond toyTail] 0 = some 3 := by
  decide

def rankGap (sourceRank : α → Int) (destinationRank : β → Int)
    (rule : GuardedRule α β) (x : α) : Int :=
  sourceRank x - destinationRank (rule.target x)

/-- Exact endpoint accounting. Either summand may be negative. -/
theorem rankGap_compose (rα : α → Int) (rβ : β → Int) (rγ : γ → Int)
    (first : GuardedRule α β) (second : GuardedRule β γ) (x : α) :
    rankGap rα rγ (compose first second) x =
      rankGap rα rβ first x + rankGap rβ rγ second (first.target x) := by
  simp only [rankGap,compose]
  omega

theorem composite_decreases_of_positive_budget
    (rα : α → Nat) (rβ : β → Nat) (rγ : γ → Nat)
    (first : GuardedRule α β) (second : GuardedRule β γ) (x : α)
    (budget : 0 <
      rankGap (fun a => (rα a : Int)) (fun b => (rβ b : Int)) first x +
      rankGap (fun b => (rβ b : Int)) (fun c => (rγ c : Int)) second (first.target x)) :
    rγ ((compose first second).target x) < rα x := by
  simp only [rankGap,compose] at *
  omega

/-- Mathematical relation composition retains every alternative, unlike
selecting a single intermediate target before downstream guards are known. -/
def RelComp (R : α → β → Prop) (T : β → γ → Prop) : α → γ → Prop :=
  fun x z => ∃ y, R x y ∧ T y z

theorem relComp_union_right (R : α → β → Prop) (T U : β → γ → Prop) (x : α) (z : γ) :
    RelComp R (fun y z => T y z ∨ U y z) x z ↔
      RelComp R T x z ∨ RelComp R U x z := by
  constructor
  · rintro ⟨y,hR,hT | hU⟩
    · exact Or.inl ⟨y,hR,hT⟩
    · exact Or.inr ⟨y,hR,hU⟩
  · rintro (⟨y,hR,hT⟩ | ⟨y,hR,hU⟩)
    · exact ⟨y,hR,Or.inl hT⟩
    · exact ⟨y,hR,Or.inr hU⟩

inductive Chain (R : S → S → Prop) : S → S → Prop where
  | refl (x : S) : Chain R x x
  | cons {x y z : S} : R x y → Chain R y z → Chain R x z

theorem chain_coalesces {f : S → S} {R : S → S → Prop}
    (sound : ∀ x y, R x y → Coalesces f x y)
    {x y : S} (chain : Chain R x y) : Coalesces f x y := by
  induction chain with
  | refl x => exact coalesces_refl f x
  | cons edge rest ih => exact coalesces_trans (sound _ _ edge) ih

/-- Arbitrary local increases are allowed. What must be supplied for EVERY
source is a finite chain ending below its ORIGINAL natural-valued rank. -/
theorem capture_of_total_saturated_progress
    (f : S → S) (Captured : S → Prop) (rank : S → Nat) (R : S → S → Prop)
    (sound : ∀ x y, R x y → Coalesces f x y)
    (transfer : ∀ x y, Coalesces f x y → Captured y → Captured x)
    (total : ∀ x, Captured x ∨ ∃ y, Chain R x y ∧ rank y < rank x) :
    ∀ x, Captured x := by
  have all : ∀ n x, rank x = n → Captured x := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro x hx
      rcases total x with captured | reduced
      · exact captured
      · obtain ⟨y,chain,decrease⟩ := reduced
        apply transfer x y (chain_coalesces sound chain)
        exact ih (rank y) (by omega) y rfl
  intro x
  exact all (rank x) x rfl

/-- A finite overlapping rule bank is enough if its union is TOTAL outside
captured bases and every enabled rule has sound strict descent. -/
theorem capture_of_total_bank
    (f : S → S) (Captured : S → Prop) (rank : S → Nat)
    (rules : List (GuardedRule S S))
    (sound : ∀ rule ∈ rules, Realizes f id id rule)
    (decreases : ∀ rule ∈ rules, ∀ x, rule.enabled x = true → rank (rule.target x) < rank x)
    (transfer : ∀ x y, Coalesces f x y → Captured y → Captured x)
    (total : ∀ x, Captured x ∨ ∃ rule ∈ rules, rule.enabled x = true) :
    ∀ x, Captured x := by
  apply capture_of_total_saturated_progress f Captured rank
    (fun x y => ∃ rule ∈ rules, rule.enabled x = true ∧ rule.target x = y)
  · intro x y edge
    obtain ⟨rule,hr,he,hy⟩ := edge
    rw [← hy]
    exact sound rule hr x he
  · exact transfer
  · intro x
    rcases total x with captured | reduced
    · exact Or.inl captured
    · obtain ⟨rule,hr,he⟩ := reduced
      exact Or.inr ⟨rule.target x,Chain.cons ⟨rule,hr,he,rfl⟩ (Chain.refl _),
        decreases rule hr x he⟩

/-- Exponent-coordinate acceleration of the exact 243-to-128 cover pump.
Reconstruction of the integer m=2^a*3^b*q is separate; q is unchanged. -/
def CounterStep (x y : Nat × Nat) : Prop :=
  5 ≤ x.2 ∧ y.1 = x.1+7 ∧ y.2+5 = x.2

theorem counter_chain_iff (x y : Nat × Nat) :
    Chain CounterStep x y ↔ ∃ k, y.1 = x.1+7*k ∧ y.2+5*k = x.2 := by
  constructor
  · intro chain
    induction chain with
    | refl x => exact ⟨0,by omega,by omega⟩
    | cons edge rest ih =>
      obtain ⟨k,ha,hb⟩ := ih
      obtain ⟨hmin,hea,heb⟩ := edge
      exact ⟨k+1,by omega,by omega⟩
  · rintro ⟨k,ha,hb⟩
    induction k generalizing x y with
    | zero =>
      have eq : x = y := by
        apply Prod.ext
        · omega
        · omega
      rw [eq]
      exact Chain.refl y
    | succ k ih =>
      let middle : Nat × Nat := (x.1+7,x.2-5)
      have step : CounterStep x middle := by
        dsimp [CounterStep,middle]
        constructor
        · omega
        constructor <;> omega
      have tail : Chain CounterStep middle y := by
        apply ih
        · dsimp [middle]; omega
        · dsimp [middle]; omega
      exact Chain.cons step tail

end CollatzCoverAlgebra

#print axioms CollatzCoverAlgebra.coalesces_trans
#print axioms CollatzCoverAlgebra.realizes_compose
#print axioms CollatzCoverAlgebra.select_defined_iff
#print axioms CollatzCoverAlgebra.rankGap_compose
#print axioms CollatzCoverAlgebra.composite_decreases_of_positive_budget
#print axioms CollatzCoverAlgebra.capture_of_total_saturated_progress
#print axioms CollatzCoverAlgebra.capture_of_total_bank

#print axioms CollatzCoverAlgebra.meetsBy_trans
#print axioms CollatzCoverAlgebra.early_selection_loses_composite

#print axioms CollatzCoverAlgebra.counter_chain_iff
