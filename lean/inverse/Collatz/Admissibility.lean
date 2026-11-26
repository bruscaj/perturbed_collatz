import Collatz.Physical

namespace Collatz.Physical

abbrev Clock (w : Word) := Fin (w.periodPred+1)
def Binary {w : Word} (h : Clock w → Int) := ∀ i, h i = 0 ∨ h i = 1
def Gradient (w : Word) (h : Clock w → Int) := ∀ i, w.impulse i = h (i+1)-h i
def Floor (w : Word) (h : Clock w → Int) := ∀ i, h (i+1)-h i ≤ w.impulse i

theorem safe_tail {w : Word} {s : State w} (hs : Safe w s) : Safe w (step w s) :=
  fun k => hs (k+1)

theorem floor_invariant (w : Word) (h : Clock w → Int) (binary : Binary h)
    (floor : Floor w h) (s : State w) (hs : h s.1 ≤ s.2) :
    h (step w s).1 ≤ (step w s).2 := by
  change h (s.1+1) ≤ shortcut s.2+w.impulse s.1
  have base := binary s.1
  have edge := floor s.1
  unfold shortcut; split <;> omega

theorem admissible_of_floor (w : Word) (h : Clock w → Int) (binary : Binary h)
    (floor : Floor w h) : Admissible w := by
  have invariant (s : State w) (hs : h s.1 ≤ s.2) (k : Nat) :
      h (run (step w) k s).1 ≤ (run (step w) k s).2 := by
    induction k generalizing s with
    | zero => exact hs
    | succ k ih => exact ih _ (floor_invariant w h binary floor s hs)
  intro i n hn k
  have hi : h i ≤ n := by have := binary i; omega
  have := invariant (i,n) hi k
  have := binary (run (step w) k (i,n)).1
  omega

/-- Pointwise least safe height at each phase when every positive seed is safe. -/
noncomputable def leastSafe (w : Word) (i : Clock w) : Int := by
  classical
  exact if Safe w (i,0) then 0 else 1

theorem leastSafe_binary (w : Word) : Binary (leastSafe w) := by
  intro i; unfold leastSafe; split <;> simp

theorem leastSafe_le (w : Word) (s : State w) (hs : Safe w s) : leastSafe w s.1 ≤ s.2 := by
  have nonneg : 0 ≤ s.2 := hs 0
  unfold leastSafe; split
  · exact nonneg
  · rename_i unsafeZero
    have neq : s.2 ≠ 0 := by
      intro h
      apply unsafeZero
      have e : s = (s.1,0) := Prod.ext (by rfl) h
      simpa only [← e] using hs
    omega

theorem leastSafe_floor (w : Word) (ad : Admissible w) : Floor w (leastSafe w) := by
  intro i
  by_cases zero : Safe w (i,0)
  · have hi : leastSafe w i = 0 := by simp [leastSafe,zero]
    have hs := leastSafe_le _ _ (safe_tail zero)
    change leastSafe w (i+1) ≤ shortcut 0+w.impulse i at hs
    have t : shortcut 0 = 0 := by decide
    omega
  · have hi : leastSafe w i = 1 := by simp [leastSafe,zero]
    have hs := leastSafe_le _ _ (safe_tail (ad i 2 (by decide)))
    change leastSafe w (i+1) ≤ shortcut 2+w.impulse i at hs
    have t : shortcut 2 = 1 := by decide
    omega

theorem admissible_iff_floor (w : Word) :
    Admissible w ↔ ∃ h : Clock w → Int, Binary h ∧ Floor w h :=
  ⟨fun ad => ⟨leastSafe w,leastSafe_binary w,leastSafe_floor w ad⟩,
   fun ⟨h,b,f⟩ => admissible_of_floor w h b f⟩

private theorem sum_snoc (l : List Int) (x : Int) : (l++[x]).sum = l.sum+x := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih,Int.add_assoc]

private theorem sum_shift {n : Nat} (h : Fin (n+1) → Int) :
    (List.ofFn fun i => h (i+1)).sum = (List.ofFn h).sum := by
  have next (i : Fin n) : i.castSucc+1 = i.succ := by
    apply Fin.ext
    have lt : i.castSucc < Fin.last n := i.isLt
    rw [Fin.val_add_one_of_lt lt]; rfl
  conv => lhs; rw [List.ofFn_succ_last]
  conv => rhs; rw [List.ofFn_succ]
  simp [sum_snoc,next,Int.add_comm]

private theorem sum_sub {n : Nat} (f g : Fin n → Int) :
    (List.ofFn fun i => f i-g i).sum = (List.ofFn f).sum-(List.ofFn g).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.ofFn_succ,List.sum_cons]
    rw [ih (fun i => f i.succ) (fun i => g i.succ)]
    omega

private theorem sum_nonneg {n : Nat} (f : Fin n → Int) (hf : ∀ i, 0 ≤ f i) :
    0 ≤ (List.ofFn f).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.ofFn_succ,List.sum_cons]
    exact Int.add_nonneg (hf 0) (ih _ (fun i => hf i.succ))

private theorem zero_of_sum {n : Nat} (f : Fin n → Int) (hf : ∀ i, 0 ≤ f i)
    (tot : (List.ofFn f).sum = 0) (i : Fin n) : f i = 0 := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    rw [List.ofFn_succ,List.sum_cons] at tot
    have tail := sum_nonneg (fun j => f j.succ) (fun j => hf j.succ)
    have a := hf 0
    refine Fin.cases (by omega) (fun j => ?_) i
    apply ih (fun j => f j.succ) (fun j => hf j.succ) (by omega) j

theorem gradient_conservative (w : Word) (h : Clock w → Int) (g : Gradient w h) :
    Conservative w := by
  unfold Conservative
  rw [show w.impulse = (fun i => h (i+1)-h i) by funext i; exact g i,sum_sub,sum_shift]
  omega

theorem floor_gradient (w : Word) (c : Conservative w) (h : Clock w → Int) (f : Floor w h) :
    Gradient w h := by
  let d := fun i : Clock w => w.impulse i-(h (i+1)-h i)
  have nonneg (i : Clock w) : 0 ≤ d i := by have := f i; dsimp [d]; omega
  have tot : (List.ofFn d).sum = 0 := by
    dsimp [d]; rw [sum_sub,sum_sub,sum_shift]; change (List.ofFn w.impulse).sum = 0 at c
    omega
  intro i
  have := zero_of_sum d nonneg tot i
  dsimp [d] at this; omega

/-- Conservativity forces every inequality at the least safe height to be an equality. -/
theorem admissible_conservative_iff_binary_height (w : Word) :
    (Admissible w ∧ Conservative w) ↔ ∃ h : Clock w → Int, Binary h ∧ Gradient w h := by
  constructor
  · intro ⟨ad,c⟩
    exact ⟨leastSafe w,leastSafe_binary w,floor_gradient w c _ (leastSafe_floor w ad)⟩
  · intro ⟨h,b,g⟩
    exact ⟨admissible_of_floor w h b (fun i => Int.le_of_eq (g i).symm),
      gradient_conservative w h g⟩

def advancePhase {n : Nat} (i : Fin (n+1)) (k : Nat) : Fin (n+1) :=
  match k with
  | 0 => i
  | k+1 => advancePhase (i+1) k

def UnitAlphabet (w : Word) := ∀ i, w.impulse i = -1 ∨ w.impulse i = 0 ∨ w.impulse i = 1

/-- Consecutive nonzero impulses, including pairs crossing a period boundary, are opposites. -/
def Alternating (w : Word) : Prop :=
  ∀ i k, w.impulse i ≠ 0 → (∀ j < k, w.impulse (advancePhase (i+1) j) = 0) →
    w.impulse (advancePhase (i+1) k) ≠ 0 →
    w.impulse (advancePhase (i+1) k) = -w.impulse i

theorem gradient_unit_alphabet (w : Word) (h : Clock w → Int) (b : Binary h) (g : Gradient w h) :
    UnitAlphabet w := by
  intro i; have := b i; have := b (i+1); have := g i; omega

theorem height_across_zeros (w : Word) (h : Clock w → Int) (g : Gradient w h) (i : Clock w)
    (k : Nat) (zeros : ∀ j < k, w.impulse (advancePhase i j) = 0) : h (advancePhase i k) = h i := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih =>
    have z : w.impulse i = 0 := zeros 0 (by omega)
    have e := g i
    have hk := ih (i+1) (fun j hj => zeros (j+1) (by omega))
    change h (advancePhase (i+1) k) = h i
    omega

theorem gradient_alternates (w : Word) (h : Clock w → Int) (b : Binary h) (g : Gradient w h) :
    Alternating w := by
  intro i k start zeros finish
  have same := height_across_zeros w h g (i+1) k zeros
  have e := g i
  have f := g (advancePhase (i+1) k)
  have := b i; have := b (i+1); have := b (advancePhase (i+1) k+1)
  omega

private def nextNegative (w : Word) (i : Clock w) : Prop :=
  ∃ k, w.impulse (advancePhase i k) = -1 ∧ ∀ j < k, w.impulse (advancePhase i j) = 0

private theorem nextNegative_shift (w : Word) (i : Clock w) (zero : w.impulse i = 0) :
    nextNegative w i ↔ nextNegative w (i+1) := by
  constructor
  · intro ⟨k,last,zeros⟩
    cases k with
    | zero => change w.impulse i = -1 at last; omega
    | succ k => exact ⟨k,last,fun j hj => zeros (j+1) (by omega)⟩
  · intro ⟨k,last,zeros⟩
    refine ⟨k+1,last,?_⟩
    intro j hj
    cases j with
    | zero => exact zero
    | succ j => exact zeros j (by omega)

theorem alternating_admissible (w : Word) (unit : UnitAlphabet w) (alt : Alternating w) :
    Admissible w := by
  classical
  let h (i : Clock w) : Int := if nextNegative w i then 1 else 0
  have b : Binary h := by intro i; dsimp [h]; split <;> simp
  apply admissible_of_floor w h b
  intro i
  rcases unit i with neg | z | pos
  · have now : nextNegative w i := ⟨0,neg,by intro j hj; omega⟩
    have after : ¬nextNegative w (i+1) := by
      intro ⟨k,last,zeros⟩
      have cmp := alt i k (by omega) zeros (by omega)
      omega
    simp [h,now,after,neg]
  · have eq := nextNegative_shift w i z
    simp [h,eq,z]
  · have := b i; have := b (i+1); omega

theorem conservative_admissible_iff_alternating (w : Word) (c : Conservative w) :
    Admissible w ↔ UnitAlphabet w ∧ Alternating w := by
  constructor
  · intro a
    obtain ⟨h,b,g⟩ := (admissible_conservative_iff_binary_height w).mp ⟨a,c⟩
    exact ⟨gradient_unit_alphabet w h b g,gradient_alternates w h b g⟩
  · exact fun ⟨u,a⟩ => alternating_admissible w u a

/-- The positive coordinate of a safe state. The conjugacy identity also holds on signed inputs. -/
def coordinate {w : Word} (h : Clock w → Int) (s : State w) := s.2+1-h s.1

theorem coordinate_conjugacy (w : Word) (h : Clock w → Int) (b : Binary h) (g : Gradient w h)
    (s : State w) :
    coordinate h (step w s) =
      if h s.1 = 1 then shortcut (coordinate h s) else shortcut (coordinate h s-1)+1 := by
  change shortcut s.2+w.impulse s.1+1-h (s.1+1) = _
  rw [g]
  rcases b s.1 with hi | hi <;> simp [coordinate,hi] <;> omega

theorem safe_iff_above_least (w : Word) (a : Admissible w) (s : State w) :
    Safe w s ↔ leastSafe w s.1 ≤ s.2 := by
  constructor
  · exact leastSafe_le w s
  · intro below
    have hs : 0 ≤ s.2 := by have := leastSafe_binary w s.1; omega
    by_cases zero : s.2 = 0
    · have safeZero : Safe w (s.1,0) := by
        by_cases h : Safe w (s.1,0)
        · exact h
        have one : leastSafe w s.1 = 1 := by simp [leastSafe,h]
        omega
      have e : s = (s.1,0) := Prod.ext rfl zero
      rw [e]; exact safeZero
    · exact a s.1 s.2 (by omega)

private theorem constant_along_clock {n : Nat} (d : Fin (n+1) → Int)
    (same : ∀ i, d (i+1) = d i) (i : Fin (n+1)) : d i = d 0 := by
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih =>
    have next : i.castSucc+1 = i.succ := by
      apply Fin.ext
      have lt : i.castSucc < Fin.last n := i.isLt
      rw [Fin.val_add_one_of_lt lt]; rfl
    rw [← next, same]; exact ih

theorem height_unique (w : Word) (nonzero : ∃ i, w.impulse i ≠ 0)
    (h g : Clock w → Int) (hb : Binary h) (gb : Binary g)
    (hg : Gradient w h) (gg : Gradient w g) : h = g := by
  let diff (i : Clock w) := h i-g i
  have same (i : Clock w) : diff (i+1) = diff i := by
    have := hg i; have := gg i; dsimp [diff]; omega
  obtain ⟨j,move⟩ := nonzero
  have hj : diff j = 0 := by
    have := hb j; have := gb j; have := hb (j+1); have := gb (j+1)
    have := hg j; have := gg j; dsimp [diff]; omega
  funext i
  have p := constant_along_clock diff same j
  have q := constant_along_clock diff same i
  dsimp [diff] at hj p q; omega

theorem safe_iff_height (w : Word) (nonzero : ∃ i, w.impulse i ≠ 0) (h : Clock w → Int)
    (hb : Binary h) (hg : Gradient w h) (s : State w) : Safe w s ↔ h s.1 ≤ s.2 := by
  obtain ⟨ad,c⟩ := (admissible_conservative_iff_binary_height w).2 ⟨h,hb,hg⟩
  have eq := height_unique w nonzero _ h (leastSafe_binary w) hb
    (floor_gradient w c _ (leastSafe_floor w ad)) hg
  rw [← eq]; exact safe_iff_above_least w ad s

def zStep (w : Word) (h : Clock w → Int) (s : State w) : State w :=
  (s.1+1,if h s.1 = 1 then shortcut s.2 else shortcut (s.2-1)+1)

def toCoordinate {w : Word} (h : Clock w → Int) (s : State w) : State w := (s.1,coordinate h s)

theorem coordinate_orbit (w : Word) (h : Clock w → Int) (b : Binary h) (g : Gradient w h)
    (s : State w) (k : Nat) :
    toCoordinate h (run (step w) k s) = run (zStep w h) k (toCoordinate h s) := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    change toCoordinate h (run (step w) k (step w s)) = run _ k (zStep w h (toCoordinate h s))
    rw [ih]
    exact congrArg (run _ k) (Prod.ext rfl (coordinate_conjugacy w h b g s))

theorem coordinate_injective (w : Word) (h : Clock w → Int) (s t : State w)
    (eq : toCoordinate h s = toCoordinate h t) : s = t := by
  have phase := congrArg Prod.fst eq
  change s.1 = t.1 at phase
  have value := congrArg Prod.snd eq
  change s.2+1-h s.1 = t.2+1-h t.1 at value
  rw [phase] at value
  exact Prod.ext phase (by omega)

theorem cycle_correspondence (w : Word) (h : Clock w → Int) (b : Binary h) (g : Gradient w h)
    (s : State w) (k : Nat) : run (step w) k s = s ↔ run (zStep w h) k (toCoordinate h s) = toCoordinate h s := by
  rw [← coordinate_orbit w h b g]
  exact ⟨congrArg _, coordinate_injective w h _ _⟩

/-- Word rotation changes only the base phase of the forcing sequence. -/
def rotate (w : Word) (r : Clock w) : Word :=
  ⟨w.periodPred, fun i => w.impulse (i+r)⟩

def originalState (w : Word) (r : Clock w) (s : State (rotate w r)) : State w :=
  let i : Clock w := s.1
  (i+r,s.2)

theorem rotation_step (w : Word) (r : Clock w) (s : State (rotate w r)) :
    originalState w r (step _ s) = step w (originalState w r s) := by
  refine Prod.ext ?_ rfl
  let i : Clock w := s.1
  change (i+1)+r = (i+r)+1
  apply Fin.ext
  simp only [Fin.val_add,Nat.mod_add_mod]
  congr 1; omega

theorem rotation_orbit (w : Word) (r : Clock w) (s : State (rotate w r)) (k : Nat) :
    originalState w r (run (step _) k s) = run (step w) k (originalState w r s) := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    change originalState w r (run _ k (step _ s)) = run _ k (step _ (originalState w r s))
    rw [ih,rotation_step]

theorem rotation_onto (w : Word) (r i : Clock w) : ∃ j : Clock w, j+r = i := by
  let p := w.periodPred+1
  refine ⟨Fin.ofNat p (i.val+p-r.val),?_⟩
  apply Fin.ext
  change (((i.val+p-r.val)%p+r.val)%p) = i.val
  rw [Nat.mod_add_mod]
  have hr : r.val < p := r.isLt
  have eq : i.val+p-r.val+r.val = i.val+p := by omega
  rw [eq]
  exact (Nat.add_mod_right _ _).trans (Nat.mod_eq_of_lt i.isLt)

theorem rotation_admissible (w : Word) (r : Clock w) :
    Admissible (rotate w r) ↔ Admissible w := by
  constructor
  · intro a i n hn k
    obtain ⟨j,hj⟩ := rotation_onto w r i
    have h := a j n hn k
    have e := congrArg Prod.snd (rotation_orbit w r (j,n) k)
    change (run (step (rotate w r)) k (j,n)).2 = (run (step w) k (j+r,n)).2 at e
    rw [hj] at e
    rw [← e]; exact h
  · intro a i n hn k
    have e := congrArg Prod.snd (rotation_orbit w r (i,n) k)
    let j : Clock w := i
    change (run (step (rotate w r)) k (i,n)).2 = (run (step w) k (j+r,n)).2 at e
    rw [e]; exact a (j+r) n hn k

def parityFactor (n : Int) : Int := if n%2 = 0 then 1 else 3

theorem shortcut_lift (n t : Int) :
    shortcut (n+2*t) = shortcut n+parityFactor n*t := by
  unfold shortcut parityFactor
  split <;> split <;> simp_all <;> omega

/-- In the signed continued model every dyadic lift has exactly the same phase and an odd,
    positive affine multiplier. The assertion includes negative states and all crossings of zero. -/
theorem signed_parity_lift (w : Word) (i : Clock w) (n : Int) (k : Nat) :
    ∃ c : Int, 0 < c ∧ c%2 = 1 ∧ ∀ q : Int,
      run (step w) k (i,n+2^k*q) =
      ((run (step w) k (i,n)).1, (run (step w) k (i,n)).2+c*q) := by
  induction k generalizing i n with
  | zero => exact ⟨1,by decide,by decide,fun q => by simp [run]⟩
  | succ k ih =>
    obtain ⟨c,hpos,hodd,replay⟩ := ih (i+1) (shortcut n+w.impulse i)
    refine ⟨c*parityFactor n,?_,?_,?_⟩
    · unfold parityFactor; split <;> omega
    · unfold parityFactor; split <;> omega
    · intro q
      let t := 2^k*q
      have shift : n+2^(k+1)*q = n+2*t := by
        dsimp [t]; rw [Int.pow_succ,Int.mul_comm _ 2,Int.mul_assoc]
      have move : step w (i,n+2^(k+1)*q) =
          (i+1, shortcut n+w.impulse i + 2^k*(parityFactor n*q)) := by
        refine Prod.ext rfl ?_
        change shortcut (n+2^(k+1)*q)+w.impulse i = _
        rw [shift,shortcut_lift]
        dsimp [t]; rw [Int.mul_left_comm (parityFactor n)]; omega
      change run (step w) k (step w (i,n+2^(k+1)*q)) =
        ((run (step w) k (step w (i,n))).1, (run (step w) k (step w (i,n))).2+_)
      rw [move,replay]
      simp only [Int.mul_assoc]; rfl

end Collatz.Physical
