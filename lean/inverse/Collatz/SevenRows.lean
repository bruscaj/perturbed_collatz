import Collatz.SevenFrontier

namespace Collatz.SevenStep
open Physical

set_option maxRecDepth 10000
set_option maxHeartbeats 16000000

/-- The source has m = 2^ticks*q + base, the target m = slope*q + offset, for q ≥ 0.
    Positive representatives make the first multiple of the modulus the zero residue's base. -/
structure Row where
  source : Phase
  ticks : Nat
  base : Nat
  target : Phase
  slope : Nat
  offset : Nat
  deriving DecidableEq, Repr

def rows : List Row := [
  ⟨1, 2, 1, 3, 3, 1⟩,
  ⟨1, 1, 2, 2, 3, 3⟩,
  ⟨1, 2, 3, 3, 1, 1⟩,
  ⟨2, 6, 1, 1, 9, 1⟩,
  ⟨2, 1, 2, 3, 3, 3⟩,
  ⟨2, 3, 3, 5, 9, 4⟩,
  ⟨2, 3, 5, 5, 3, 2⟩,
  ⟨2, 3, 7, 5, 3, 3⟩,
  ⟨2, 7, 9, 2, 9, 1⟩,
  ⟨2, 6, 17, 1, 3, 1⟩,
  ⟨2, 6, 25, 1, 9, 4⟩,
  ⟨2, 6, 33, 1, 3, 2⟩,
  ⟨2, 6, 41, 1, 9, 6⟩,
  ⟨2, 6, 49, 1, 1, 1⟩,
  ⟨2, 6, 57, 1, 27, 25⟩,
  ⟨2, 7, 73, 2, 3, 2⟩,
  ⟨3, 2, 1, 5, 3, 1⟩,
  ⟨3, 5, 2, 1, 9, 1⟩,
  ⟨3, 2, 3, 5, 9, 7⟩,
  ⟨3, 2, 4, 5, 3, 3⟩,
  ⟨3, 5, 6, 1, 3, 1⟩,
  ⟨3, 5, 10, 1, 9, 3⟩,
  ⟨3, 6, 14, 2, 3, 1⟩,
  ⟨3, 5, 18, 1, 27, 16⟩,
  ⟨3, 5, 22, 1, 9, 7⟩,
  ⟨3, 6, 26, 2, 9, 4⟩,
  ⟨3, 5, 30, 1, 3, 3⟩,
  ⟨3, 6, 46, 2, 1, 1⟩,
  ⟨3, 6, 58, 2, 3, 3⟩,
  ⟨5, 7, 1, 5, 9, 1⟩,
  ⟨5, 3, 2, 1, 27, 7⟩,
  ⟨5, 3, 3, 1, 9, 4⟩,
  ⟨5, 4, 4, 2, 3, 1⟩,
  ⟨5, 3, 5, 1, 3, 2⟩,
  ⟨5, 3, 6, 1, 9, 7⟩,
  ⟨5, 3, 7, 1, 3, 3⟩,
  ⟨5, 3, 8, 1, 9, 9⟩,
  ⟨5, 4, 9, 2, 3, 2⟩,
  ⟨5, 4, 12, 2, 9, 7⟩,
  ⟨5, 5, 17, 3, 3, 2⟩,
  ⟨5, 7, 33, 5, 3, 1⟩,
  ⟨5, 7, 65, 5, 3, 2⟩,
  ⟨5, 7, 97, 5, 1, 1⟩]

def Row.start (r : Row) : Affine := ⟨3*(2^r.ticks : Nat),3*(r.base:Int)-1+height r.source⟩
def Row.accept (r : Row) (i : Phase) (x : Affine) : Bool :=
  i == r.target && x.a == 3*(r.slope:Int) && x.b == 3*(r.offset:Int)-1+height i

def clockAt (i : Phase) (n : Nat) : Phase :=
  match n with
  | 0 => i
  | k+1 => clockAt (i+1) k

def Row.check (r : Row) : Bool :=
  0 < r.ticks && r.ticks ≤ cap r.source && cap r.source ≤ 7 &&
  0 < r.base && r.base ≤ 2^r.ticks && decide (2^r.ticks ∣ 128) &&
  r.start.a % 2 == 0 &&
  decide (∀ k : Fin 7, k.val < r.ticks → clockAt (r.source+1) k.val = r.target →
    k.val+1 = r.ticks) &&
  checkHit r.accept (r.ticks-1) (r.source+1) (r.start.advance r.source)

/-- Each of the 43 listed cylinders passes the signed check. -/
theorem checked_rows : rows.length = 43 ∧ rows.all Row.check = true := by decide +kernel

theorem orbit_phase (k : Nat) (s : State) : (orbit k s).1 = clockAt s.1 k := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih => exact ih (tick s)

theorem Row.sound (r : Row) (ok : r.check) (q : Nat) :
    let start := site r.source (2^r.ticks*q+r.base)
    orbit r.ticks start = site r.target (r.slope*q+r.offset) ∧
    Marked (orbit r.ticks start) ∧ ∀ d, 0 < d → d < r.ticks → ¬Marked (orbit d start) := by
  dsimp only
  simp only [Row.check, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hpos,hcap⟩,cap7⟩,_⟩,_⟩,_⟩,even⟩,clock⟩,trace⟩ := ok
  let start := site r.source (2^r.ticks*q+r.base)
  let finish := site r.target (r.slope*q+r.offset)
  have hs : (r.source,r.start.val q) = start := by
    refine Prod.ext rfl ?_
    simp only [start,site,Row.start,Affine.val,Int.natCast_add,Int.natCast_mul,Int.mul_add,
      Int.mul_assoc]
    omega
  have ht := advance_sound r.source r.start q even
  rw [hs] at ht
  have goal (j : Phase) (x : Affine) (accept : r.accept j x) : (j,x.val q) = finish := by
    simp only [Row.accept,Bool.and_eq_true,beq_iff_eq] at accept
    obtain ⟨⟨hj,ha⟩,hb⟩ := accept
    refine Prod.ext hj ?_
    simp only [Affine.val,ha,hb,finish,site,Int.natCast_add,Int.natCast_mul,Int.mul_add,
      Int.mul_assoc,hj]
    omega
  obtain ⟨k,hk,marked,arrived,first⟩ := checkHit_sound r.accept q (· = finish) goal _ _ _ trace
  rw [← ht] at marked arrived first
  have htgt := congrArg Prod.fst arrived
  rw [orbit_phase] at htgt
  change clockAt (r.source+1) k = r.target at htgt
  have below : k < r.ticks := by omega
  have heq := clock ⟨k,by omega⟩ below htgt
  change k+1 = r.ticks at heq
  change orbit r.ticks start = finish ∧ Marked (orbit r.ticks start) ∧
    ∀ d, 0 < d → d < r.ticks → ¬Marked (orbit d start)
  rw [← heq]
  refine ⟨arrived,marked,?_⟩
  intro d hd hu
  cases d with
  | zero => omega
  | succ d => exact first d (by omega)

def Row.applies (i : Phase) (m : Nat) (r : Row) : Bool :=
  r.source == i && (m-1) % (2^r.ticks)+1 == r.base

private theorem unique_rows : ∀ (i : Phase) (r : Fin 128),
    active i → (rows.filter (Row.applies i (r.val+1))).length = 1 := by decide +kernel

theorem partition (i : Phase) (m : Nat) (ha : active i) :
    (rows.filter (Row.applies i m)).length = 1 := by
  let k : Fin 128 := ⟨(m-1)%128,Nat.mod_lt _ (by decide)⟩
  have he : rows.filter (Row.applies i m) = rows.filter (Row.applies i (k.val+1)) := by
    apply List.filter_congr
    intro r hr
    have checked := List.all_eq_true.mp checked_rows.2 r hr
    simp only [Row.check, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at checked
    have div : 2^r.ticks ∣ 128 := checked.1.1.1.2
    simp [Row.applies,k,Nat.mod_mod_of_dvd _ div]
  rw [he]
  exact unique_rows i k ha

/-- The selected residue admits the row's unrestricted nonnegative parameter. -/
theorem parameter_of_applies (r : Row) (i : Phase) (m : Nat)
    (hm : 0 < m) (applies : r.applies i m) :
    r.source = i ∧ ∃ q : Nat, m = 2^r.ticks*q+r.base := by
  simp only [Row.applies,Bool.and_eq_true,beq_iff_eq] at applies
  refine ⟨applies.1, (m-1)/(2^r.ticks), ?_⟩
  have := Nat.mod_add_div (m-1) (2^r.ticks)
  omega

def Row.gain (r : Row) := weight r.target*(r.slope:Int)-weight r.source*(2^r.ticks : Nat)
def Row.intercept (r : Row) := weight r.target*(r.offset:Int)-weight r.source*(r.base:Int)
def Row.change (r : Row) (q : Nat) := r.gain*(q:Int)+r.intercept

def boundary (i : Phase) (m : Nat) : Bool :=
  (i == 1 && m == 1) || (i == 3 && (m == 1 || m == 5)) ||
  (i == 5 && (m == 1 || m == 3))

/-- The positive source representative on the even B1 cylinder is m=2. -/
theorem increasing_rows : rows.filter (fun r => decide (0 < r.gain)) =
    [⟨1,1,2,2,3,3⟩,⟨3,2,3,5,9,7⟩,⟨5,3,2,1,27,7⟩] := by decide +kernel

def Row.classified (r : Row) : Bool :=
  if r.gain > 0 then 0 < r.intercept else
    r.gain ≤ 0 && 2*r.gain+r.intercept < 0 && 5 < 2*(2^r.ticks)+r.base &&
    decide (∀ q : Fin 2, (0 ≤ r.change q.val) ↔
      boundary r.source (2^r.ticks*q.val+r.base) = true)

private theorem rank_rows : rows.all Row.classified := by decide +kernel

theorem rank_classification (r : Row) (hr : r ∈ rows) (q : Nat) :
    (r.gain > 0 → 0 < r.change q) ∧
    (r.gain ≤ 0 → (0 ≤ r.change q ↔ boundary r.source (2^r.ticks*q+r.base) = true)) := by
  have ok := List.all_eq_true.mp rank_rows r hr
  by_cases h : r.gain > 0
  · simp [Row.classified,h] at ok
    constructor
    · intro _
      have := Int.mul_nonneg (Int.le_of_lt h) (Int.natCast_nonneg q)
      unfold Row.change; omega
    · omega
  · simp only [Row.classified,if_neg h,Bool.and_eq_true,decide_eq_true_eq] at ok
    constructor
    · omega
    · intro _
      by_cases small : q < 2
      · exact ok.2 ⟨q,small⟩
      · have leq : (2:Int) ≤ (q:Int) := by omega
        have slope := Int.mul_le_mul_of_nonpos_left ok.1.1.1 leq
        have large := Nat.mul_le_mul_left (2^r.ticks) (show 2 ≤ q by omega)
        have size : 5 < 2^r.ticks*q+r.base := by
          rw [Nat.mul_comm 2] at ok
          omega
        have eqfalse : boundary r.source (2^r.ticks*q+r.base) = false := by
          unfold boundary
          have h1 : 2^r.ticks*q+r.base ≠ 1 := by omega
          have h3 : 2^r.ticks*q+r.base ≠ 3 := by omega
          have h5 : 2^r.ticks*q+r.base ≠ 5 := by omega
          simp [h1,h3,h5]
        simp only [eqfalse, Bool.false_eq_true, iff_false]
        unfold Row.change; omega

/-- The affine comparison equals one third of the difference of signed physical ranks. -/
theorem rank_change (r : Row) (q : Nat) :
    signedRank (site r.target (r.slope*q+r.offset)) -
    signedRank (site r.source (2^r.ticks*q+r.base)) = 3*r.change q := by
  have atSite (i : Phase) (m : Nat) : z i (site i m).2 = 3*(m:Int) := by
    simp [z,site]; omega
  change weight r.target * z r.target (site r.target _).2 -
    weight r.source * z r.source (site r.source _).2 = _
  rw [atSite,atSite]
  simp only [Row.change,Row.gain,Row.intercept,Int.natCast_add,Int.natCast_mul,
    Int.mul_add,Int.mul_sub,Int.sub_mul,← Int.mul_assoc]
  simp only [Int.mul_comm _ 3]
  omega

theorem finite_captures (i : Phase) (m : Nat) (hb : boundary i m = true) :
    Captured (site i m) := by
  simp only [boundary,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq] at hb
  have replay : smallHit (site i m) 20 = true := by
    rcases hb with ((⟨rfl,rfl⟩ | ⟨rfl,(rfl|rfl)⟩) | ⟨rfl,(rfl|rfl)⟩) <;> decide
  exact smallHit_sound _ _ replay

/-- The physical orbit starting at phase 3 and value 14 attains the six-tick bound. -/
theorem sharp_entry : Marked (orbit 6 (3,14)) ∧
    ∀ t : Fin 6, ¬Marked (orbit t.val (3,14)) := by
  unfold Marked; decide +kernel

end Collatz.SevenStep
