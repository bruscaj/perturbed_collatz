import Collatz.Branches

/-!
# Binary inverse trees for the word (+1, 0, −1)

A bit selects one concrete six-update inverse from `Collatz.Branches`.
Words are stored with their newest choice at the head. Removing the head
therefore corresponds to advancing the forcing word through two laps.
-/

namespace Collatz.Tree

def child : Bool → Nat → Nat
  | false => A
  | true  => B

private theorem child_good (b : Bool) {y : Nat} (hy : Good y) :
    Good (child b y) := by
  cases b
  · exact A_good hy
  · exact B_good hy

private theorem child_parent (b : Bool) {y : Nat} (hy : Good y) :
    twoLaps (child b y) = y := by
  cases b
  · exact A_parent y
  · exact B_parent hy

private theorem child_grow (b : Bool) {y : Nat} (hy : Good y) :
    y < child b y := by
  cases b
  · exact A_grow y
  · exact B_grow hy

private theorem same_child_bit {b c : Bool} {y : Nat} (hy : Good y)
    (h : child b y = child c y) : b = c := by
  have hlt := B_lt_A hy
  cases b <;> cases c <;> simp [child] at * <;> omega

/-- Seed selected by a word of inverse choices, starting from the given root. -/
def endpoint (root : Nat) : List Bool → Nat
  | [] => root
  | b :: tail => child b (endpoint root tail)

theorem endpoint_good {root : Nat} (hr : Good root) (w : List Bool) :
    Good (endpoint root w) := by
  induction w with
  | nil => exact hr
  | cons b _ ih => exact child_good b ih

private theorem root_le_endpoint {root : Nat} (hr : Good root) (w : List Bool) :
    root ≤ endpoint root w := by
  induction w with
  | nil => exact Nat.le_refl root
  | cons b w ih =>
    have h := child_grow b (endpoint_good hr w)
    change root ≤ child b (endpoint root w)
    omega

private theorem nonempty_strict {root : Nat} (hr : Good root) (b : Bool) (w : List Bool) :
    root < endpoint root (b :: w) := by
  have h₁ := root_le_endpoint hr w
  have h₂ := child_grow b (endpoint_good hr w)
  change root < child b (endpoint root w)
  omega

/-- Distinct inverse words from the same root give distinct integers, even at different depths. -/
theorem endpoint_injective {root : Nat} (hr : Good root) (v w : List Bool)
    (h : endpoint root v = endpoint root w) : v = w := by
  induction v generalizing w with
  | nil =>
    cases w with
    | nil => rfl
    | cons b w =>
      have hstrict := nonempty_strict hr b w
      change root = endpoint root (b :: w) at h
      omega
  | cons a v ih =>
    cases w with
    | nil =>
      have hstrict := nonempty_strict hr a v
      change endpoint root (a :: v) = root at h
      omega
    | cons b w =>
      change child a (endpoint root v) = child b (endpoint root w) at h
      have hp := congrArg twoLaps h
      rw [child_parent a (endpoint_good hr v), child_parent b (endpoint_good hr w)] at hp
      have ht := ih w hp
      subst w
      have hb := same_child_bit (endpoint_good hr v) h
      subst b
      rfl

/-- Each block advances six scalar updates (two laps of the three-element word). -/
def advanceBlocks : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => advanceBlocks k (twoLaps n)

/-- Return after the specified number of six-update blocks. No minimal return time is assumed. -/
theorem endpoint_returns {root : Nat} (hr : Good root) (w : List Bool) :
    advanceBlocks w.length (endpoint root w) = root := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    change advanceBlocks w.length (twoLaps (child b (endpoint root w))) = root
    rw [child_parent b (endpoint_good hr w)]
    exact ih

private theorem child_bound (b : Bool) {y : Nat} (hy : Good y) :
    child b y + 1 ≤ 64 * (y + 1) := by
  cases b with
  | false => exact A_bound y
  | true =>
    have h := B_bound hy
    change B y + 1 ≤ 64 * (y + 1)
    omega

theorem endpoint_bound {root : Nat} (hr : Good root) (w : List Bool) :
    endpoint root w + 1 ≤ 64 ^ w.length * (root + 1) := by
  induction w with
  | nil => simp [endpoint]
  | cons b w ih =>
    have hb := child_bound b (endpoint_good hr w)
    have hm := Nat.mul_le_mul_left 64 ih
    calc
      endpoint root (b :: w) + 1 ≤ 64 * (endpoint root w + 1) := hb
      _ ≤ 64 * (64 ^ w.length * (root + 1)) := hm
      _ = 64 ^ (b :: w).length * (root + 1) := by
        simp only [List.length_cons, Nat.pow_succ]
        ac_rfl

/-- Number of choices of the smaller B branch along a path. -/
def countB : List Bool → Nat
  | [] => 0
  | false :: w => countB w
  | true :: w => countB w + 1

private theorem scaled_child_bound (b : Bool) {y : Nat} (hy : Good y) :
    (if b then 3 else 1) * (child b y + 1) ≤ 64 * (y + 1) := by
  cases b with
  | false => simpa [child] using A_bound y
  | true => exact B_bound hy

/-- Integer form of the path budget: an A edge costs at most 64, a B edge at most 64/3. -/
theorem endpoint_weighted_bound {root : Nat} (hr : Good root) (w : List Bool) :
    3 ^ countB w * (endpoint root w + 1) ≤ 64 ^ w.length * (root + 1) := by
  induction w with
  | nil => simp [countB, endpoint]
  | cons b w ih =>
    have hf : 3 ^ countB (b :: w) = 3 ^ countB w * (if b then 3 else 1) := by
      cases b <;> simp [countB, Nat.pow_succ]
    calc
      _ = 3 ^ countB w * ((if b then 3 else 1) * (child b (endpoint root w) + 1)) := by
        rw [hf]
        simp [endpoint, Nat.mul_assoc]
      _ ≤ 3 ^ countB w * (64 * (endpoint root w + 1)) :=
        Nat.mul_le_mul_left _ (scaled_child_bound b (endpoint_good hr w))
      _ = 64 * (3 ^ countB w * (endpoint root w + 1)) := by ac_rfl
      _ ≤ 64 * (64 ^ w.length * (root + 1)) := Nat.mul_le_mul_left _ ih
      _ = 64 ^ (b :: w).length * (root + 1) := by
        simp only [List.length_cons, Nat.pow_succ]
        ac_rfl

/-- A canonical lower-bit-first encoding of the integers in [0, 2^k). -/
def bits : (k : Nat) → Fin (2 ^ k) → List Bool
  | 0, _ => []
  | k + 1, i =>
    decide (i.val % 2 = 1) :: bits k ⟨i.val / 2, by
      have hi : i.val < 2 ^ k * 2 := calc
        i.val < 2 ^ (k + 1) := i.isLt
        _ = 2 ^ k * 2 := Nat.pow_succ _ _
      omega⟩

theorem bits_length (k : Nat) (i : Fin (2 ^ k)) : (bits k i).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [bits, ih]

private theorem bits_injective (k : Nat) (i j : Fin (2 ^ k))
    (h : bits k i = bits k j) : i = j := by
  induction k with
  | zero =>
    apply Fin.ext
    have hi := i.isLt
    have hj := j.isLt
    change i.val < 1 at hi
    change j.val < 1 at hj
    omega
  | succ k ih =>
    simp only [bits, List.cons.injEq] at h
    obtain ⟨hb, ht⟩ := h
    have hq := congrArg Fin.val (ih _ _ ht)
    change i.val / 2 = j.val / 2 at hq
    apply Fin.ext
    by_cases hi : i.val % 2 = 1 <;> by_cases hj : j.val % 2 = 1 <;>
      simp [hi, hj] at hb <;> omega

/-- At least 2^k distinct good seeds below 64^k*(root+1) return in k blocks.
The lower bound is expressed by a concrete injection indexed by Fin (2^k). -/
theorem fixed_depth_lower_bound {root : Nat} (hr : Good root) (k : Nat) :
    ∃ seed : Fin (2 ^ k) → Nat,
      (∀ i j, seed i = seed j → i = j) ∧
      ∀ i, Good (seed i) ∧ seed i < 64 ^ k * (root + 1) ∧
        advanceBlocks k (seed i) = root := by
  refine ⟨fun i => endpoint root (bits k i), ?_, ?_⟩
  · intro i j h
    exact bits_injective k i j (endpoint_injective hr _ _ h)
  · intro i
    have hb := endpoint_bound hr (bits k i)
    have ht := endpoint_returns hr (bits k i)
    rw [bits_length] at hb ht
    exact ⟨endpoint_good hr _, Nat.lt_of_succ_le hb, ht⟩

end Collatz.Tree
