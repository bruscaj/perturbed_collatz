import GeneralArithmetic
import GeneralStrideWords
import Mathlib.Algebra.BigOperators.Fin

/-! Exact block-to-word compilation for the frozen refined arithmetic cells. -/
namespace ExternalO3GeneralBlockWords
open ExternalO3GeneralDraft ExternalO3GeneralArithmetic ExternalO3GeneralStrideWords
open ExternalO3Spec (IsOddSeed stride strideValuation blockLength nextBlock)
open ExternalO3Arithmetic
open scoped BigOperators

/-- Unroll exactly j valuation-one strides, retaining the literal endpoint. -/
theorem prefix_ones_cell (j r : ℕ) (tail : List ℕ) (x : ℕ) :
    StrideWordCell r (List.replicate j 1 ++ tail) x ↔
      (∀ t : ℕ, t < j → strideValuation ((Nat.iterate stride t) x) = 1) ∧
      StrideWordCell r tail ((Nat.iterate stride j) x) := by
  induction j generalizing x with
  | zero => simp
  | succ j ih =>
    simp only [List.replicate_succ, List.cons_append, StrideWordCell]
    rw [ih]
    constructor
    · rintro ⟨h0, hones, hc⟩
      refine ⟨?_, ?_⟩
      · intro t ht
        cases t with
        | zero => simpa using h0
        | succ t =>
          simpa only [Function.iterate_succ_apply] using hones t (by omega)
      · simpa only [Function.iterate_succ_apply] using hc
    · rintro ⟨hones, hc⟩
      refine ⟨by simpa using hones 0 (by omega), ?_, ?_⟩
      · intro t ht
        simpa only [Function.iterate_succ_apply] using hones (t + 1) (by omega)
      · simpa only [Function.iterate_succ_apply] using hc

/-- A first non-one valuation identifies the actual remaining block length. -/
theorem blockLength_of_first_exit (x j : ℕ) (hx : IsOddSeed x)
    (hones : ∀ t : ℕ, t < j → strideValuation ((Nat.iterate stride t) x) = 1)
    (hexit : 2 ≤ strideValuation ((Nat.iterate stride j) x)) :
    blockLength x = j + 1 := by
  obtain ⟨hpos, hprefix, hlast⟩ := block_length_law x hx
  apply Nat.le_antisymm
  · by_contra hn
    have h1 := hprefix j (by omega)
    omega
  · by_contra hn
    have h1 := hones (blockLength x - 1) (by omega)
    omega

theorem exit_stride_eq_nextBlock (x ℓ : ℕ) (hℓ : 1 ≤ ℓ) (hr : blockLength x = ℓ) :
    stride ((Nat.iterate stride (ℓ - 1)) x) = nextBlock x := by
  unfold nextBlock
  rw [hr]
  simpa only [Nat.succ_eq_add_one, Nat.sub_add_cancel hℓ] using
    (Function.iterate_succ_apply' stride (ℓ - 1) x).symm

/-- A complete prescribed block is exactly its actual block length and exit. -/
theorem block_word_cell (r ℓ κ : ℕ) (tail : List ℕ) (x : ℕ)
    (hx : IsOddSeed x) (hℓ : 1 ≤ ℓ) (hκ : 2 ≤ κ) :
    StrideWordCell r (List.replicate (ℓ - 1) 1 ++ κ :: tail) x ↔
      blockLength x = ℓ ∧
      strideValuation ((Nat.iterate stride (ℓ - 1)) x) = κ ∧
      StrideWordCell r tail (nextBlock x) := by
  rw [prefix_ones_cell]
  simp only [StrideWordCell]
  constructor
  · rintro ⟨hones, hk, hc⟩
    have hr : blockLength x = ℓ := by
      have h := blockLength_of_first_exit x (ℓ - 1) hx hones (by omega)
      simpa only [Nat.sub_add_cancel hℓ] using h
    exact ⟨hr, hk, by simpa only [exit_stride_eq_nextBlock x ℓ hℓ hr] using hc⟩
  · rintro ⟨hr, hk, hc⟩
    refine ⟨?_, hk, ?_⟩
    · intro t ht
      exact (block_length_law x hx).2.1 t (by rw [hr]; omega)
    · simpa only [exit_stride_eq_nextBlock x ℓ hℓ hr] using hc

/-- Chronological valuation word: each block's ones followed by its exact exit. -/
def blockWord : (m : ℕ) → (Fin (m + 1) → ℕ) → (Fin m → ℕ) → List ℕ
  | 0, _, _ => []
  | m + 1, lengths, exits =>
    List.replicate (lengths 0 - 1) 1 ++
      exits 0 :: blockWord m (fun i => lengths i.succ) (fun i => exits i.succ)

theorem blockWord_sum (m : ℕ) (lengths : Fin (m + 1) → ℕ) (exits : Fin m → ℕ) :
    (blockWord m lengths exits).sum =
      ∑ i : Fin m, (lengths i.castSucc - 1 + exits i) := by
  induction m with
  | zero => simp [blockWord]
  | succ m ih =>
    simp only [blockWord, List.sum_append, List.sum_replicate_nat, Nat.mul_one,
      List.sum_cons, ih, Fin.sum_univ_succ]
    simp only [Fin.castSucc_zero, Fin.succ_castSucc, Nat.add_assoc]

theorem blockWord_positive (m : ℕ) (lengths : Fin (m + 1) → ℕ) (exits : Fin m → ℕ)
    (hκ : ∀ i, 1 ≤ exits i) : ∀ k ∈ blockWord m lengths exits, 1 ≤ k := by
  induction m with
  | zero => simp [blockWord]
  | succ m ih =>
    intro k hk
    simp only [blockWord, List.mem_append, List.mem_replicate, List.mem_cons] at hk
    rcases hk with ⟨_, rfl⟩ | rfl | hk
    · exact le_rfl
    · exact hκ 0
    · exact ih (fun i => lengths i.succ) (fun i => exits i.succ) (fun i => hκ i.succ) k hk

theorem futureBlockSeed_after_next (x i : ℕ) :
    futureBlockSeed (nextBlock x) i = futureBlockSeed x (i + 1) := by
  simp only [futureBlockSeed, Function.iterate_succ_apply]

theorem refinedCell_zero (lengths : Fin 1 → ℕ) (exits : Fin 0 → ℕ) (x : ℕ) :
    RefinedCell 0 lengths exits x ↔
      IsOddSeed x ∧ blockLength x = lengths (Fin.last 0) := by
  simp [RefinedCell, Fin.forall_fin_succ, futureBlockSeed]

theorem refinedCell_succ (m : ℕ) (lengths : Fin (m + 2) → ℕ)
    (exits : Fin (m + 1) → ℕ) (x : ℕ) :
    RefinedCell (m + 1) lengths exits x ↔
      IsOddSeed x ∧ blockLength x = lengths 0 ∧
      strideValuation ((Nat.iterate stride (lengths 0 - 1)) x) = exits 0 ∧
      RefinedCell m (fun i => lengths i.succ) (fun i => exits i.succ) (nextBlock x) := by
  constructor
  · rintro ⟨hx, hl, hk⟩
    refine ⟨hx, ?_, ?_, nextBlock_odd x hx, ?_, ?_⟩
    · simpa [futureBlockSeed] using hl 0
    · simpa [futureBlockSeed] using hk 0
    · intro i
      rw [futureBlockSeed_after_next]
      simpa only [Fin.val_succ] using hl i.succ
    · intro i
      rw [futureBlockSeed_after_next]
      simpa only [Fin.val_succ, Fin.succ_castSucc] using hk i.succ
  · rintro ⟨hx, hl0, hk0, _, hlt, hkt⟩
    refine ⟨hx, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa [futureBlockSeed] using hl0
      · simpa only [futureBlockSeed_after_next, Fin.val_succ] using hlt j
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa [futureBlockSeed] using hk0
      · simpa only [futureBlockSeed_after_next, Fin.val_succ, Fin.succ_castSucc] using hkt j

/-- Literal refined block data are exactly the compiled finite valuation word. -/
theorem refinedCell_iff_word (m : ℕ) (lengths : Fin (m + 1) → ℕ)
    (exits : Fin m → ℕ) (hdata : ValidBlockData m lengths exits) (x : ℕ) :
    RefinedCell m lengths exits x ↔
      IsOddSeed x ∧
      StrideWordCell (lengths (Fin.last m)) (blockWord m lengths exits) x := by
  induction m generalizing x with
  | zero => simpa only [blockWord, StrideWordCell] using refinedCell_zero lengths exits x
  | succ m ih =>
    let tailLengths : Fin (m + 1) → ℕ := fun i => lengths i.succ
    let tailExits : Fin m → ℕ := fun i => exits i.succ
    have htail : ValidBlockData m tailLengths tailExits :=
      ⟨fun i => hdata.1 i.succ, fun i => hdata.2 i.succ⟩
    rw [refinedCell_succ]
    constructor
    · rintro ⟨hx, hl, hk, hc⟩
      have ht := (ih tailLengths tailExits htail (nextBlock x)).mp hc
      refine ⟨hx, ?_⟩
      apply (block_word_cell _ (lengths 0) (exits 0)
        (blockWord m tailLengths tailExits) x hx (hdata.1 0) (hdata.2 0)).mpr
      exact ⟨hl, hk, ht.2⟩
    · rintro ⟨hx, hc⟩
      have ht := (block_word_cell (lengths (Fin.last (m + 1))) (lengths 0) (exits 0)
        (blockWord m tailLengths tailExits) x hx (hdata.1 0) (hdata.2 0)).mp hc
      refine ⟨hx, ht.1, ht.2.1, ?_⟩
      exact (ih tailLengths tailExits htail (nextBlock x)).mpr ⟨nextBlock_odd x hx, ht.2.2⟩

theorem blockWord_exponent (m : ℕ) (lengths : Fin (m + 1) → ℕ) (exits : Fin m → ℕ) :
    (blockWord m lengths exits).sum + lengths (Fin.last m) = refinedExponent m lengths exits := by
  rw [blockWord_sum]
  rfl

/-- The frozen arithmetic realization target, with no population-law assumption. -/
theorem refined_cylinder_classes : RefinedCylinderClasses := by
  intro m lengths exits hdata
  have hpositive : ∀ k ∈ blockWord m lengths exits, 1 ≤ k :=
    blockWord_positive m lengths exits (fun i => Nat.le_trans (by decide) (hdata.2 i))
  have hlast : 1 ≤ lengths (Fin.last m) := by
    have h := hdata.1 (Fin.last m)
    omega
  obtain ⟨d, ⟨hd, hevent⟩, hunique⟩ := stride_word_unique_class
    (blockWord m lengths exits) (lengths (Fin.last m)) hpositive hlast
  have hE := blockWord_exponent m lengths exits
  have hcell (n : ℕ) : RefinedCell m lengths exits (2 * n + 1) ↔
      StrideWordCell (lengths (Fin.last m)) (blockWord m lengths exits) (2 * n + 1) := by
    have hx : IsOddSeed (2 * n + 1) := ⟨by omega, by omega⟩
    simpa only [hx, true_and] using refinedCell_iff_word m lengths exits hdata (2 * n + 1)
  refine ⟨d, ⟨by simpa only [hE] using hd, ?_⟩, ?_⟩
  · intro n
    exact (hcell n).trans (by simpa only [hE] using hevent n)
  · rintro d' ⟨hd', hevent'⟩
    apply hunique d'
    refine ⟨by simpa only [hE] using hd', ?_⟩
    intro n
    simpa only [hE] using (hcell n).symm.trans (hevent' n)

end ExternalO3GeneralBlockWords
