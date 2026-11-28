import CountablePartition

/-!
General-index form of the literal countable-partition density transfer.
The independent proof uses finite label sets directed by inclusion, not a
coding into natural labels. Summability and total mass one provide tightness.
No countability assumption on the index type and no uniform stabilization
threshold is needed. All population frequencies are the original literal
Finset.range-cardinality/N functions imported from CountablePartition.
This is a generic theorem; no Syracuse-cylinder hypotheses are established here.
-/
namespace ExternalO3PartitionGeneral

open Filter ExternalO3CountablePartition
open scoped Topology BigOperators

/-- Finite truncation and order squeeze for countably many coordinates. -/
theorem finite_tail_squeeze {ι : Type*}
    (a : ℕ → ℝ) (μ ν : ι → ℕ → ℝ) (w v : ι → ℝ)
    (hw : Summable w) (hv : Summable v) (hwtotal : ∑' i, w i = 1)
    (hμ : ∀ i, Tendsto (μ i) atTop (𝓝 (w i)))
    (hν : ∀ i, Tendsto (ν i) atTop (𝓝 (v i)))
    (hbounds : ∀ s : Finset ι, ∀ᶠ N in atTop,
      (∑ i ∈ s, ν i N) ≤ a N ∧
      a N ≤ (∑ i ∈ s, ν i N) + 1 -
        (∑ i ∈ s, μ i N)) :
    Tendsto a atTop (𝓝 (∑' i, v i)) := by
  have hvs : Tendsto (fun s : Finset ι => ∑ i ∈ s, v i)
      atTop (𝓝 (∑' i, v i)) := hv.hasSum
  have hws : Tendsto (fun s : Finset ι => ∑ i ∈ s, w i)
      atTop (𝓝 (1 : ℝ)) := by
    rw [← hwtotal]
    exact hw.hasSum
  have hupper : Tendsto (fun s : Finset ι =>
      (∑ i ∈ s, v i) + 1 - (∑ i ∈ s, w i))
      atTop (𝓝 (∑' i, v i)) := by
    simpa using (hvs.add_const 1).sub hws
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro lower hlower
    obtain ⟨s, hK⟩ := ((tendsto_order.1 hvs).1 lower hlower).exists
    have hfinite : Tendsto (fun N => ∑ i ∈ s, ν i N)
        atTop (𝓝 (∑ i ∈ s, v i)) :=
      tendsto_finsetSum _ (fun i _ => hν i)
    filter_upwards [(tendsto_order.1 hfinite).1 lower hK, hbounds s] with N hN hb
    exact hN.trans_le hb.1
  · intro upper hupperBound
    obtain ⟨s, hK⟩ := ((tendsto_order.1 hupper).2 upper hupperBound).exists
    have hfiniteν : Tendsto (fun N => ∑ i ∈ s, ν i N)
        atTop (𝓝 (∑ i ∈ s, v i)) :=
      tendsto_finsetSum _ (fun i _ => hν i)
    have hfiniteμ : Tendsto (fun N => ∑ i ∈ s, μ i N)
        atTop (𝓝 (∑ i ∈ s, w i)) :=
      tendsto_finsetSum _ (fun i _ => hμ i)
    have hfinite := (hfiniteν.add_const 1).sub hfiniteμ
    filter_upwards [(tendsto_order.1 hfinite).2 upper hK, hbounds s] with N hN hb
    exact hb.2.trans_lt hN

/-- Finite sums of averages can be interchanged with population averages. -/
theorem sum_average {ι : Type*} (u : ι → ℕ → ℝ) (s : Finset ι) (N : ℕ) :
    (∑ i ∈ s, average (u i) N) =
      average (fun n => ∑ i ∈ s, u i n) N := by
  simp only [average, div_eq_mul_inv, ← Finset.sum_mul]
  congr 1
  exact Finset.sum_comm

/-- A population element has at most one label in a finite truncation. -/
theorem label_bits {ι : Type*} (label : ℕ → ι) (s : Finset ι) (n : ℕ) :
    (∑ i ∈ s, bit (fun m => label m = i) n) =
      bit (fun m => label m ∈ s) n := by
  classical
  by_cases hl : label n ∈ s
  · have hrhs : bit (fun m => label m ∈ s) n = 1 := by simp [bit, hl]
    rw [hrhs]
    calc
      (∑ i ∈ s, bit (fun m => label m = i) n) =
          bit (fun m => label m = label n) n :=
        Finset.sum_eq_single_of_mem (label n) hl
          (fun i _ hi => by simp [bit, hi.symm])
      _ = 1 := by simp [bit]
  · have hrhs : bit (fun m => label m ∈ s) n = 0 := by simp [bit, hl]
    rw [hrhs]
    apply Finset.sum_eq_zero
    intro i hi
    have hne : label n ≠ i := by
      intro heq
      exact hl (heq ▸ hi)
    simp [bit, hne]

/-- The same identity for the selected (failing) part of each label. -/
theorem selected_label_bits {ι : Type*} (label : ℕ → ι) (fails : ℕ → Prop) (s : Finset ι) (n : ℕ) :
    (∑ i ∈ s, bit (fun m => label m = i ∧ fails m) n) =
      bit (fun m => label m ∈ s ∧ fails m) n := by
  classical
  by_cases hf : fails n
  · calc
      (∑ i ∈ s, bit (fun m => label m = i ∧ fails m) n) =
          (∑ i ∈ s, bit (fun m => label m = i) n) := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : label n = i <;> simp [bit, hf, hi]
      _ = bit (fun m => label m ∈ s ∧ fails m) n := by
        rw [label_bits]
        by_cases hl : label n ∈ s <;> simp [bit, hf, hl]
  · simp [bit, hf]

/-- The finite-label error is bounded by the uncovered population mass. -/
theorem finite_partition_bounds {ι : Type*} (label : ℕ → ι) (fails : ℕ → Prop)
    (s : Finset ι) (N : ℕ) (hN : 0 < N) :
    (∑ i ∈ s, frequency (fun n => label n = i ∧ fails n) N) ≤
      frequency fails N ∧
    frequency fails N ≤
      (∑ i ∈ s, frequency (fun n => label n = i ∧ fails n) N) +
      1 - (∑ i ∈ s, frequency (fun n => label n = i) N) := by
  classical
  have hpoint (n : ℕ) :
      (∑ i ∈ s, bit (fun m => label m = i ∧ fails m) n) ≤ bit fails n ∧
      bit fails n ≤
        (∑ i ∈ s, bit (fun m => label m = i ∧ fails m) n) + 1 -
        (∑ i ∈ s, bit (fun m => label m = i) n) := by
    rw [selected_label_bits, label_bits]
    by_cases hf : fails n <;> by_cases hl : label n ∈ s <;> simp [bit, hf, hl]
  have hlo := Finset.sum_le_sum (s := Finset.range N) (fun n _ => (hpoint n).1)
  have hhi := Finset.sum_le_sum (s := Finset.range N) (fun n _ => (hpoint n).2)
  have hNreal : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  simp_rw [frequency_eq_average]
  rw [sum_average, sum_average]
  constructor
  · exact div_le_div_of_nonneg_right hlo hNreal.le
  · have hdiv := div_le_div_of_nonneg_right hhi hNreal.le
    simpa only [average, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, add_div,
      sub_div, div_self hNreal.ne'] using hdiv

/-- Select a subfamily of cylinder masses. -/
noncomputable def selectedWeight {ι : Type*} (bad : ι → Prop) (w : ι → ℝ) (i : ι) : ℝ := by
  classical
  exact if bad i then w i else 0

/-- Per-cylinder eventual agreement suffices; its threshold may depend on i. -/
theorem selected_frequency_limit {ι : Type*}
    (label : ℕ → ι) (fails : ℕ → Prop) (bad : ι → Prop) (w : ι → ℝ)
    (i : ι)
    (hmass : Tendsto (frequency (fun n => label n = i)) atTop (𝓝 (w i)))
    (hstable : ∃ M, ∀ n, M ≤ n → label n = i → (fails n ↔ bad i)) :
    Tendsto (frequency (fun n => label n = i ∧ fails n))
      atTop (𝓝 (selectedWeight bad w i)) := by
  classical
  let Q : ℕ → Prop := fun n => label n = i ∧ bad i
  have hQ : Tendsto (frequency Q) atTop (𝓝 (selectedWeight bad w i)) := by
    change Tendsto (fun N => frequency Q N) atTop (𝓝 (selectedWeight bad w i))
    by_cases hb : bad i
    · simpa [Q, hb, selectedWeight] using hmass
    · simp [Q, hb, selectedWeight, frequency]
  apply frequency_of_eventually_iff _ Q _ ?_ hQ
  obtain ⟨M, hM⟩ := hstable
  filter_upwards [eventually_ge_atTop M] with n hn
  by_cases hi : label n = i
  · simpa only [Q, hi, true_and] using hM n hn hi
  · simp only [Q, hi, false_and]

/-- Countable-cylinder density transfer for literal finite-population counts.
The label map is a disjoint exhaustive countable partition. Neither uniform
stabilization nor countable additivity of natural density is a hypothesis. -/
theorem countable_partition_density {ι : Type*}
    (label : ℕ → ι) (fails : ℕ → Prop) (bad : ι → Prop) (w : ι → ℝ)
    (hw : Summable w) (hwtotal : ∑' i, w i = 1)
    (hmass : ∀ i, Tendsto (frequency (fun n => label n = i)) atTop (𝓝 (w i)))
    (hstable : ∀ i, ∃ M, ∀ n, M ≤ n → label n = i → (fails n ↔ bad i)) :
    Tendsto (frequency fails) atTop (𝓝 (∑' i, selectedWeight bad w i)) := by
  classical
  have hv : Summable (selectedWeight bad w) := by
    have heq : selectedWeight bad w = {i | bad i}.indicator w := by
      funext i
      simp [selectedWeight, Set.indicator]
    rw [heq]
    exact hw.indicator {i | bad i}
  apply finite_tail_squeeze (frequency fails)
    (fun i => frequency (fun n => label n = i))
    (fun i => frequency (fun n => label n = i ∧ fails n))
    w (selectedWeight bad w) hw hv hwtotal hmass
    (fun i => selected_frequency_limit label fails bad w i (hmass i) (hstable i))
  intro s
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact finite_partition_bounds label fails s N hN

end ExternalO3PartitionGeneral
