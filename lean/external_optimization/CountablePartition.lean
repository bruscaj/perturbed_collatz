import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
Generic countable-partition transfer, independently reconstructed.
For each finite set of labels, eventually stable failure decisions have the
corresponding weighted finite density. The error outside those labels is
bounded by their uncovered population mass. Summable weights with total one
make this mass arbitrarily small. No uniform stabilization threshold and no
countable-union density theorem are assumed.
For a fixed cutoff K, write μ_i(N) for label-i frequency and ν_i(N) for
label-i failure frequency. Pointwise disjointness gives
  sum_(i<K) ν_i(N) ≤ failure frequency ≤ sum_(i<K) ν_i(N) + 1 - sum_(i<K) μ_i(N).
Eventual agreement on each fixed label makes its indicator difference tend to
zero; Cesàro averaging therefore gives ν_i(N) → selectedWeight_i. Taking the
finite-coordinate limits and then K → infinity makes both endpoints approach
the same selected total, because the full label masses sum to one. The proof
uses order neighborhoods to perform these two limits, rather than interchanging
an infinite sum with a natural-density limit.
This file does not identify the Syracuse cylinders or establish their premises.
-/
namespace ExternalO3CountablePartition
open Filter
open scoped Topology BigOperators

/-- Actual natural frequency in the first N population indices. -/
noncomputable def frequency (P : ℕ → Prop) (N : ℕ) : ℝ := by
  classical
  exact ((Finset.range N).filter P).card / (N : ℝ)

noncomputable def bit (P : ℕ → Prop) (n : ℕ) : ℝ := by
  classical
  exact if P n then 1 else 0

noncomputable def average (u : ℕ → ℝ) (N : ℕ) : ℝ :=
  (∑ n ∈ Finset.range N, u n) / (N : ℝ)

theorem frequency_eq_average (P : ℕ → Prop) (N : ℕ) :
    frequency P N = average (bit P) N := by
  classical
  simp [frequency, average, bit]

/-- Finite truncation and order squeeze for countably many coordinates. -/
theorem finite_tail_squeeze
    (a : ℕ → ℝ) (μ ν : ℕ → ℕ → ℝ) (w v : ℕ → ℝ)
    (hw : Summable w) (hv : Summable v) (hwtotal : ∑' i, w i = 1)
    (hμ : ∀ i, Tendsto (μ i) atTop (𝓝 (w i)))
    (hν : ∀ i, Tendsto (ν i) atTop (𝓝 (v i)))
    (hbounds : ∀ K, ∀ᶠ N in atTop,
      (∑ i ∈ Finset.range K, ν i N) ≤ a N ∧
      a N ≤ (∑ i ∈ Finset.range K, ν i N) + 1 -
        (∑ i ∈ Finset.range K, μ i N)) :
    Tendsto a atTop (𝓝 (∑' i, v i)) := by
  have hvs : Tendsto (fun K => ∑ i ∈ Finset.range K, v i)
      atTop (𝓝 (∑' i, v i)) := hv.hasSum.tendsto_sum_nat
  have hws : Tendsto (fun K => ∑ i ∈ Finset.range K, w i)
      atTop (𝓝 (1 : ℝ)) := by
    simpa only [hwtotal] using hw.hasSum.tendsto_sum_nat
  have hupper : Tendsto (fun K =>
      (∑ i ∈ Finset.range K, v i) + 1 - (∑ i ∈ Finset.range K, w i))
      atTop (𝓝 (∑' i, v i)) := by
    simpa using (hvs.add_const 1).sub hws
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro lower hlower
    obtain ⟨K, hK⟩ := ((tendsto_order.1 hvs).1 lower hlower).exists
    have hfinite : Tendsto (fun N => ∑ i ∈ Finset.range K, ν i N)
        atTop (𝓝 (∑ i ∈ Finset.range K, v i)) :=
      tendsto_finsetSum _ (fun i _ => hν i)
    filter_upwards [(tendsto_order.1 hfinite).1 lower hK, hbounds K] with N hN hb
    exact hN.trans_le hb.1
  · intro upper hupperBound
    obtain ⟨K, hK⟩ := ((tendsto_order.1 hupper).2 upper hupperBound).exists
    have hfiniteν : Tendsto (fun N => ∑ i ∈ Finset.range K, ν i N)
        atTop (𝓝 (∑ i ∈ Finset.range K, v i)) :=
      tendsto_finsetSum _ (fun i _ => hν i)
    have hfiniteμ : Tendsto (fun N => ∑ i ∈ Finset.range K, μ i N)
        atTop (𝓝 (∑ i ∈ Finset.range K, w i)) :=
      tendsto_finsetSum _ (fun i _ => hμ i)
    have hfinite := (hfiniteν.add_const 1).sub hfiniteμ
    filter_upwards [(tendsto_order.1 hfinite).2 upper hK, hbounds K] with N hN hb
    exact hb.2.trans_lt hN

/-- Eventual changes to a predicate do not change an existing frequency limit. -/
theorem frequency_of_eventually_iff (P Q : ℕ → Prop) (d : ℝ)
    (hPQ : ∀ᶠ n in atTop, P n ↔ Q n)
    (hQ : Tendsto (frequency Q) atTop (𝓝 d)) :
    Tendsto (frequency P) atTop (𝓝 d) := by
  classical
  have hzero : Tendsto (fun n => bit P n - bit Q n) atTop (𝓝 (0 : ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hPQ] with n hn
    simp [bit, hn]
  have havg : Tendsto (average (fun n => bit P n - bit Q n))
      atTop (𝓝 (0 : ℝ)) := by
    change Tendsto (fun N => (∑ n ∈ Finset.range N, (bit P n - bit Q n)) / (N : ℝ))
      atTop (𝓝 (0 : ℝ))
    simpa only [div_eq_mul_inv, mul_comm] using hzero.cesaro
  have hdiff : Tendsto (fun N => frequency P N - frequency Q N)
      atTop (𝓝 (0 : ℝ)) := by
    change Tendsto (fun N => average (fun n => bit P n - bit Q n) N)
      atTop (𝓝 (0 : ℝ)) at havg
    simpa only [frequency_eq_average, average, Finset.sum_sub_distrib, sub_div] using havg
  simpa only [sub_add_cancel, zero_add] using hdiff.add hQ

/-- Finite sums of averages can be interchanged with population averages. -/
theorem sum_average (u : ℕ → ℕ → ℝ) (K N : ℕ) :
    (∑ i ∈ Finset.range K, average (u i) N) =
      average (fun n => ∑ i ∈ Finset.range K, u i n) N := by
  simp only [average, div_eq_mul_inv, ← Finset.sum_mul]
  congr 1
  exact Finset.sum_comm

/-- A population element has at most one label in a finite truncation. -/
theorem label_bits (label : ℕ → ℕ) (K n : ℕ) :
    (∑ i ∈ Finset.range K, bit (fun m => label m = i) n) =
      if label n < K then 1 else 0 := by
  classical
  by_cases hl : label n < K
  · rw [ite_eq_left hl]
    calc
      (∑ i ∈ Finset.range K, bit (fun m => label m = i) n) =
          bit (fun m => label m = label n) n :=
        Finset.sum_eq_single_of_mem (label n) (Finset.mem_range.mpr hl)
          (fun i _ hi => by simp [bit, hi.symm])
      _ = 1 := by simp [bit]
  · rw [ite_eq_right hl]
    apply Finset.sum_eq_zero
    intro i hi
    have hne : label n ≠ i := by
      intro heq
      exact hl (heq ▸ Finset.mem_range.mp hi)
    simp [bit, hne]

/-- The same identity for the selected (failing) part of each label. -/
theorem selected_label_bits (label : ℕ → ℕ) (fails : ℕ → Prop) (K n : ℕ) :
    (∑ i ∈ Finset.range K, bit (fun m => label m = i ∧ fails m) n) =
      bit (fun m => label m < K ∧ fails m) n := by
  classical
  by_cases hf : fails n
  · calc
      (∑ i ∈ Finset.range K, bit (fun m => label m = i ∧ fails m) n) =
          (∑ i ∈ Finset.range K, bit (fun m => label m = i) n) := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : label n = i <;> simp [bit, hf, hi]
      _ = bit (fun m => label m < K ∧ fails m) n := by
        rw [label_bits]
        by_cases hl : label n < K <;> simp [bit, hf, hl]
  · simp [bit, hf]

/-- The finite-label error is bounded by the uncovered population mass. -/
theorem finite_partition_bounds (label : ℕ → ℕ) (fails : ℕ → Prop)
    (K N : ℕ) (hN : 0 < N) :
    (∑ i ∈ Finset.range K, frequency (fun n => label n = i ∧ fails n) N) ≤
      frequency fails N ∧
    frequency fails N ≤
      (∑ i ∈ Finset.range K, frequency (fun n => label n = i ∧ fails n) N) +
      1 - (∑ i ∈ Finset.range K, frequency (fun n => label n = i) N) := by
  classical
  have hpoint (n : ℕ) :
      (∑ i ∈ Finset.range K, bit (fun m => label m = i ∧ fails m) n) ≤ bit fails n ∧
      bit fails n ≤
        (∑ i ∈ Finset.range K, bit (fun m => label m = i ∧ fails m) n) + 1 -
        (∑ i ∈ Finset.range K, bit (fun m => label m = i) n) := by
    rw [selected_label_bits, label_bits]
    by_cases hf : fails n <;> by_cases hl : label n < K <;> simp [bit, hf, hl]
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
noncomputable def selectedWeight (bad : ℕ → Prop) (w : ℕ → ℝ) (i : ℕ) : ℝ := by
  classical
  exact if bad i then w i else 0

/-- Per-cylinder eventual agreement suffices; its threshold may depend on i. -/
theorem selected_frequency_limit
    (label : ℕ → ℕ) (fails : ℕ → Prop) (bad : ℕ → Prop) (w : ℕ → ℝ)
    (i : ℕ)
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
theorem countable_partition_density
    (label : ℕ → ℕ) (fails : ℕ → Prop) (bad : ℕ → Prop) (w : ℕ → ℝ)
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
  intro K
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact finite_partition_bounds label fails K N hN

end ExternalO3CountablePartition
