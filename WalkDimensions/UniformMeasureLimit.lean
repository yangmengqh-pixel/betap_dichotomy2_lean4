import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Uniform limits of finite measures on measurable sets
-/

open Filter Function MeasureTheory Set
open scoped ENNReal Topology

namespace WalkDimensions

variable {X : Type*} [MeasurableSpace X]

theorem exists_measure_of_uniform_real_limit (ν : ℕ → Measure X) [∀ n, IsFiniteMeasure (ν n)]
    (V : Set X → ℝ) (hV : ∀ A, MeasurableSet A → 0 ≤ V A)
    (huniform : ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ A, MeasurableSet A →
      |(ν n A).toReal - V A| < ε) :
    ∃ μ : Measure X, ∀ A, MeasurableSet A → μ A = ENNReal.ofReal (V A) := by
  have hlimit (A : Set X) (hA : MeasurableSet A) :
      Tendsto (fun n ↦ (ν n A).toReal) atTop (𝓝 (V A)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [huniform ε hε] with n hn
    simpa only [Real.dist_eq] using hn A hA
  have hzero : V ∅ = 0 := by
    apply tendsto_nhds_unique (hlimit ∅ MeasurableSet.empty)
    simp only [measure_empty, ENNReal.toReal_zero, tendsto_const_nhds]
  have hunion {S : ℕ → Set X} (hS : ∀ i, MeasurableSet (S i)) (hdis : Pairwise (Disjoint on S)) :
      HasSum (fun i ↦ V (S i)) (V (⋃ i, S i)) := by
    let T (n : ℕ) := ⋃ i ∈ Finset.range n, S i
    let U := ⋃ i, S i
    have hT (n : ℕ) : MeasurableSet (T n) := Finset.measurableSet_biUnion _ (fun i _ ↦ hS i)
    have hU : MeasurableSet U := MeasurableSet.iUnion hS
    have hMono : Monotone T := by
      intro n m h
      exact iUnion₂_mono' fun i hi ↦ ⟨i, Finset.range_mono h hi, subset_rfl⟩
    have hUnion : (⋃ n, T n) = U := by
      ext x
      simp only [T, U, mem_iUnion, Finset.mem_range]
      constructor
      · rintro ⟨n, i, _, hx⟩
        exact ⟨i, hx⟩
      · rintro ⟨i, hi⟩
        exact ⟨i + 1, i, Nat.lt_succ_self i, hi⟩
    have hFinite (n : ℕ) : V (T n) = ∑ j ∈ Finset.range n, V (S j) := by
      have hSum (t : Finset ℕ) : Tendsto (fun k ↦ ∑ j ∈ t, (ν k (S j)).toReal)
          atTop (𝓝 (∑ j ∈ t, V (S j))) := by
        classical
        induction t using Finset.induction_on with
        | empty => simpa only [Finset.sum_empty] using tendsto_const_nhds
        | insert i t hi ih =>
            simp only [Finset.sum_insert hi]
            exact (hlimit _ (hS i)).add ih
      apply tendsto_nhds_unique (hlimit (T n) (hT n))
      have hEq (k : ℕ) : (ν k (T n)).toReal = ∑ j ∈ Finset.range n, (ν k (S j)).toReal := by
        rw [measure_biUnion_finset (fun _ _ _ _ h ↦ hdis h) (fun i _ ↦ hS i),
          ENNReal.toReal_sum (fun i _ ↦ measure_ne_top _ _)]
      simp_rw [hEq]
      exact hSum _
    rw [hasSum_iff_tendsto_nat_of_nonneg (fun i ↦ hV _ (hS i))]
    simp_rw [← hFinite]
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨k, hk⟩ := (huniform (ε / 3) (div_pos hε (by norm_num))).exists
    have hνlim : Tendsto (fun n ↦ (ν k (T n)).toReal) atTop (𝓝 ((ν k U).toReal)) := by
      apply (ENNReal.continuousAt_toReal (measure_ne_top (ν k) U)).tendsto.comp
      rw [← hUnion]
      exact tendsto_measure_iUnion_atTop hMono
    filter_upwards [(Metric.tendsto_nhds.mp hνlim) (ε / 3) (div_pos hε (by norm_num))] with n hn
    have h₁ := hk (T n) (hT n)
    have h₂ := hk U hU
    rw [Real.dist_eq] at hn ⊢
    exact abs_lt.mpr ⟨by linarith only [(abs_lt.mp h₁).2, (abs_lt.mp h₂).1, (abs_lt.mp hn).1],
      by linarith only [(abs_lt.mp h₁).1, (abs_lt.mp h₂).2, (abs_lt.mp hn).2]⟩
  let μ := Measure.ofMeasurable (fun A _ ↦ ENNReal.ofReal (V A))
    (by rw [hzero, ENNReal.ofReal_zero]) (fun {S} hS hd ↦ by
      have h := hunion hS hd
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun i ↦ hV _ (hS i)) h.summable, h.tsum_eq])
  exact ⟨μ, fun A hA ↦ Measure.ofMeasurable_apply A hA⟩

end WalkDimensions
