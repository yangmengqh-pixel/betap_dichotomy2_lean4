import WalkDimensions.EnergyMeasureClarkson
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan

/-!
# Signed energy measures from first variation
-/

open Filter Function MeasureTheory Set
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {p : ℝ} (E : PEnergy μ p)

noncomputable def energyVariation (f : E.domain) (A : Set X) (hA : MeasurableSet A) :
    E.domain →ₗ[ℝ] ℝ := (E.exists_energyMeasure_first_variation f hA).choose

theorem hasDerivAt_energyMeasure (f g : E.domain) {A : Set X} (hA : MeasurableSet A) :
    HasDerivAt (fun t : ℝ ↦ (E.energyMeasure (f + t • g) A).toReal)
      (p * E.energyVariation f A hA g) 0 :=
  (E.exists_energyMeasure_first_variation f hA).choose_spec.1 g

theorem abs_energyVariation_le (f g : E.domain) {A : Set X} (hA : MeasurableSet A) :
    |E.energyVariation f A hA g| ≤
      (E.energyMeasureRoot A hA f) ^ (p - 1) * E.energyMeasureRoot A hA g :=
  (E.exists_energyMeasure_first_variation f hA).choose_spec.2 g

private noncomputable def variationValue (f g : E.domain) (A : Set X) : ℝ := by
  classical
  exact if hA : MeasurableSet A then E.energyVariation f A hA g else 0

private theorem variationValue_eq (f g : E.domain) {A : Set X} (hA : MeasurableSet A) :
    E.variationValue f g A = E.energyVariation f A hA g := by
  unfold variationValue
  exact dite_eq_left hA

private theorem variationValue_empty (f g : E.domain) : E.variationValue f g ∅ = 0 := by
  rw [E.variationValue_eq f g MeasurableSet.empty]
  have h := E.hasDerivAt_energyMeasure f g MeasurableSet.empty
  simp only [measure_empty, ENNReal.toReal_zero] at h
  exact (mul_eq_zero.mp (h.unique (hasDerivAt_const (0 : ℝ) (0 : ℝ)))).resolve_left
    (zero_lt_one.trans E.one_lt).ne'

private theorem variationValue_union (f g : E.domain) {A B : Set X}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hdis : Disjoint A B) :
    E.variationValue f g (A ∪ B) = E.variationValue f g A + E.variationValue f g B := by
  have hAB := E.hasDerivAt_energyMeasure f g (hA.union hB)
  have hA' := E.hasDerivAt_energyMeasure f g hA
  have hB' := E.hasDerivAt_energyMeasure f g hB
  have he : (fun t : ℝ ↦ (E.energyMeasure (f + t • g) (A ∪ B)).toReal) =
      fun t : ℝ ↦ (E.energyMeasure (f + t • g) A).toReal + (E.energyMeasure (f + t • g) B).toReal := by
    funext t
    rw [measure_union hdis hB, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  rw [he] at hAB
  rw [E.variationValue_eq f g (hA.union hB), E.variationValue_eq f g hA, E.variationValue_eq f g hB]
  apply mul_left_cancel₀ (zero_lt_one.trans E.one_lt).ne'
  rw [mul_add]
  exact hAB.unique (hA'.add hB')

private theorem abs_variationValue_le_measure_add (f g : E.domain) {A : Set X}
    (hA : MeasurableSet A) :
    |E.variationValue f g A| ≤ ((E.energyMeasure f + E.energyMeasure g) A).toReal := by
  rw [E.variationValue_eq f g hA, FunLike.coe_add, Pi.add_apply,
    ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
    E.energyMeasure_real_eq f hA, E.energyMeasure_real_eq g hA]
  let a := E.energyMeasureRoot A hA f
  let b := E.energyMeasureRoot A hA g
  have ha : 0 ≤ a := apply_nonneg _ _
  have hb : 0 ≤ b := apply_nonneg _ _
  apply (E.abs_energyVariation_le f g hA).trans
  change a ^ (p - 1) * b ≤ a ^ p + b ^ p
  rcases le_total a b with hab | hab
  · have h := Real.rpow_le_rpow ha hab (sub_nonneg.mpr E.one_lt.le)
    apply (mul_le_mul_of_nonneg_right h hb).trans
    have he : b ^ (p - 1) * b = b ^ p := by
      nth_rw 2 [← Real.rpow_one b]
      rw [← Real.rpow_add' hb (by linarith only [E.one_lt]), sub_add_cancel]
    rw [he]
    exact le_add_of_nonneg_left (Real.rpow_nonneg ha _)
  · apply (mul_le_mul_of_nonneg_left hab (Real.rpow_nonneg ha _)).trans
    have he : a ^ (p - 1) * a = a ^ p := by
      nth_rw 2 [← Real.rpow_one a]
      rw [← Real.rpow_add' ha (by linarith only [E.one_lt]), sub_add_cancel]
    rw [he]
    exact le_add_of_nonneg_right (Real.rpow_nonneg hb _)

private theorem variationValue_biUnion (f g : E.domain) {ι : Type*} (s : Finset ι)
    (S : ι → Set X) (hm : ∀ i, MeasurableSet (S i)) (hdis : Pairwise (Disjoint on S)) :
    E.variationValue f g (⋃ i ∈ s, S i) = ∑ i ∈ s, E.variationValue f g (S i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty, Finset.sum_empty,
      E.variationValue_empty]
  | insert i t hi ih =>
      rw [Finset.set_biUnion_insert, Finset.sum_insert hi, E.variationValue_union f g
        (hm i) (Finset.measurableSet_biUnion _ (fun j _ ↦ hm j)) _ , ih]
      refine disjoint_iUnion_right.mpr fun j ↦ disjoint_iUnion_right.mpr fun hj ↦ ?_
      exact hdis (fun he ↦ hi (he ▸ hj))

private theorem variationValue_iUnion (f g : E.domain) {S : ℕ → Set X}
    (hS : ∀ i, MeasurableSet (S i)) (hdis : Pairwise (Disjoint on S)) :
    HasSum (fun i ↦ E.variationValue f g (S i)) (E.variationValue f g (⋃ i, S i)) := by
  let ν := E.energyMeasure f + E.energyMeasure g
  let T (t : Finset ℕ) := ⋃ i ∈ t, S i
  let U := ⋃ i, S i
  have hT (t : Finset ℕ) : MeasurableSet (T t) := Finset.measurableSet_biUnion _ (fun i _ ↦ hS i)
  have hU : MeasurableSet U := MeasurableSet.iUnion hS
  have hMono : Monotone T := by
    intro t r ht
    exact iUnion₂_mono' fun i hi ↦ ⟨i, ht hi, subset_rfl⟩
  have hUnion : (⋃ t, T t) = U := by
    ext x
    simp only [T, U, mem_iUnion]
    constructor
    · rintro ⟨t, i, _, hx⟩
      exact ⟨i, hx⟩
    · rintro ⟨i, hx⟩
      exact ⟨{i}, i, Finset.mem_singleton_self _, hx⟩
  have hTU (t : Finset ℕ) : T t ⊆ U := by rw [← hUnion]; exact subset_iUnion _ _
  have hlim : Tendsto (fun t ↦ (ν (T t)).toReal) atTop (𝓝 ((ν U).toReal)) := by
    apply (ENNReal.continuousAt_toReal (measure_ne_top ν U)).tendsto.comp
    rw [← hUnion]
    exact tendsto_measure_iUnion_atTop hMono
  have hTail : Tendsto (fun t ↦ (ν (U \ T t)).toReal) atTop (𝓝 0) := by
    have he (t : Finset ℕ) : (ν (U \ T t)).toReal = (ν U).toReal - (ν (T t)).toReal := by
      rw [measure_sdiff (hTU t) (hT t).nullMeasurableSet (measure_ne_top _ _),
        ENNReal.toReal_sub_of_le (measure_mono (hTU t)) (measure_ne_top _ _)]
    simp_rw [he]
    simpa only [sub_self] using hlim.const_sub ((ν U).toReal)
  change Tendsto (fun t : Finset ℕ ↦ ∑ i ∈ t, E.variationValue f g (S i))
    atTop (𝓝 (E.variationValue f g U))
  simp_rw [← E.variationValue_biUnion f g _ S hS hdis]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hTail.eventually_lt_const hε] with t ht
  change dist (E.variationValue f g (T t)) (E.variationValue f g U) < ε
  have he : E.variationValue f g U = E.variationValue f g (T t) +
      E.variationValue f g (U \ T t) := by
    have h := E.variationValue_union f g (hT t) (hU.diff (hT t)) disjoint_sdiff_right
    have hset : T t ∪ (U \ T t) = U := by
      ext x
      have hsub := @hTU t x
      simp only [mem_union, Set.mem_sdiff]
      tauto
    rwa [hset] at h
  rw [Real.dist_eq, he, sub_add_cancel_left, abs_neg]
  exact (E.abs_variationValue_le_measure_add f g (hU.diff (hT t))).trans_lt ht

/-- The signed measure given by the derivative in the second energy argument. -/
noncomputable def energyDerivativeMeasure (f g : E.domain) : SignedMeasure X where
  measureOf' := E.variationValue f g
  empty' := E.variationValue_empty f g
  not_measurable' := fun {_} hA ↦ by
    unfold variationValue
    exact dite_eq_right hA
  m_iUnion' := fun {_} hS hd ↦ E.variationValue_iUnion f g hS hd

theorem energyDerivativeMeasure_apply (f g : E.domain) {A : Set X} (hA : MeasurableSet A) :
    E.energyDerivativeMeasure f g A = E.energyVariation f A hA g :=
  E.variationValue_eq f g hA

end WalkDimensions.PEnergy
