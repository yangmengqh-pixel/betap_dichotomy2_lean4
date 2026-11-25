import WalkDimensions.EnergyDerivativeProduct
import WalkDimensions.CoreEnergyLevels

/-!
# Weighted derivatives and their local bounds
-/

open Filter Function MeasureTheory Set
open scoped ENNReal

namespace WalkDimensions

variable {X : Type*} [MeasurableSpace X]

theorem weightSignedMeasure_apply_eq_zero_of_forall (ν : SignedMeasure X)
    {u : X → ℝ} (hu : ν.Integrable u) {A : Set X} (hA : MeasurableSet A)
    (hzero : EqOn u (fun _ ↦ 0) A) : weightSignedMeasure ν u A = 0 := by
  have h := weightSignedMeasure_congr_on ν hu
    (integrable_vectorMeasure_of_bounded ν measurable_const (fun _ ↦ le_rfl) :
      ν.Integrable (fun _ : X ↦ (0 : ℝ))) hA hzero
  rwa [weightSignedMeasure_apply_const ν 0 hA, zero_mul] at h

theorem weightSignedMeasure_apply_inter_of_variation (ν : SignedMeasure X)
    {u : X → ℝ} (hu : ν.Integrable u) {A B : Set X}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hzero : ν.totalVariation (A \ B) = 0) :
    weightSignedMeasure ν u A = weightSignedMeasure ν u (A ∩ B) := by
  have hz : weightSignedMeasure ν u (A \ B) = 0 := by
    have h := abs_weightSignedMeasure_apply_le_lintegral ν hu (A := A \ B)
    rw [Measure.restrict_eq_zero.mpr hzero, lintegral_zero_measure, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at h
    exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
  have hd : Disjoint (A ∩ B) (A \ B) := disjoint_left.mpr fun _ hx hy ↦ hy.2 hx.2
  have h := VectorMeasure.of_union (v := weightSignedMeasure ν u) hd (hA.inter hB) (hA.diff hB)
  rwa [inter_union_sdiff, hz, add_zero] at h

theorem weightSignedMeasure_finsetSum {ι : Type*} (ν : SignedMeasure X)
    (t : Finset ι) {u : ι → X → ℝ} (h : ∀ i ∈ t, ν.Integrable (u i)) :
    weightSignedMeasure ν (∑ i ∈ t, u i) = ∑ i ∈ t, weightSignedMeasure ν (u i) := by
  ext A hA
  change (ν.withDensity (∑ i ∈ t, u i) (ContinuousLinearMap.lsmul ℝ ℝ)) A = _
  have hFun : (∑ i ∈ t, u i) = fun x ↦ ∑ i ∈ t, u i x :=
    funext fun x ↦ Finset.sum_apply x _ _
  rw [hFun, VectorMeasure.withDensity_apply (integrable_finsetSum _ h)]
  have he := VectorMeasure.integral_finsetSum (μ := ν.restrict A)
    (B := ContinuousLinearMap.lsmul ℝ ℝ) t (fun i hi ↦ (h i hi).restrict)
  rw [he]
  simp only [FunLike.coe_sum, Finset.sum_apply, weightSignedMeasure]
  exact Finset.sum_congr rfl fun i hi ↦ (VectorMeasure.withDensity_apply (h i hi)).symm

theorem weightSignedMeasure_finsetSum_measure {ι : Type*}
    (t : Finset ι) {ν : ι → SignedMeasure X} {u : X → ℝ}
    (h : ∀ i ∈ t, (ν i).Integrable u) :
    weightSignedMeasure (∑ i ∈ t, ν i) u = ∑ i ∈ t, weightSignedMeasure (ν i) u := by
  ext A hA
  change (∑ i ∈ t, ν i).withDensity u (ContinuousLinearMap.lsmul ℝ ℝ) A = _
  rw [VectorMeasure.withDensity_apply (VectorMeasure.Integrable.finsetSum_vectorMeasure h)]
  change ∫ᵛ x, u x ∂[ContinuousLinearMap.lsmul ℝ ℝ;
    (VectorMeasure.restrictₗ (R := ℝ) A) (∑ i ∈ t, ν i)] = _
  rw [map_sum]
  simp only [VectorMeasure.restrictₗ_apply]
  rw [VectorMeasure.integral_finsetSum_vectorMeasure
    (fun i hi ↦ (h i hi).restrict)]
  simp only [FunLike.coe_sum, Finset.sum_apply, weightSignedMeasure]
  exact Finset.sum_congr rfl fun i hi ↦ (VectorMeasure.withDensity_apply (h i hi)).symm

theorem sum_abs_weightSignedMeasure_apply_le {ι : Type*} (ν : SignedMeasure X)
    (t : Finset ι) {u : ι → X → ℝ} (hI : ∀ i ∈ t, ν.Integrable (u i))
    {A : Set X} (hA : MeasurableSet A) (h₀ : ∀ i ∈ t, ∀ x ∈ A, 0 ≤ u i x)
    (h₁ : ∀ x ∈ A, (∑ i ∈ t, u i x) ≤ 1) :
    (∑ i ∈ t, |weightSignedMeasure ν (u i) A|) ≤ (ν.totalVariation A).toReal := by
  let μ := ν.totalVariation.restrict A
  have hU (i : ι) (hi : i ∈ t) : Integrable (u i) μ := by
    change Integrable (u i) (ν.totalVariation.restrict A)
    rw [ν.totalVariation_eq_variation]
    exact (show Integrable (u i) ν.variation from hI i hi).integrableOn
  have h₀' (i : ι) (hi : i ∈ t) : 0 ≤ᵐ[μ] u i :=
    (ae_restrict_mem hA).mono (h₀ i hi)
  have hbound (i : ι) (hi : i ∈ t) :
      |weightSignedMeasure ν (u i) A| ≤ ∫ x, u i x ∂μ := by
    have h := abs_weightSignedMeasure_apply_le_lintegral ν (hI i hi) (A := A)
    change _ ≤ ∫⁻ x, ENNReal.ofReal |u i x| ∂μ at h
    have he : (∫⁻ x, ENNReal.ofReal |u i x| ∂μ) = ∫⁻ x, ENNReal.ofReal (u i x) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [h₀' i hi] with x hx
      rw [abs_of_nonneg hx]
    rw [he, ← ofReal_integral_eq_lintegral_ofReal (hU i hi) (h₀' i hi)] at h
    exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg_of_ae (h₀' i hi))).mp h
  calc
    _ ≤ ∑ i ∈ t, ∫ x, u i x ∂μ := Finset.sum_le_sum hbound
    _ = ∫ x, ∑ i ∈ t, u i x ∂μ := (integral_finsetSum t hU).symm
    _ ≤ ∫ _ : X, (1 : ℝ) ∂μ := integral_mono_ae (integrable_finsetSum _ hU)
      (integrable_const _) ((ae_restrict_mem hA).mono h₁)
    _ = _ := by simp [μ, integral_const, measureReal_def]

theorem weightSignedMeasure_of_toSignedMeasure_apply (ν : Measure X) [IsFiniteMeasure ν]
    {u : X → ℝ} (hu : (ν.toSignedMeasure).Integrable u) {A : Set X} (hA : MeasurableSet A) :
    weightSignedMeasure ν.toSignedMeasure u A = ∫ x in A, u x ∂ν := by
  have he : (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) =
      (ContinuousLinearMap.lsmul ℝ ℝ).flip := by
    ext; rfl
  rw [weightSignedMeasure, VectorMeasure.withDensity_apply hu, he,
    VectorMeasure.setIntegral_toSignedMeasure hA]

namespace PEnergy.CompactCore

variable [MetricSpace X] [LocallyCompactSpace X] [BorelSpace X]
  {m : Measure X} [IsFiniteMeasureOnCompacts m] {p : ℝ} {E : PEnergy m p}

theorem energyDerivativeMeasure_variation_zero_of_const_on (u v : E.CompactCore)
    {A : Set X} (hA : MeasurableSet A) {a : ℝ} (h0 : EqOn v.toFun (fun _ ↦ a) A) :
    (E.energyDerivativeMeasure u.domainElement v.domainElement).totalVariation A = 0 := by
  have hz : E.energyMeasure v.domainElement A = 0 := by
    rw [E.energyMeasure_core v]
    exact measure_mono_null h0 (v.coreEnergyMeasure_level a)
  have h := E.energyDerivativeMeasure_variation_le u.domainElement v.domainElement hA
  change _ ≤ 2 * (E.energyMeasureLaws.root A hA u.domainElement) ^ (p - 1) *
    E.energyMeasureLaws.root A hA v.domainElement at h
  rw [E.energyMeasureLaws.root_apply A hA v.domainElement, measureReal_def, hz,
    ENNReal.toReal_zero, Real.zero_rpow (inv_ne_zero (zero_lt_one.trans E.one_lt).ne'), mul_zero] at h
  exact (ENNReal.toReal_eq_zero_iff _).mp (le_antisymm h ENNReal.toReal_nonneg)
    |>.resolve_right (measure_ne_top _ _)

theorem energyDerivativeMeasure_variation_le_of_local_root (u v : E.CompactCore)
    {A : Set X} (hA : MeasurableSet A) {K : ℝ} (hK : 0 ≤ K)
    (h : E.energyMeasureRoot A hA v.domainElement ≤ K * E.energyMeasureRoot A hA u.domainElement) :
    (E.energyDerivativeMeasure u.domainElement v.domainElement).totalVariation A ≤
      ENNReal.ofReal (2 * K) * E.energyMeasure u.domainElement A := by
  let ν := E.energyDerivativeMeasure u.domainElement v.domainElement
  let a := E.energyMeasureRoot A hA u.domainElement
  have h₀ : 0 ≤ a := apply_nonneg _ _
  have hMass : a ^ p = (E.energyMeasure u.domainElement A).toReal :=
    (E.energyMeasure_real_eq u.domainElement hA).symm
  have hb := (E.energyDerivativeMeasure_variation_le u.domainElement v.domainElement hA).trans
    (mul_le_mul_of_nonneg_left h (mul_nonneg (by norm_num) (Real.rpow_nonneg h₀ _)))
  change (ν.totalVariation A).toReal ≤ 2 * a ^ (p - 1) * (K * a) at hb
  have he : 2 * a ^ (p - 1) * (K * a) = (2 * K) * a ^ p := by
    have he' : a ^ (p - 1) * a = a ^ p := by
      conv_lhs => arg 2; rw [← Real.rpow_one a]
      rw [← Real.rpow_add' h₀, sub_add_cancel]
      linarith only [E.one_lt]
    rw [← he']
    ring
  rw [he, hMass] at hb
  have hle := ENNReal.ofReal_le_ofReal hb
  rwa [ENNReal.ofReal_toReal (measure_ne_top _ _), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_toReal (measure_ne_top _ _)] at hle

end PEnergy.CompactCore

end WalkDimensions
