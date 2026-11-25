import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure

/-!
# Bounded scalar weights for signed measures
-/

open Filter Function MeasureTheory Set
open scoped ENNReal Topology

namespace WalkDimensions

variable {X : Type*} [MeasurableSpace X]

noncomputable def weightSignedMeasure (ν : SignedMeasure X) (u : X → ℝ) : SignedMeasure X :=
  ν.withDensity u (ContinuousLinearMap.lsmul ℝ ℝ)

theorem integrable_vectorMeasure_of_bounded (ν : SignedMeasure X) {u : X → ℝ}
    (hu : Measurable u) {K : ℝ} (hK : ∀ x, |u x| ≤ K) : ν.Integrable u := by
  have : IsFiniteMeasure ν.variation := by
    rw [← ν.totalVariation_eq_variation]
    infer_instance
  apply Integrable.of_bound hu.aestronglyMeasurable K
  exact Eventually.of_forall fun x ↦ by simpa only [Real.norm_eq_abs] using hK x

theorem weightSignedMeasure_sub (ν : SignedMeasure X) {u v : X → ℝ}
    (hu : ν.Integrable u) (hv : ν.Integrable v) :
    weightSignedMeasure ν (u - v) = weightSignedMeasure ν u - weightSignedMeasure ν v := by
  ext A hA
  simp only [weightSignedMeasure, VectorMeasure.withDensity_apply (hu.sub hv),
    VectorMeasure.withDensity_apply hu, VectorMeasure.withDensity_apply hv,
    sub_apply]
  exact VectorMeasure.integral_sub hu.restrict hv.restrict

theorem weightSignedMeasure_add (ν : SignedMeasure X) {u v : X → ℝ}
    (hu : ν.Integrable u) (hv : ν.Integrable v) :
    weightSignedMeasure ν (u + v) = weightSignedMeasure ν u + weightSignedMeasure ν v := by
  ext A hA
  simp only [weightSignedMeasure, VectorMeasure.withDensity_apply (hu.add hv),
    VectorMeasure.withDensity_apply hu, VectorMeasure.withDensity_apply hv,
    FunLike.coe_add, Pi.add_apply]
  exact VectorMeasure.integral_add hu.restrict hv.restrict

theorem weightSignedMeasure_apply_const (ν : SignedMeasure X) (c : ℝ) {A : Set X}
    (_hA : MeasurableSet A) : weightSignedMeasure ν (fun _ ↦ c) A = c * ν A := by
  have : IsFiniteMeasure ν.variation := by
    rw [← ν.totalVariation_eq_variation]
    infer_instance
  have hI : ν.Integrable (fun _ ↦ c) := integrable_const _
  rw [weightSignedMeasure, VectorMeasure.withDensity_apply hI, VectorMeasure.setIntegral_const]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]

theorem abs_weightSignedMeasure_apply_le (ν : SignedMeasure X) {u : X → ℝ}
    (hu : ν.Integrable u) {A : Set X} (hA : MeasurableSet A) {C : ℝ}
    (hC : ∀ x ∈ A, |u x| ≤ C) :
    |weightSignedMeasure ν u A| ≤ C * (ν.totalVariation A).toReal := by
  have : IsFiniteMeasure ν.variation := by
    rw [← ν.totalVariation_eq_variation]
    infer_instance
  have : IsFiniteMeasure (ν.restrict A).variation := by
    rw [VectorMeasure.variation_restrict hA]
    infer_instance
  have hBound : ∀ᵐ x ∂(ν.restrict A).variation, ‖u x‖ ≤ C := by
    rw [VectorMeasure.variation_restrict hA]
    filter_upwards [ae_restrict_mem hA] with x hx
    simpa only [Real.norm_eq_abs] using hC x hx
  have h := VectorMeasure.norm_integral_le_of_norm_le_const
    (B := ContinuousLinearMap.lsmul ℝ ℝ) hBound
  rw [weightSignedMeasure, VectorMeasure.withDensity_apply hu]
  rw [Real.norm_eq_abs, VectorMeasure.variation_restrict hA,
    measureReal_def, Measure.restrict_apply_univ, ← ν.totalVariation_eq_variation] at h
  rw [ContinuousLinearMap.opNorm_lsmul ℝ (E := ℝ) ℝ, mul_one] at h
  exact h

theorem weightSignedMeasure_add_measure {ν η : SignedMeasure X} {u : X → ℝ}
    (hν : ν.Integrable u) (hη : η.Integrable u) :
    weightSignedMeasure (ν + η) u = weightSignedMeasure ν u + weightSignedMeasure η u := by
  ext A hA
  simp only [weightSignedMeasure, VectorMeasure.withDensity_apply (hν.add_vectorMeasure hη),
    VectorMeasure.withDensity_apply hν, VectorMeasure.withDensity_apply hη,
    FunLike.coe_add, Pi.add_apply]
  rw [VectorMeasure.restrict_add, VectorMeasure.integral_add_vectorMeasure hν.restrict hη.restrict]

theorem weightSignedMeasure_smul (ν : SignedMeasure X) {u : X → ℝ}
    (hu : ν.Integrable u) (a : ℝ) :
    weightSignedMeasure ν (a • u) = a • weightSignedMeasure ν u := by
  ext A hA
  simp only [weightSignedMeasure, VectorMeasure.withDensity_apply (hu.smul a),
    VectorMeasure.withDensity_apply hu, smul_apply, VectorMeasure.integral_smul]

theorem weightSignedMeasure_congr_on (ν : SignedMeasure X) {u v : X → ℝ}
    (hu : ν.Integrable u) (hv : ν.Integrable v) {A : Set X} (hA : MeasurableSet A)
    (he : EqOn u v A) : weightSignedMeasure ν u A = weightSignedMeasure ν v A := by
  simp only [weightSignedMeasure, VectorMeasure.withDensity_apply hu,
    VectorMeasure.withDensity_apply hv]
  apply VectorMeasure.integral_congr_ae
  rw [VectorMeasure.variation_restrict hA]
  exact (ae_restrict_mem hA).mono he

theorem abs_weightSignedMeasure_apply_le_lintegral (ν : SignedMeasure X) {u : X → ℝ}
    (hu : ν.Integrable u) {A : Set X} :
    ENNReal.ofReal |weightSignedMeasure ν u A| ≤
      ∫⁻ x in A, ENNReal.ofReal |u x| ∂ν.totalVariation := by
  have h := VectorMeasure.eNorm_setIntegral_le_lintegral_eNorm
    (μ := ν) (s := A) (f := u) (B := ContinuousLinearMap.lsmul ℝ ℝ)
  have hb : ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)‖ₑ = 1 := by
    rw [← ofReal_norm, ContinuousLinearMap.opNorm_lsmul ℝ (E := ℝ) ℝ, ENNReal.ofReal_one]
  rw [← ν.totalVariation_eq_variation, hb, one_mul] at h
  simpa only [Real.eNorm_eq_ofReal_abs, weightSignedMeasure,
    VectorMeasure.withDensity_apply hu] using h

theorem abs_signedMeasure_sub_apply_le_of_cover (ν η : SignedMeasure X) (μ : Measure X)
    [IsFiniteMeasure μ] {B : ℕ → Set X} (hB : ∀ i, MeasurableSet (B i)) (hCover : ⋃ i, B i = univ)
    {C : ℝ} (hC : 0 ≤ C)
    (hLocal : ∀ i (A : Set X), MeasurableSet A → A ⊆ B i →
      |ν A - η A| ≤ C * (μ A).toReal)
    {A : Set X} (hA : MeasurableSet A) :
    |ν A - η A| ≤ C * (μ A).toReal := by
  let S (i : ℕ) := A ∩ disjointed B i
  have hS (i : ℕ) : MeasurableSet (S i) := hA.inter (MeasurableSet.disjointed hB i)
  have hd : Pairwise (Disjoint on S) := fun i j hij ↦
    (disjoint_disjointed B hij).mono inter_subset_right inter_subset_right
  have hU : (⋃ i, S i) = A := by
    simp only [S, ← inter_iUnion, iUnion_disjointed, hCover, inter_univ]
  have htv := (ν.m_iUnion hS hd).sub (η.m_iUnion hS hd)
  rw [hU] at htv
  have hlim : Tendsto (fun t : Finset ℕ ↦ |∑ i ∈ t, (ν (S i) - η (S i))|)
      atTop (𝓝 |ν A - η A|) := htv.abs
  apply le_of_tendsto hlim
  refine Eventually.of_forall fun t ↦ ?_
  calc
    _ ≤ ∑ i ∈ t, |ν (S i) - η (S i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ t, C * (μ (S i)).toReal := Finset.sum_le_sum fun i _ ↦
      hLocal i (S i) (hS i) (inter_subset_right.trans (disjointed_subset B i))
    _ = C * (μ (⋃ i ∈ t, S i)).toReal := by
      rw [← Finset.mul_sum, measure_biUnion_finset (fun _ _ _ _ hh ↦ hd hh) (fun i _ ↦ hS i),
        ENNReal.toReal_sum (fun _ _ ↦ measure_ne_top _ _)]
    _ ≤ _ := mul_le_mul_of_nonneg_left (ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono (iUnion₂_subset fun _ _ ↦ inter_subset_left))) hC

end WalkDimensions
