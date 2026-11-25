import WalkDimensions.EnergyDerivativeClip
import WalkDimensions.TransportMassBounds

/-!
# A bounded perturbation captures energy on its unclipped values
-/

open Filter Function MeasureTheory Set
open scoped ENNReal

namespace WalkDimensions.PEnergy.CompactCore

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [LocallyCompactSpace X] {m : Measure X} [IsFiniteMeasureOnCompacts m] {p : ℝ} {E : PEnergy m p}

private theorem weightSignedMeasure_apply_univ_eq_of_support (ν : SignedMeasure X)
    {u : X → ℝ} (hu : ν.Integrable u) {B : Set X} (hB : MeasurableSet B)
    (hSupp : support u ⊆ B) : weightSignedMeasure ν u univ = weightSignedMeasure ν u B := by
  have hz := weightSignedMeasure_apply_eq_zero_of_forall ν hu hB.compl
    (fun _ hx ↦ notMem_support.mp (fun h ↦ hx (hSupp h)))
  have he := VectorMeasure.of_union (v := weightSignedMeasure ν u)
    (disjoint_compl_right (a := B)) hB hB.compl
  rwa [union_compl_self, hz, add_zero] at he

theorem measure_band_le_of_clipped_variation (f v χ : E.CompactCore)
    {B U : Set X} (hB : MeasurableSet B) (hU : MeasurableSet U) (hUB : U ⊆ B)
    (hχ : ∀ x, 0 ≤ χ.toFun x) (hχ₁ : EqOn χ.toFun (fun _ ↦ 1) U)
    (hSupp : support χ.toFun ⊆ B)
    {c a : ℝ} (ha : 0 ≤ a) (hv : EqOn v.toFun (fun x ↦ f.toFun x - c) B) :
    let S := {x | |f.toFun x - c| ≤ a}
    let d := v.clip ha
    (E.energyMeasure f.domainElement (U ∩ S)).toReal ≤
      |E.energyDerivativeMeasure f.domainElement (χ.mul d).domainElement univ| +
        a * ((E.energyDerivativeMeasure f.domainElement χ.domainElement).totalVariation B).toReal := by
  let S := {x | |f.toFun x - c| ≤ a}
  let d := v.clip ha
  let ν := (E.energyMeasure f.domainElement).restrict (B ∩ S)
  let D (g : E.CompactCore) := E.energyDerivativeMeasure f.domainElement g.domainElement
  have hS : MeasurableSet S :=
    (isClosed_le (f.continuous.sub continuous_const).abs continuous_const).measurableSet
  have hBS := hB.inter hS
  have hD := energyDerivativeMeasure_restrict_clip f v hB ha hv
  change (D d).restrict B = ν.toSignedMeasure at hD
  have hI : (D d).Integrable χ.toFun := χ.integrable_vectorMeasure _
  have hEqu : weightSignedMeasure (D d) χ.toFun univ = ∫ x in B, χ.toFun x ∂ν := by
    rw [weightSignedMeasure_apply_univ_eq_of_support _ hI hB hSupp]
    have he := VectorMeasure.restrict_withDensity
      (B := ContinuousLinearMap.lsmul ℝ ℝ) (s := B) hI
    change (weightSignedMeasure (D d) χ.toFun).restrict B =
      weightSignedMeasure ((D d).restrict B) χ.toFun at he
    have he' := congrArg (fun η : SignedMeasure X ↦ η B) he
    change ((weightSignedMeasure (D d) χ.toFun).restrict B) B =
      weightSignedMeasure ((D d).restrict B) χ.toFun B at he'
    rw [VectorMeasure.restrict_apply _ hB hB, inter_self, hD,
      weightSignedMeasure_of_toSignedMeasure_apply _ (χ.integrable_vectorMeasure _) hB] at he'
    exact he'
  have hLower : (E.energyMeasure f.domainElement (U ∩ S)).toReal ≤ ∫ x in B, χ.toFun x ∂ν := by
    let k : X → ℝ := U.indicator (1 : X → ℝ)
    have hInt : Integrable χ.toFun (ν.restrict B) := by
      obtain ⟨K, hK⟩ := χ.continuous.bounded_above_of_compact_support χ.compactSupport
      exact Integrable.of_bound χ.continuous.aestronglyMeasurable K (Eventually.of_forall hK)
    have hkInt : Integrable k (ν.restrict B) := (integrable_const _).indicator hU
    have hk (x : X) : k x ≤ χ.toFun x := by
      by_cases h : x ∈ U
      · rw [show k x = 1 from indicator_of_mem h _, hχ₁ h]
      · rw [show k x = 0 from indicator_of_notMem h _]
        exact hχ x
    have hh := integral_mono hkInt hInt hk
    change (∫ x, U.indicator (1 : X → ℝ) x ∂ν.restrict B) ≤ _ at hh
    rw [integral_indicator_one hU, measureReal_def, Measure.restrict_apply hU,
      inter_eq_left.mpr hUB] at hh
    dsimp only [ν] at hh
    rwa [Measure.restrict_apply hU, ← inter_assoc, inter_eq_left.mpr hUB] at hh
  have hDχ : (D χ).totalVariation (univ \ B) = 0 :=
    f.energyDerivativeMeasure_variation_zero_of_const_on χ (MeasurableSet.univ.diff hB)
      (fun x hx ↦ notMem_support.mp (fun h ↦ hx.2 (hSupp h)))
  have hSecond : |weightSignedMeasure (D χ) d.toFun univ| ≤ a * ((D χ).totalVariation B).toReal := by
    rw [weightSignedMeasure_apply_inter_of_variation _ (d.integrable_vectorMeasure _) MeasurableSet.univ
      hB hDχ, univ_inter]
    exact abs_weightSignedMeasure_apply_le _ (d.integrable_vectorMeasure _) hB
      (fun x _ ↦ abs_symmetricClip_le ha (v.toFun x))
  have hProd := congrArg (fun η : SignedMeasure X ↦ η univ) (f.energyDerivativeMeasure_mul χ d)
  change D (χ.mul d) univ = _ at hProd
  rw [FunLike.coe_add, Pi.add_apply] at hProd
  rw [← hEqu] at hLower
  change _ ≤ |D (χ.mul d) univ| + a * ((D χ).totalVariation B).toReal
  have he : weightSignedMeasure (D d) χ.toFun univ =
      D (χ.mul d) univ - weightSignedMeasure (D χ) d.toFun univ := by linarith only [hProd]
  apply hLower.trans
  rw [he]
  exact (le_abs_self _).trans ((abs_sub _ _).trans (add_le_add_right hSecond _))

end WalkDimensions.PEnergy.CompactCore
