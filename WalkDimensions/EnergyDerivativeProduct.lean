import WalkDimensions.EnergyDerivativeSquare

/-!
# The Leibniz rule for the signed energy measure on the compact core
-/

open Filter Function MeasureTheory Set
open scoped ENNReal

namespace WalkDimensions.PEnergy.CompactCore

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {p : ℝ} {E : PEnergy μ p}

omit [LocallyCompactSpace X] in
theorem integrable_vectorMeasure (v : E.CompactCore) (ν : SignedMeasure X) : ν.Integrable v.toFun := by
  obtain ⟨K, hK⟩ := v.continuous.bounded_above_of_compact_support v.compactSupport
  exact integrable_vectorMeasure_of_bounded ν v.continuous.measurable
    (fun x ↦ by simpa only [Real.norm_eq_abs] using hK x)

theorem energyDerivativeMeasure_mul (u v w : E.CompactCore) :
    E.energyDerivativeMeasure u.domainElement (v.mul w).domainElement =
      weightSignedMeasure (E.energyDerivativeMeasure u.domainElement w.domainElement) v.toFun +
        weightSignedMeasure (E.energyDerivativeMeasure u.domainElement v.domainElement) w.toFun := by
  let D := E.energyDerivativeLinear u.domainElement
  let s := v.add w
  have hAlg : (s.mul s).domainElement =
      (v.mul v).domainElement + (w.mul w).domainElement + (2 : ℝ) • (v.mul w).domainElement := by
    change (s.mul s).domainElement =
      (((v.mul v).add (w.mul w)).add ((v.mul w).smul 2)).domainElement
    apply domainElement_eq_of_toFun_eq
    funext x
    change (s.mul s).toFun x = (v.mul v).toFun x + (w.mul w).toFun x + 2 * (v.mul w).toFun x
    simp only [mul_apply]
    change (v.toFun x + w.toFun x) * (v.toFun x + w.toFun x) = _
    ring
  have hsq (f : E.CompactCore) :
      D (f.mul f).domainElement = (2 : ℝ) • weightSignedMeasure (D f.domainElement) f.toFun := by
    change E.energyDerivativeMeasure u.domainElement (f.mul f).domainElement = _
    rw [energyDerivativeMeasure_square u f]
    exact weightSignedMeasure_smul _ (f.integrable_vectorMeasure _) 2
  have hSum : D s.domainElement = D v.domainElement + D w.domainElement := by
    change D (v.domainElement + w.domainElement) = _
    rw [map_add]
  have hWeight (ν : SignedMeasure X) :
      weightSignedMeasure ν s.toFun = weightSignedMeasure ν v.toFun +
        weightSignedMeasure ν w.toFun :=
    weightSignedMeasure_add ν (v.integrable_vectorMeasure ν) (w.integrable_vectorMeasure ν)
  have he := congrArg D hAlg
  simp only [map_add, map_smul, hsq] at he
  rw [hSum, weightSignedMeasure_add_measure (s.integrable_vectorMeasure _) (s.integrable_vectorMeasure _),
    hWeight, hWeight] at he
  ext A hA
  have heA := congrArg (fun ν : SignedMeasure X ↦ ν A) he
  simp only [smul_apply, smul_eq_mul, FunLike.coe_add, Pi.add_apply] at heA ⊢
  change D (v.mul w).domainElement A =
    weightSignedMeasure (D w.domainElement) v.toFun A +
      weightSignedMeasure (D v.domainElement) w.toFun A
  linarith only [heA]

end WalkDimensions.PEnergy.CompactCore
