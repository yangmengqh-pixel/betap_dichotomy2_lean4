import WalkDimensions.TransportMassBounds

/-!
# The local and complement variation estimates after rescaling
-/

open Filter Function MeasureTheory Set
open scoped ENNReal

namespace WalkDimensions.PEnergy.CompactCore

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [LocallyCompactSpace X] {m : Measure X} [IsFiniteMeasureOnCompacts m]
  {p : ℝ} {E : PEnergy m p}

theorem energyDerivativeMeasure_variation_real_le_of_local_root (u v : E.CompactCore)
    {S : Set X} (hS : MeasurableSet S) {K : ℝ} (hK : 0 ≤ K)
    (h : E.energyMeasureRoot S hS v.domainElement ≤ K * E.energyMeasureRoot S hS u.domainElement) :
    ((E.energyDerivativeMeasure u.domainElement v.domainElement).totalVariation S).toReal ≤
      (2 * K) * (E.energyMeasure u.domainElement S).toReal := by
  have he := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
    (u.energyDerivativeMeasure_variation_le_of_local_root v hS hK h)
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at he

theorem energyDerivativeMeasure_variation_le_of_scaled_compl (u v : E.CompactCore)
    {S : Set X} (hS : MeasurableSet S) {r τ c b L : ℝ}
    (hr : 0 < r) (hτ : 0 < τ) (hb : 0 ≤ b) (hL : 0 ≤ L)
    (hMass : (E.energyMeasure u.domainElement S).toReal ≤ b * r ^ c)
    (hRoot : E.rootSeminorm v.domainElement ≤ L * (τ * r) ^ (-((p - 1) / p) * c)) :
    ((E.energyDerivativeMeasure u.domainElement v.domainElement).totalVariation S).toReal ≤
      2 * L * b ^ ((p - 1) / p) * τ ^ (-((p - 1) / p) * c) := by
  let a := (p - 1) / p
  have ha : 0 ≤ a := div_nonneg (sub_nonneg.mpr E.one_lt.le) (zero_lt_one.trans E.one_lt).le
  have hF := Real.rpow_le_rpow ENNReal.toReal_nonneg hMass ha
  have hG := mul_le_mul (mul_le_mul_of_nonneg_left hF (show 0 ≤ (2 : ℝ) by norm_num)) hRoot
    (apply_nonneg _ _) (mul_nonneg (by norm_num) (Real.rpow_nonneg (by positivity) _))
  refine (u.energyDerivativeMeasure_variation_le_global_root v hS).trans (hG.trans_eq ?_)
  change 2 * (b * r ^ c) ^ a * (L * (τ * r) ^ (-a * c)) =
    2 * L * b ^ a * τ ^ (-a * c)
  rw [Real.mul_rpow hb (Real.rpow_nonneg hr.le _), ← Real.rpow_mul hr.le,
    Real.mul_rpow hτ.le hr.le, show c * a = a * c by ring, neg_mul]
  have hcancel : r ^ (a * c) * r ^ (-(a * c)) = 1 := by
    rw [← Real.rpow_add hr, add_neg_cancel, Real.rpow_zero]
  calc
    _ = (2 * L * b ^ a * τ ^ (-(a * c))) * (r ^ (a * c) * r ^ (-(a * c))) := by ring
    _ = _ := by rw [hcancel, mul_one]

end WalkDimensions.PEnergy.CompactCore
