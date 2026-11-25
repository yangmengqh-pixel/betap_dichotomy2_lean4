import WalkDimensions.PotentialHausdorffCutoffs
import WalkDimensions.ClippedCutoffPartition
import WalkDimensions.DoublingCovers

/-!
# Uniform density and energy estimates for a finite covering by cutoffs
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SecondCountableTopology X] {m : Measure X}
  [IsFiniteMeasureOnCompacts m] [m.IsOpenPosMeasure] {p : ℝ} {E : PEnergy m p}

omit [SecondCountableTopology X] [m.IsOpenPosMeasure] in
theorem energyMeasureRoot_le_of_apply_le_mul (f g : E.domain) {S : Set X}
    (hS : MeasurableSet S) {a : ℝ} (ha : 0 ≤ a)
    (h : E.energyMeasure f S ≤ ENNReal.ofReal a * E.energyMeasure g S) :
    E.energyMeasureRoot S hS f ≤ a ^ p⁻¹ * E.energyMeasureRoot S hS g := by
  change E.energyMeasureLaws.root S hS f ≤ a ^ p⁻¹ * E.energyMeasureLaws.root S hS g
  rw [E.energyMeasureLaws.root_apply, E.energyMeasureLaws.root_apply, measureReal_def, measureReal_def]
  have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal ha] at hh
  exact (Real.rpow_le_rpow ENNReal.toReal_nonneg hh (inv_nonneg.mpr (zero_lt_one.trans E.one_lt).le)).trans_eq
    (Real.mul_rpow ha ENNReal.toReal_nonneg)

omit [ProperSpace X] [SecondCountableTopology X] [m.IsOpenPosMeasure] in
theorem rootSeminorm_le_of_energy_le_rpow (f : E.domain)
    {c K r : ℝ} (hK : 0 ≤ K) (hr : 0 < r)
    (h : (E.energy f : ℝ) ≤ K * r ^ (-(p - 1) * c)) :
    E.rootSeminorm f ≤ K ^ p⁻¹ * r ^ (-((p - 1) / p) * c) := by
  rw [E.rootSeminorm_apply]
  have hp := zero_lt_one.trans E.one_lt
  apply (Real.rpow_le_rpow (NNReal.coe_nonneg _) h (inv_nonneg.mpr hp.le)).trans_eq
  rw [Real.mul_rpow hK (Real.rpow_nonneg hr.le _), ← Real.rpow_mul hr.le]
  congr 2
  rw [div_eq_mul_inv]
  ring

omit [SecondCountableTopology X] [m.IsOpenPosMeasure] in
theorem energyMeasureRoot_le_of_hausdorff_bound (u f : E.domain) {W S : Set X} {c J s : ℝ}
    {K : ℝ≥0∞} (hK : K ≠ ∞) (hJ : 0 ≤ J) (hs : 0 < s) (hS : MeasurableSet S)
    (hSW : S ⊆ W) (hmass : ∀ T ⊆ W, μH[c] T ≤ K * E.energyMeasure u T)
    (hf : E.energyMeasure f ≤ ENNReal.ofReal (J * s ^ (-p * c)) • μH[c]) :
    E.energyMeasureRoot S hS f ≤ (J * K.toReal) ^ p⁻¹ * s ^ (-c) *
      E.energyMeasureRoot S hS u := by
  let k := J * K.toReal
  have hk : 0 ≤ k := mul_nonneg hJ ENNReal.toReal_nonneg
  have hf' : E.energyMeasure f S ≤ ENNReal.ofReal (k * s ^ (-p * c)) * E.energyMeasure u S := by
    calc
      _ ≤ ENNReal.ofReal (J * s ^ (-p * c)) * μH[c] S := hf S
      _ ≤ ENNReal.ofReal (J * s ^ (-p * c)) * (K * E.energyMeasure u S) :=
        mul_le_mul_of_nonneg_left (hmass S hSW) bot_le
      _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_toReal hK, ← ENNReal.ofReal_mul (by positivity)]
        have he : J * s ^ (-p * c) * K.toReal = k * s ^ (-p * c) := by dsimp only [k]; ring
        rw [he]
  apply (E.energyMeasureRoot_le_of_apply_le_mul _ _ hS (mul_nonneg hk (Real.rpow_nonneg hs.le _)) hf').trans_eq
  rw [Real.mul_rpow hk (Real.rpow_nonneg hs.le _), ← Real.rpow_mul hs.le]
  have hp := zero_lt_one.trans E.one_lt
  congr 3
  rw [neg_mul, mul_comm p, neg_mul, mul_assoc, mul_inv_cancel₀ hp.ne', mul_one]

end WalkDimensions.PEnergy
