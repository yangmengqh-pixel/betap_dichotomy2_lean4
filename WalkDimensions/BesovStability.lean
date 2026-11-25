import WalkDimensions.LargeScale

/-!
# Stability of the Besov increment bounds at a fixed scale
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal

namespace WalkDimensions

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {m : Measure X} [SFinite m] [SecondCountableTopology X]

theorem besovEnergy_sub_le_local {p β r : ℝ} (hp : 0 ≤ p)
    {u v : X → ℝ} (hu : Measurable u) (U : Set X) :
    besovEnergy m p β U (u - v) r ≤ (2 : ℝ≥0∞) ^ p *
      (besovEnergy m p β U u r + besovEnergy m p β U v r) := by
  let C := (2 : ℝ≥0∞) ^ p
  have hC : C ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hp (by norm_num)
  have hstep (x : X) : ballMoment m p (u - v) r x ≤ C *
      (ballMoment m p u r x + ballMoment m p v r x) := by
    have hmeas (w : X → ℝ) (hw : Measurable w) :
        Measurable (fun y ↦ ENNReal.ofReal |w x - w y| ^ p) :=
      ((continuous_abs.measurable.comp (measurable_const.sub hw)).ennreal_ofReal).pow_const _
    unfold ballMoment
    rw [← lintegral_add_left (hmeas u hu), ← lintegral_const_mul' _ _ hC]
    apply lintegral_mono
    intro y
    change ENNReal.ofReal |u x - v x - (u y - v y)| ^ p ≤ _
    rw [show u x - v x - (u y - v y) =
      u x - u y - (v x - v y) by ring]
    exact ennreal_abs_sub_rpow_le _ _ hp
  unfold besovEnergy
  have h := lintegral_mono (μ := m.restrict U) hstep
  rw [lintegral_const_mul' _ _ hC, lintegral_add_left (measurable_ballMoment hu p r)] at h
  exact (mul_le_mul_of_nonneg_left h bot_le).trans_eq (by rw [← mul_add, mul_left_comm])

theorem besovEnergy_sub_le {p β r : ℝ} (hp : 0 ≤ p)
    {u v : X → ℝ} (hu : Measurable u) :
    besovEnergy m p β univ (u - v) r ≤ (2 : ℝ≥0∞) ^ p *
      (besovEnergy m p β univ u r + besovEnergy m p β univ v r) :=
  besovEnergy_sub_le_local hp hu univ

omit [MetricSpace X] [BorelSpace X] [SFinite m] [SecondCountableTopology X] in
theorem eLpNorm_rpow_eq_lintegral_abs {p : ℝ} (hp : 0 < p)
    {u : X → ℝ} (hu : AEStronglyMeasurable u m) :
    (eLpNorm u (ENNReal.ofReal p) m) ^ p = ∫⁻ x, ENNReal.ofReal |u x| ^ p ∂m := by
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (ENNReal.ofReal_ne_zero_iff.mpr hp)
    ENNReal.ofReal_ne_top hu, ENNReal.toReal_ofReal hp.le, one_div, ← ENNReal.rpow_mul,
    inv_mul_cancel₀ hp.ne', ENNReal.rpow_one]
  simp only [Real.eNorm_eq_ofReal_abs]

theorem besovEnergy_le_eLpNorm_of_doubling [ProperSpace X] [IsFiniteMeasureOnCompacts m]
    [m.IsOpenPosMeasure] {p β r : ℝ} (hp : 0 < p) (hr : 0 < r) {D : ℝ≥0∞}
    (hD : ∀ x r, 0 < r → m (ball x (2 * r)) ≤ D * m (ball x r))
    {u : X → ℝ} (hu : Measurable u) :
    besovEnergy m p β univ u r ≤
      ((ENNReal.ofReal r) ^ (-β) * ((2 : ℝ≥0∞) ^ p * (1 + D))) *
        (eLpNorm u (ENNReal.ofReal p) m) ^ p := by
  have h := besovEnergy_zero_scale_le_of_doubling hp.le hr hD hu
  simp only [besovEnergy, neg_zero, ENNReal.rpow_zero, one_mul] at h
  rw [besovEnergy, eLpNorm_rpow_eq_lintegral_abs hp hu.aestronglyMeasurable, mul_assoc]
  exact mul_le_mul_of_nonneg_left h bot_le

end WalkDimensions
