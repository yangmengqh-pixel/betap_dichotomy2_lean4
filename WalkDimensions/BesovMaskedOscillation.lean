import WalkDimensions.LargeScale
import WalkDimensions.OscillatoryTruncation

/-!
# Increment bounds for a masked oscillation
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal

namespace WalkDimensions

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] {m : Measure X} [SFinite m]

theorem besovEnergy_masked_sawtooth_le {p β r s : ℝ} (hp : 0 < p) (hr : 0 < r)
    {f ξ : X → ℝ} (hf : Measurable f)
    (hRange : ∀ x, ξ x ∈ Icc (0 : ℝ) 1) {U : Set X} (hU : MeasurableSet U)
    (hSupp : support ξ ⊆ U) :
    besovEnergy m p β univ (fun x ↦ ξ x * sawtooth r (f x)) s ≤
      (2 : ℝ≥0∞) ^ p * (besovEnergy m p β U f s +
        (ENNReal.ofReal r) ^ p * besovEnergy m p β univ ξ s) := by
  let C := (2 : ℝ≥0∞) ^ p
  let R := (ENNReal.ofReal r) ^ p
  have hC : C ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hp.le (by norm_num)
  have hR : R ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.ofReal_ne_top
  let w (x : X) := sawtooth r (f x)
  let h (x : X) := ξ x * w x
  have hpt (x y : X) : ENNReal.ofReal |h x - h y| ^ p ≤
      C * (U.indicator (fun x ↦ ENNReal.ofReal |f x - f y| ^ p) x +
        R * ENNReal.ofReal |ξ x - ξ y| ^ p) := by
    have hdist := lipschitzWith_iff_dist_le_mul.mp (lipschitzWith_sawtooth r) (f x) (f y)
    have hinc : |w x - w y| ≤ |f x - f y| := by
      simpa only [w, Real.dist_eq, NNReal.coe_one, one_mul] using hdist
    have h1 : ENNReal.ofReal |ξ x * (w x - w y)| ^ p ≤
        U.indicator (fun x ↦ ENNReal.ofReal |f x - f y| ^ p) x := by
      by_cases hx : x ∈ U
      · rw [indicator_of_mem hx, abs_mul, abs_of_nonneg (hRange x).1]
        apply ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal _) hp.le
        exact (mul_le_of_le_one_left (abs_nonneg _) (hRange x).2).trans hinc
      · have he : ξ x = 0 := notMem_support.mp (fun h ↦ hx (hSupp h))
        rw [he, zero_mul, abs_zero, ENNReal.ofReal_zero, indicator_of_notMem hx]
        rw [ENNReal.zero_rpow_of_pos hp]
    have h2 : ENNReal.ofReal |w y * (ξ x - ξ y)| ^ p ≤
        R * ENNReal.ofReal |ξ x - ξ y| ^ p := by
      have hw : 0 ≤ w y := sawtooth_nonneg _ _
      rw [abs_mul, abs_of_nonneg hw, ENNReal.ofReal_mul hw, ENNReal.mul_rpow_of_nonneg _ _ hp.le]
      exact mul_le_mul_of_nonneg_right
        (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (sawtooth_le hr _)) hp.le) bot_le
    have he : h x - h y = ξ x * (w x - w y) - -(w y * (ξ x - ξ y)) := by
      dsimp only [h]
      ring
    rw [he]
    have ht := ennreal_abs_sub_rpow_le (ξ x * (w x - w y)) (-(w y * (ξ x - ξ y))) hp.le
    rw [abs_neg] at ht
    exact ht.trans (mul_le_mul_of_nonneg_left (add_le_add h1 h2) bot_le)
  have hpoint (x : X) : ballMoment m p h s x ≤
      C * (U.indicator (ballMoment m p f s) x + R * ballMoment m p ξ s x) := by
    have hmeas : Measurable (fun y ↦ U.indicator (fun x ↦ ENNReal.ofReal |f x - f y| ^ p) x) := by
      by_cases hx : x ∈ U
      · simp only [indicator_of_mem hx]
        exact (((continuous_abs.measurable.comp (measurable_const.sub hf)).ennreal_ofReal).pow_const _)
      · simp only [indicator_of_notMem hx]
        exact measurable_const
    have he := lintegral_mono (μ := normalizedBall m x s) (hpt x)
    rw [lintegral_const_mul' _ _ hC, lintegral_add_left hmeas, lintegral_const_mul' _ _ hR] at he
    by_cases hx : x ∈ U
    · simpa only [ballMoment, indicator_of_mem hx] using he
    · simpa only [ballMoment, indicator_of_notMem hx, lintegral_zero] using he
  have hmF := (measurable_ballMoment (m := m) hf p s).indicator hU
  have hle := lintegral_mono (μ := m) hpoint
  rw [lintegral_const_mul' _ _ hC, lintegral_add_left hmF, lintegral_indicator hU,
    lintegral_const_mul' _ _ hR] at hle
  unfold besovEnergy
  simp only [Measure.restrict_univ]
  exact (mul_le_mul_of_nonneg_left hle bot_le).trans_eq (by rw [mul_left_comm, mul_add, mul_left_comm])

end WalkDimensions
