import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-!
# Measure bounds from the capacitary pushforward identity

The consequences (3.7) and (3.8) in arXiv:2611.02422v1.
-/

open MeasureTheory Metric Set
open scoped ENNReal NNReal

namespace WalkDimensions

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {ν : Measure X} {u : X → ℝ} {K : ℝ≥0} {M : ℝ≥0∞}

/-- The pushforward identity bounds the energy measure of every metric
ball by the length of an interval containing its image. -/
theorem measure_ball_le_of_holder_and_map_eq_smul_volume {c H : ℝ}
    (hc : 0 ≤ c) (hH : 0 ≤ H) (hu : Continuous u)
    (hHolder : ∀ y z, |u y - u z| ≤ H * dist y z ^ c)
    (hmap : ν.map u = M • volume.restrict (Icc (0 : ℝ) 1)) (x : X) (r : ℝ) :
    ν (ball x r) ≤ M * ENNReal.ofReal (2 * H * r ^ c) := by
  let a : ℝ := H * r ^ c
  let J := Icc (u x - a) (u x + a)
  have hsub : ball x r ⊆ u ⁻¹' J := by
    intro y hy
    have hxy := (hHolder y x).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow dist_nonneg (mem_ball.mp hy).le hc) hH)
    have h := abs_le.mp hxy
    change u x - a ≤ u y ∧ u y ≤ u x + a
    exact ⟨by linarith only [h.1], by linarith only [h.2]⟩
  calc
    _ ≤ ν (u ⁻¹' J) := measure_mono hsub
    _ = (ν.map u) J := (Measure.map_apply hu.measurable measurableSet_Icc).symm
    _ ≤ M * volume J := by
      rw [hmap, smul_apply, smul_eq_mul]
      exact mul_le_mul_of_nonneg_left (Measure.restrict_le_self J) bot_le
    _ = _ := by
      rw [Real.volume_Icc]
      congr 2
      dsimp only [a]
      ring

/-- The pushforward identity bounds the energy measure of every metric
ball by the length of an interval containing its image. -/
theorem measure_ball_le_of_map_eq_smul_volume (hLip : LipschitzWith K u)
    (hmap : ν.map u = M • volume.restrict (Icc (0 : ℝ) 1)) (x : X) (r : ℝ) :
    ν (ball x r) ≤ M * ENNReal.ofReal (2 * (K : ℝ) * r) := by
  let a : ℝ := (K : ℝ) * r
  let J := Icc (u x - a) (u x + a)
  have hsub : ball x r ⊆ u ⁻¹' J := by
    intro y hy
    have hxy := (lipschitzWith_iff_dist_le_mul.mp hLip y x).trans
      (mul_le_mul_of_nonneg_left (mem_ball.mp hy).le K.coe_nonneg)
    rw [Real.dist_eq] at hxy
    have h := abs_le.mp hxy
    change u x - a ≤ u y ∧ u y ≤ u x + a
    exact ⟨by linarith only [h.1], by linarith only [h.2]⟩
  calc
    _ ≤ ν (u ⁻¹' J) := measure_mono hsub
    _ = (ν.map u) J := (Measure.map_apply hLip.continuous.measurable measurableSet_Icc).symm
    _ ≤ M * volume J := by
      rw [hmap, smul_apply, smul_eq_mul]
      exact mul_le_mul_of_nonneg_left (Measure.restrict_le_self J) bot_le
    _ = _ := by
      rw [Real.volume_Icc]
      congr 2
      dsimp only [a]
      ring

/-- A Lipschitz map with the capacitary pushforward identity bounds its
source measure by one-dimensional Hausdorff measure. -/
theorem measure_le_smul_hausdorff_one_of_map_eq_smul_volume (hLip : LipschitzWith K u)
    (hmap : ν.map u = M • volume.restrict (Icc (0 : ℝ) 1)) :
    ν ≤ (M * (K : ℝ≥0∞)) • μH[1] := by
  intro S
  calc
    ν S ≤ ν.map u (u '' S) := Measure.le_map_apply_image hLip.continuous.measurable.aemeasurable S
    _ ≤ M * volume (u '' S) := by
      rw [hmap, smul_apply, smul_eq_mul]
      exact mul_le_mul_of_nonneg_left (Measure.restrict_le_self (u '' S)) bot_le
    _ ≤ M * ((K : ℝ≥0∞) * μH[1] S) := by
      apply mul_le_mul_of_nonneg_left _ bot_le
      rw [← hausdorffMeasure_real]
      simpa only [ENNReal.rpow_one] using (hLip.hausdorffMeasure_image_le (d := 1) zero_le_one S)
    _ = _ := by rw [smul_apply, smul_eq_mul, mul_assoc]

/-- A Hölder potential with the interval pushforward bounds its measure by
Hausdorff measure at the Hölder exponent. -/
theorem measure_le_smul_hausdorff_of_map_eq_smul_volume {c : ℝ≥0}
    (hc : 0 < c) (hH : HolderWith K c u)
    (hmap : ν.map u = M • volume.restrict (Icc (0 : ℝ) 1)) :
    ν ≤ (M * (K : ℝ≥0∞)) • μH[(c : ℝ)] := by
  intro S
  have hu := hH.continuous hc
  calc
    ν S ≤ ν.map u (u '' S) := Measure.le_map_apply_image hu.measurable.aemeasurable S
    _ ≤ M * volume (u '' S) := by
      rw [hmap, smul_apply, smul_eq_mul]
      exact mul_le_mul_of_nonneg_left (Measure.restrict_le_self (u '' S)) bot_le
    _ ≤ M * ((K : ℝ≥0∞) * μH[(c : ℝ)] S) := by
      apply mul_le_mul_of_nonneg_left _ bot_le
      rw [← hausdorffMeasure_real]
      simpa only [ENNReal.rpow_one, mul_one] using
        (hH.holderOnWith (s := S)).hausdorffMeasure_image_le (by exact_mod_cast hc)
          (d := 1) zero_le_one
    _ = _ := by rw [smul_apply, smul_eq_mul, mul_assoc]

end WalkDimensions
