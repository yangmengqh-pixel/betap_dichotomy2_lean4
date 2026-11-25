import WalkDimensions.Besov
import WalkDimensions.Doubling
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Integration over a moving ball

Tonelli's theorem for metric ball kernels and a localized comparison of their
average masses under volume doubling.
-/

open MeasureTheory Metric Set Function
open scoped ENNReal

namespace WalkDimensions

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]

private theorem measurableSet_ball_relation (r : ℝ) :
    MeasurableSet {z : X × X | dist z.2 z.1 < r} :=
  measurableSet_lt (continuous_snd.dist continuous_fst).measurable measurable_const

theorem measurable_measure_ball (m : Measure X) [SFinite m] (r : ℝ) :
    Measurable (fun x : X ↦ m (ball x r)) :=
  measurable_measure_prodMk_left (measurableSet_ball_relation r)

theorem measurable_lintegral_ball {m : Measure X} [SFinite m] (r : ℝ)
    {F : X × X → ℝ≥0∞} (hF : Measurable F) :
    Measurable (fun x ↦ ∫⁻ y in ball x r, F (x, y) ∂m) := by
  let B : Set (X × X) := {z | dist z.2 z.1 < r}
  have h := Measurable.lintegral_prod_right (f := fun x y ↦ B.indicator F (x, y))
    (ν := m) (hF.indicator (measurableSet_ball_relation r))
  convert h using 1
  ext x
  rw [← lintegral_indicator measurableSet_ball]
  apply lintegral_congr
  intro y
  rfl

theorem lintegral_lintegral_ball_swap {m ν : Measure X} [SFinite m] [SFinite ν] (r : ℝ)
    {F : X × X → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ x, ∫⁻ y in ball x r, F (x, y) ∂ν ∂m) =
      ∫⁻ y, ∫⁻ x in ball y r, F (x, y) ∂m ∂ν := by
  let B : Set (X × X) := {z | dist z.2 z.1 < r}
  have h := lintegral_lintegral_swap (μ := m) (ν := ν)
    (f := fun x y ↦ B.indicator F (x, y)) (hF.indicator (measurableSet_ball_relation r)).aemeasurable
  convert h using 1
  · apply lintegral_congr
    intro x
    rw [← lintegral_indicator measurableSet_ball]
    apply lintegral_congr
    intro y
    rfl
  · apply lintegral_congr
    intro y
    rw [← lintegral_indicator measurableSet_ball]
    apply lintegral_congr
    intro x
    by_cases hx : x ∈ ball y r
    · have hxy : (x, y) ∈ B := by simpa only [B, mem_ofPred_eq, mem_ball, dist_comm] using hx
      rw [indicator_of_mem hx, indicator_of_mem hxy]
    · have hxy : (x, y) ∉ B := by simpa only [B, mem_ofPred_eq, mem_ball, dist_comm] using hx
      rw [indicator_of_notMem hx, indicator_of_notMem hxy]

theorem lintegral_lintegral_ball_restrict_swap {m ν : Measure X} [SFinite m] [SFinite ν]
    {U : Set X} (r : ℝ) {F : X × X → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ x in U, ∫⁻ y in ball x r, F (x, y) ∂ν ∂m) =
      ∫⁻ y in thickening r U, ∫⁻ x in U ∩ ball y r, F (x, y) ∂m ∂ν := by
  rw [lintegral_lintegral_ball_swap r hF]
  simp only [Measure.restrict_restrict measurableSet_ball, inter_comm U]
  symm
  rw [← lintegral_indicator isOpen_thickening.measurableSet]
  apply lintegral_congr
  intro y
  by_cases hy : y ∈ thickening r U
  · rw [indicator_of_mem hy]
  · have he : ball y r ∩ U = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro x ⟨hx, hxU⟩
      exact hy (mem_thickening_iff.mpr ⟨x, hxU, by simpa only [dist_comm, mem_ball] using hx⟩)
    rw [indicator_of_notMem hy, he, Measure.restrict_empty, lintegral_zero_measure]

/-- Averaging the masses of enlarged balls with inverse reference-ball volume
costs only a fixed iterate of the doubling constant. -/
theorem lintegral_inv_ball_mul_measure_ball_le {m ν : Measure X} [SFinite m] [SFinite ν]
    [ProperSpace X] [IsFiniteMeasureOnCompacts m] [m.IsOpenPosMeasure]
    {D : ℝ≥0∞} (hD : ∀ (x : X) (r : ℝ), 0 < r → m (ball x (2 * r)) ≤ D * m (ball x r))
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) {n : ℕ} (hscale : 2 * t ≤ (2 : ℝ) ^ n * s)
    {U : Set X} (hU : MeasurableSet U) :
    (∫⁻ x in U, (m (ball x s))⁻¹ * ν (ball x t) ∂m) ≤ D ^ n * ν (thickening t U) := by
  have hF : Measurable (fun z : X × X ↦ (m (ball z.1 s))⁻¹) :=
    (measurable_measure_ball m s).inv.comp measurable_fst
  simp_rw [← setLIntegral_const]
  rw [lintegral_lintegral_ball_restrict_swap t hF]
  apply lintegral_mono
  intro y
  calc
    _ ≤ ∫⁻ x in U ∩ ball y t, D ^ n * (m (ball y t))⁻¹ ∂m := by
      apply setLIntegral_mono' (hU.inter measurableSet_ball)
      intro x hx
      apply inv_measure_le_mul_inv_of_le
        (measure_ball_pos m x hs).ne' (measure_ball_pos m y ht).ne'
        measure_ball_ne_top measure_ball_ne_top
      exact measure_ball_le_of_dist_le hD hs n (by
        have hxy := mem_ball.mp hx.2
        rw [dist_comm] at hxy
        linarith)
    _ ≤ ∫⁻ x in ball y t, D ^ n * (m (ball y t))⁻¹ ∂m :=
      lintegral_mono_set inter_subset_right
    _ = _ := by
      rw [setLIntegral_const, mul_assoc, ENNReal.inv_mul_cancel
        (measure_ball_pos m y ht).ne' measure_ball_ne_top, mul_one]

/-- Averaging a nonnegative function over moving balls is bounded in
integral under volume doubling. -/
theorem lintegral_normalizedBall_le_of_doubling {m : Measure X} [SFinite m]
    [ProperSpace X] [IsFiniteMeasureOnCompacts m] [m.IsOpenPosMeasure] {D : ℝ≥0∞}
    (hD : ∀ (x : X) (r : ℝ), 0 < r → m (ball x (2 * r)) ≤ D * m (ball x r))
    {r : ℝ} (hr : 0 < r) (f : X → ℝ≥0∞) :
    (∫⁻ x, ∫⁻ y, f y ∂normalizedBall m x r ∂m) ≤ D * ∫⁻ y, f y ∂m := by
  let ν := m.withDensity f
  calc
    _ = ∫⁻ x in (univ : Set X), (m (ball x r))⁻¹ * ν (ball x r) ∂m := by
      rw [Measure.restrict_univ]
      apply lintegral_congr
      intro x
      rw [normalizedBall, lintegral_smul_measure, smul_eq_mul]
      change _ = (m (ball x r))⁻¹ * m.withDensity f (ball x r)
      rw [withDensity_apply _ measurableSet_ball]
    _ ≤ D ^ 1 * ν (thickening r univ) := lintegral_inv_ball_mul_measure_ball_le
      (m := m) (ν := ν) hD hr hr (n := 1) (by rw [pow_one]) MeasurableSet.univ
    _ ≤ D * ν univ := by
      rw [pow_one]
      exact mul_le_mul_of_nonneg_left (measure_mono (subset_univ _)) bot_le
    _ = _ := by
      dsimp only [ν]
      rw [withDensity_apply f MeasurableSet.univ, Measure.restrict_univ]

end WalkDimensions
