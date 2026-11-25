import WalkDimensions.Doubling
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Integral.Average

/-!
# Lebesgue differentiation for the paper's open balls
-/

open Filter MeasureTheory Metric Set
open scoped ENNReal NNReal Topology

namespace WalkDimensions

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] {m : Measure X}

/-- Convert the open-ball doubling hypothesis to Mathlib's closed-ball form. -/
theorem VolumeDoubling.isUnifLocDoublingMeasure (h : VolumeDoubling m) :
    IsUnifLocDoublingMeasure m := by
  obtain ⟨D, hDpos, hD⟩ := h
  let d : ℝ≥0 := ⟨D, hDpos.le⟩
  have hd : ENNReal.ofReal D = (d : ℝ≥0∞) := ENNReal.ofReal_eq_coe_nnreal hDpos.le
  refine ⟨⟨d ^ 2, ?_⟩⟩
  filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi (0 : ℝ))] with r hr x
  have hr₀ : 0 < r := hr
  calc
    _ ≤ m (ball x ((2 : ℝ) ^ 2 * r)) :=
      measure_mono (closedBall_subset_ball (by nlinarith))
    _ ≤ (ENNReal.ofReal D) ^ 2 * m (ball x r) :=
      measure_ball_two_pow_le hD x hr₀ 2
    _ ≤ _ := by
      rw [hd, ENNReal.coe_pow]
      exact mul_le_mul_of_nonneg_left (measure_mono ball_subset_closedBall) bot_le

variable [BorelSpace X] [SecondCountableTopology X] [ProperSpace X]
  [IsFiniteMeasureOnCompacts m] [m.IsOpenPosMeasure]

theorem VolumeDoubling.ae_tendsto_openBall_average (h : VolumeDoubling m)
    {f : X → ℝ} (hf : LocallyIntegrable f m) :
    ∀ᵐ x ∂m, Tendsto (fun r : ℝ ↦ ⨍ y in ball x r, f y ∂m) (𝓝[>] 0) (𝓝 (f x)) := by
  have : IsUnifLocDoublingMeasure m := h.isUnifLocDoublingMeasure
  obtain ⟨D, hDpos, hD⟩ := h
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub m hf 1] with x hx
  have hx' := hx (fun _ : ℝ ↦ x) id tendsto_id (by
    filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi (0 : ℝ))] with r hr
    exact mem_closedBall_self (by simpa only [one_mul, id] using (show 0 < r from hr).le))
  change Tendsto (fun r : ℝ ↦ ⨍ y in closedBall x r, ‖f y - f x‖ ∂m) (𝓝[>] 0) (𝓝 0) at hx'
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hdom : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
      dist (⨍ y in ball x r, f y ∂m) (f x) ≤ D * (⨍ y in closedBall x r, ‖f y - f x‖ ∂m) := by
    filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi (0 : ℝ))] with r hr
    have hr₀ : 0 < r := hr
    let B := ball x r
    let C := closedBall x r
    have hBfin : m B ≠ ∞ := measure_ball_ne_top
    have hCfin : m C ≠ ∞ := (measure_closedBall_lt_top : m C < ∞).ne
    have hBpos : 0 < m B := measure_ball_pos m x hr₀
    have hCpos : 0 < m C := hBpos.trans_le (measure_mono ball_subset_closedBall)
    have hrB : 0 < m.real B := ENNReal.toReal_pos hBpos.ne' hBfin
    have hrC : 0 < m.real C := ENNReal.toReal_pos hCpos.ne' hCfin
    have hratio : m.real C ≤ D * m.real B := by
      have hvol : m C ≤ ENNReal.ofReal D * m B :=
        (measure_mono (closedBall_subset_ball (by linarith))).trans (hD x r hr₀)
      have hfin : ENNReal.ofReal D * m B ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBfin
      simpa only [Measure.real, ENNReal.toReal_mul, ENNReal.toReal_ofReal hDpos.le] using
        ENNReal.toReal_mono hfin hvol
    have hweight : (m.real B)⁻¹ ≤ D * (m.real C)⁻¹ := by
      rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hrB hrC, one_mul]
      exact hratio
    have hCint : IntegrableOn f C m := hf.integrableOn_isCompact (isCompact_closedBall x r)
    have hBint : IntegrableOn f B m := hCint.mono_set ball_subset_closedBall
    have hconst : IntegrableOn (fun _ : X ↦ f x) B m := integrableOn_const hBfin
    have hiC : IntegrableOn (fun y ↦ ‖f y - f x‖) C m :=
      (hCint.sub (integrableOn_const hCfin)).norm
    have hset : (∫ y in B, ‖f y - f x‖ ∂m) ≤ ∫ y in C, ‖f y - f x‖ ∂m :=
      setIntegral_mono_set hiC (Eventually.of_forall fun _ ↦ norm_nonneg _)
        (Eventually.of_forall ball_subset_closedBall)
    have hdiff : (⨍ y in B, f y ∂m) - f x = ⨍ y in B, f y - f x ∂m := by
      rw [setAverage_fun_sub hBint hconst, setAverage_const hBpos.ne' hBfin]
    change dist (⨍ y in B, f y ∂m) (f x) ≤ D * (⨍ y in C, ‖f y - f x‖ ∂m)
    rw [dist_eq_norm, hdiff, setAverage_eq, setAverage_eq, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr hrB.le), smul_eq_mul]
    calc
      _ ≤ (m.real B)⁻¹ * (∫ y in B, ‖f y - f x‖ ∂m) :=
        mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (inv_nonneg.mpr hrB.le)
      _ ≤ (m.real B)⁻¹ * (∫ y in C, ‖f y - f x‖ ∂m) :=
        mul_le_mul_of_nonneg_left hset (inv_nonneg.mpr hrB.le)
      _ ≤ (D * (m.real C)⁻¹) * (∫ y in C, ‖f y - f x‖ ∂m) :=
        mul_le_mul_of_nonneg_right hweight (integral_nonneg fun _ ↦ norm_nonneg _)
      _ = _ := by rw [mul_assoc]
  exact squeeze_zero' (Eventually.of_forall fun _ ↦ dist_nonneg) hdom
    (by simpa only [mul_zero] using tendsto_const_nhds.mul hx')

end WalkDimensions
