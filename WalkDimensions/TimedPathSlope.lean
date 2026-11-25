import WalkDimensions.UnitWeightConnectivity
import WalkDimensions.PointwiseSlope
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Controlling the change along a timed path by Lipschitz slopes
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal NNReal Topology

namespace WalkDimensions

variable {X : Type*} [MetricSpace X]

theorem lowerSemicontinuous_ballSlope {u : X → ℝ} (hu : Continuous u) (r : ℝ) :
    LowerSemicontinuous (ballSlope u r) := by
  apply lowerSemicontinuous_iff_isOpen_preimage.mpr
  intro c
  rw [Metric.isOpen_iff]
  intro x hx
  have h := lt_iSup_iff.mp (show c < ballSlope u r x from hx)
  obtain ⟨y, hy⟩ := h
  change c < ENNReal.ofReal (|u x - u y| / dist x (y : X)) at hy
  have hxy : x ≠ (y : X) := by
    intro he
    simp only [he, sub_self, abs_zero, zero_div, ENNReal.ofReal_zero, not_lt_zero] at hy
  let f (z : X) := ENNReal.ofReal (|u z - u y| / dist z (y : X))
  have hf : ContinuousAt f x :=
    ENNReal.continuous_ofReal.continuousAt.comp
      ((hu.sub continuous_const).abs.continuousAt.div
        (continuous_id.dist continuous_const).continuousAt (dist_ne_zero.mpr hxy))
  have hBall : x ∈ ball (y : X) r := by rw [mem_ball, dist_comm]; exact y.property
  have hEv : ∀ᶠ z in 𝓝 x, z ∈ ball (y : X) r ∧ c < f z :=
    (show ∀ᶠ z in 𝓝 x, z ∈ ball (y : X) r from isOpen_ball.mem_nhds hBall).and
      (hf.eventually_const_lt hy)
  obtain ⟨ε, hε, h⟩ := Metric.mem_nhds_iff.mp hEv
  refine ⟨ε, hε, fun z hz ↦ ?_⟩
  obtain ⟨hz', hfz⟩ := h hz
  have hyz : (y : X) ∈ ball z r := by rw [mem_ball, dist_comm]; exact hz'
  exact hfz.trans_le (le_iSup (fun v : ball z r ↦ ENNReal.ofReal (|u z - u v| / dist z (v : X))) ⟨y, hyz⟩)

private theorem TimedPath.ofReal_abs_deriv_le_slope {x y : X} (γ : TimedPath x y) (u : X → ℝ)
    (t : ℝ) (hd : DifferentiableAt ℝ (u ∘ γ.toFun) t) {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal |deriv (u ∘ γ.toFun) t| ≤ ballSlope u r (γ.toFun t) := by
  let v := u ∘ γ.toFun
  have hlim := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hd.hasDerivAt.tendsto_slope.abs
  apply le_of_tendsto hlim
  have hBall : ∀ᶠ s : ℝ in 𝓝[≠] t, s ∈ ball t r :=
    nhdsWithin_le_nhds (isOpen_ball.mem_nhds (mem_ball_self hr))
  filter_upwards [hBall, eventually_mem_nhdsWithin (a := t) (s := ({t} : Set ℝ)ᶜ)] with s hs hst
  have hst' : s ≠ t := hst
  have hDist : dist (γ.toFun s) (γ.toFun t) ≤ dist s t := by
    simpa only [NNReal.coe_one, one_mul] using γ.lipschitz.dist_le_mul s t
  have hsB := mem_ball.mpr (hDist.trans_lt (mem_ball.mp hs))
  have h := ofReal_abs_sub_le_ballSlope_mul_dist (u := u) hsB
  rw [dist_comm (γ.toFun t), abs_sub_comm] at h
  have h' := h.trans (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hDist) bot_le)
  have hst₀ : 0 < dist s t := dist_pos.mpr hst'
  have hBound := (ENNReal.div_le_iff (ENNReal.ofReal_pos.mpr hst₀).ne' ENNReal.ofReal_ne_top).mpr h'
  change ENNReal.ofReal |slope v t s| ≤ _
  rw [slope_def_field, abs_div, ← Real.dist_eq (s : ℝ) t, ENNReal.ofReal_div_of_pos hst₀]
  exact hBound

/-- The cost of the slope on any fixed positive scale dominates the
oscillation of the function along a path. -/
theorem TimedPath.ofReal_abs_sub_le_cost_ballSlope {x y : X} (γ : TimedPath x y)
    {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal |u x - u y| ≤ γ.cost (ballSlope u r) := by
  let v := u ∘ γ.toFun
  have hLip : LipschitzWith K v := by simpa only [mul_one] using hu.comp γ.lipschitz
  have hAC : AbsolutelyContinuousOnInterval v 0 γ.duration :=
    hLip.lipschitzOnWith.absolutelyContinuousOnInterval
  have hI : IntegrableOn (deriv v) (Ioc 0 γ.duration) volume := hAC.intervalIntegrable_deriv.1
  have hEq : (∫ t in Ioc 0 γ.duration, deriv v t ∂volume) = u y - u x := by
    have h := hAC.integral_deriv_eq_sub
    rwa [intervalIntegral.integral_of_le γ.duration_nonneg, show v γ.duration = u y by simp [v, γ.target],
      show v 0 = u x by simp [v, γ.source]] at h
  rw [abs_sub_comm, ← hEq, ← Real.norm_eq_abs]
  apply (ENNReal.ofReal_le_ofReal (norm_integral_le_integral_norm _)).trans
  rw [ofReal_integral_eq_lintegral_ofReal hI.norm (Eventually.of_forall fun _ ↦ norm_nonneg _)]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_of_ae (s := Ioc 0 γ.duration) hAC.ae_differentiableAt,
    ae_restrict_mem (μ := (volume : Measure ℝ)) (s := Ioc 0 γ.duration) measurableSet_Ioc] with t ht hmem
  rw [Real.norm_eq_abs]
  apply γ.ofReal_abs_deriv_le_slope u t _ hr
  apply ht
  rw [uIcc_of_le γ.duration_nonneg]
  exact Ioc_subset_Icc_self hmem

end WalkDimensions
