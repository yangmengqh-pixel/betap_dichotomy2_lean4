import WalkDimensions.Besov
import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The measurable pointwise Lipschitz slope
-/

open Filter Function MeasureTheory Metric Set TopologicalSpace
open scoped ENNReal NNReal Topology

namespace WalkDimensions

variable {X : Type*} [MetricSpace X]

private noncomputable def slopeQuotient (u : X → ℝ) (x y : X) : ℝ≥0∞ :=
  ENNReal.ofReal (|u x - u y| / dist x y)

noncomputable def ballSlope (u : X → ℝ) (r : ℝ) (x : X) : ℝ≥0∞ :=
  ⨆ y : ball x r, slopeQuotient u x y

noncomputable def pointwiseSlope (u : X → ℝ) (x : X) : ℝ≥0∞ :=
  ⨅ n : ℕ, ballSlope u (1 / ((n : ℝ) + 1)) x

theorem ballSlope_mono (u : X → ℝ) (x : X) : Monotone (fun r ↦ ballSlope u r x) := by
  intro r s hrs
  apply iSup_le
  intro y
  exact le_iSup_of_le ⟨(y : X), ball_subset_ball hrs y.property⟩ le_rfl

theorem ballSlope_le_of_lipschitzWith {u : X → ℝ} {K : ℝ≥0} (h : LipschitzWith K u)
    (x : X) (r : ℝ) : ballSlope u r x ≤ K := by
  apply iSup_le
  intro y
  by_cases he : x = (y : X)
  · have hn : u x = u y := congrArg u he
    simp [slopeQuotient, hn]
  have hd : 0 < dist x (y : X) := dist_pos.mpr he
  rw [slopeQuotient, ← ENNReal.ofReal_coe_nnreal]
  apply ENNReal.ofReal_le_ofReal
  apply (div_le_iff₀ hd).mpr
  simpa only [Real.dist_eq] using h.dist_le_mul x y

theorem ofReal_abs_sub_le_ballSlope_mul_dist {u : X → ℝ} {r : ℝ} {x y : X}
    (hy : y ∈ ball x r) :
    ENNReal.ofReal |u x - u y| ≤ ballSlope u r x * ENNReal.ofReal (dist x y) := by
  by_cases he : x = y
  · subst y
    simp
  have hd := dist_pos.mpr he
  have h := le_iSup (fun z : ball x r ↦ slopeQuotient u x z) ⟨y, hy⟩
  have hz : slopeQuotient u x y * ENNReal.ofReal (dist x y) = ENNReal.ofReal |u x - u y| := by
    rw [slopeQuotient, ← ENNReal.ofReal_mul (div_nonneg (abs_nonneg _) hd.le),
      div_mul_cancel₀ _ hd.ne']
  rw [← hz]
  exact mul_le_mul_of_nonneg_right h bot_le

variable [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]

theorem measurable_ballSlope {u : X → ℝ} (hu : Continuous u) (r : ℝ) :
    Measurable (ballSlope u r) := by
  classical
  obtain ⟨T, hTc, hTd⟩ := exists_countable_dense X
  have : Countable T := hTc.to_subtype
  let f (y : X) (x : X) := if y ∈ ball x r then slopeQuotient u x y else 0
  have hEq (x : X) : ballSlope u r x = ⨆ y : T, f y x := by
    apply le_antisymm _ (iSup_le fun y ↦ ?_)
    · apply iSup_le
      intro y
      by_contra! hh
      have hn : x ≠ (y : X) := by
        intro he
        have hx : u x = u y := congrArg u he
        simp only [slopeQuotient, hx, sub_self, abs_zero, zero_div, ENNReal.ofReal_zero] at hh
        exact not_lt_of_ge bot_le hh
      let g (z : X) := slopeQuotient u x z
      have hy : ContinuousAt g (y : X) := by
        exact ENNReal.continuous_ofReal.continuousAt.comp
          ((continuous_const.sub hu).abs.continuousAt.div
            ((continuous_const.dist continuous_id).continuousAt) (dist_ne_zero.mpr hn))
      have hh' : ∀ᶠ z in 𝓝 (y : X), (⨆ w : T, f w x) < g z :=
        hy.eventually_const_lt hh
      have hb : ∀ᶠ z in 𝓝 (y : X), z ∈ ball x r := isOpen_ball.mem_nhds y.property
      have hclose := mem_closure_iff_nhds.mp (hTd (y : X))
      obtain ⟨z, hz, hzT⟩ := hclose _ (hb.and hh')
      have haz := le_iSup (fun w : T ↦ f w x) ⟨z, hzT⟩
      exact hz.2.not_ge (by simpa only [f, ite_eq_left hz.1] using haz)
    · by_cases hy : (y : X) ∈ ball x r
      · dsimp only [f]
        rw [ite_eq_left hy]
        exact le_iSup (fun z : ball x r ↦ slopeQuotient u x z) ⟨y, hy⟩
      · dsimp only [f]
        rw [ite_eq_right hy]
        exact bot_le
  simp_rw [funext hEq]
  refine Measurable.iSup fun y ↦ ?_
  have hs : {x : X | (y : X) ∈ ball x r} = ball (y : X) r := by
    ext x
    simp only [mem_ofPred_eq, mem_ball, dist_comm x (y : X)]
  dsimp only [f]
  apply Measurable.ite (show MeasurableSet {x : X | (y : X) ∈ ball x r} by rw [hs]; exact measurableSet_ball)
  · exact (((hu.sub continuous_const).abs.measurable).div (continuous_id.dist continuous_const).measurable).ennreal_ofReal
  · exact measurable_const

theorem measurable_pointwiseSlope {u : X → ℝ} (hu : Continuous u) : Measurable (pointwiseSlope u) :=
  Measurable.iInf fun n ↦ measurable_ballSlope hu (1 / ((n : ℝ) + 1))

end WalkDimensions
