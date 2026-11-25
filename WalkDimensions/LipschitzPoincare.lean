import WalkDimensions.BesovSlope

/-!
# The first-order endpoint yields a metric Poincaré inequality
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal NNReal Topology

namespace WalkDimensions

variable {X : Type*} [MetricSpace X]

theorem pointwiseSlope_eq_of_eqOn {f g : X → ℝ} {U : Set X} (hU : IsOpen U)
    (he : EqOn f g U) {x : X} (hx : x ∈ U) : pointwiseSlope f x = pointwiseSlope g x := by
  obtain ⟨r, hr, hBall⟩ := Metric.mem_nhds_iff.1 (hU.mem_nhds hx)
  have hBallEq {s : ℝ} (hs : s ≤ r) : ballSlope f s x = ballSlope g s x := by
    unfold ballSlope
    congr 1
    funext y
    have hy := he (hBall (ball_subset_ball hs y.property))
    change ENNReal.ofReal (|f x - f y| / dist x y) =
      ENNReal.ofReal (|g x - g y| / dist x y)
    rw [show f x = g x from he hx, hy]
  have hrSeq : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hSide (u v : X → ℝ)
      (h : ∀ s ≤ r, ballSlope u s x = ballSlope v s x) :
      pointwiseSlope u x ≤ pointwiseSlope v x := by
    apply le_iInf
    intro n
    obtain ⟨k, hk⟩ := (hrSeq.eventually_lt_const (lt_min hr (show 0 < 1 / ((n : ℝ) + 1) by
      positivity))).exists
    exact (iInf_le _ k).trans ((h _ ((lt_min_iff.mp hk).1.le)).trans_le
      (ballSlope_mono _ _ ((lt_min_iff.mp hk).2.le)))
  exact le_antisymm (hSide f g fun _ hs ↦ hBallEq hs) (hSide g f fun _ hs ↦ (hBallEq hs).symm)

/-- A Lipschitz function has a compactly supported Lipschitz representative
on any prescribed ball. -/
theorem exists_compact_lipschitz_eqOn_ball [ProperSpace X] {u : X → ℝ} {K : ℝ≥0}
    (hu : LipschitzWith K u) (x : X) {R : ℝ} (hR : 0 < R) :
    ∃ (v : X → ℝ) (L : ℝ≥0), LipschitzWith L v ∧ HasCompactSupport v ∧ EqOn v u (ball x R) := by
  let M := |u x| + (K : ℝ) * R + 1
  have hM : 0 < M := by dsimp only [M]; positivity
  let w (y : X) := max (M + R - dist y x) 0
  have hw : LipschitzWith 1 w := by
    have h := (LipschitzWith.const (α := X) (M + R)).sub (LipschitzWith.dist_left x)
    simpa only [zero_add] using h.max_const (0 : ℝ)
  let v (y : X) := min (max (u y) (-w y)) (w y)
  refine ⟨v, max (max K 1) 1, (hu.max hw.neg).min hw, ?_, ?_⟩
  · apply HasCompactSupport.intro (isCompact_closedBall x (M + R))
    intro y hy
    have he : w y = 0 := max_eq_right (sub_nonpos.mpr (le_of_not_ge hy))
    dsimp only [v]
    rw [he, neg_zero, min_eq_right (le_max_right _ _)]
  · intro y hy
    have hUy := hu.dist_le_mul y x
    rw [Real.dist_eq] at hUy
    have hm : |u y| ≤ M := by
      have hb := (abs_add_le (u y - u x) (u x)).trans (add_le_add_left hUy _)
      rw [sub_add_cancel] at hb
      exact hb.trans (by dsimp [M]; nlinarith only [mem_ball.mp hy, K.coe_nonneg])
    have hwM : M ≤ w y := by
      apply le_max_of_le_left
      have h := mem_ball.mp hy
      linarith
    change min (max (u y) (-w y)) (w y) = u y
    obtain ⟨hl, hr⟩ := abs_le.mp (hm.trans hwM)
    rw [max_eq_left hl, min_eq_left hr]

variable [MeasurableSpace X] [BorelSpace X] [ProperSpace X] [SecondCountableTopology X]
  {m : Measure X} [m.Regular] [SFinite m] [m.IsOpenPosMeasure]

/-- Poincaré inequality with the pointwise Lipschitz slope in the first-order scale. -/
def SlopePoincare (m : Measure X) (p : ℝ) : Prop :=
  ∃ C : ℝ≥0∞, 0 < C ∧ C ≠ ∞ ∧ ∃ A : ℝ, 1 ≤ A ∧
    ∀ (x : X) (r : ℝ), 0 < r → ∀ (u : X → ℝ) {K : ℝ≥0}, LipschitzWith K u →
      (∫⁻ y in ball x r, ENNReal.ofReal |u y - ⨍ z in ball x r, u z ∂m| ^ p ∂m) ≤
        C * (ENNReal.ofReal r) ^ p * ∫⁻ y in ball x (A * r), pointwiseSlope u y ^ p ∂m

namespace PEnergy

theorem slopePoincare_of_firstOrder {p : ℝ} (E : PEnergy m p)
    (hvol : VolumeDoubling m) (hPI : E.Poincare E.energyMeasure p)
    (hcap : E.CapacityUpperBound p) : SlopePoincare m p := by
  obtain ⟨K, hK, hKT, hEnergy⟩ := E.exists_energy_of_compact_lipschitz_at_firstOrder hvol hPI hcap
  obtain ⟨C, A, hC, hA, hPI⟩ := hPI
  refine ⟨ENNReal.ofReal C * K, pos_iff_ne_zero.mpr (mul_ne_zero (ENNReal.ofReal_pos.mpr hC).ne' hK.ne'),
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKT, A, hA, ?_⟩
  intro x r hr u L hu
  have hAr : 0 < A * r := mul_pos (zero_lt_one.trans_le hA) hr
  obtain ⟨v, L', hv, hvC, hEq⟩ := exists_compact_lipschitz_eqOn_ball hu x hAr
  obtain ⟨f, hf, hfE⟩ := hEnergy v hv hvC
  have hε := hPI x r hr f
  have hSub : ball x r ⊆ ball x (A * r) := ball_subset_ball (by nlinarith only [hA, hr])
  have hAE : (f : RealLp m p) =ᵐ[m.restrict (ball x r)] u := by
    filter_upwards [ae_restrict_of_ae hf, ae_restrict_mem (μ := m) measurableSet_ball] with y hy hB
    exact hy.trans (hEq (hSub hB))
  have havg := average_congr hAE
  have hInt : (∫⁻ y in ball x r, ENNReal.ofReal |u y - ⨍ z in ball x r, u z ∂m| ^ p ∂m) =
      ∫⁻ y in ball x r, ENNReal.ofReal |(f : RealLp m p) y - ⨍ z in ball x r, (f : RealLp m p) z ∂m| ^ p ∂m := by
    apply lintegral_congr_ae
    filter_upwards [hAE] with y hy
    rw [hy, havg]
  have hSlope : (∫⁻ y in ball x (A * r), pointwiseSlope v y ^ p ∂m) =
      ∫⁻ y in ball x (A * r), pointwiseSlope u y ^ p ∂m := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem (μ := m) measurableSet_ball] with y hy
    rw [pointwiseSlope_eq_of_eqOn isOpen_ball hEq hy]
  rw [hInt]
  apply hε.trans
  have hfE' := hfE (ball x (A * r)) isOpen_ball measure_ball_ne_top
  rw [hSlope] at hfE'
  refine (mul_le_mul_of_nonneg_left hfE' bot_le).trans_eq ?_
  rw [ENNReal.ofReal_mul hC.le, ← ENNReal.ofReal_rpow_of_pos hr]
  ac_rfl

end PEnergy

end WalkDimensions
