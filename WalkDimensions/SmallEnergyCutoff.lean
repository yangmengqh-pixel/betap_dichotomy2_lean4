import WalkDimensions.BallPotential
import WalkDimensions.CompactCore
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Large cutoffs with arbitrarily small normalized energy
-/

open Filter MeasureTheory Metric Set
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [ProperSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
  [μ.IsOpenPosMeasure] {p : ℝ} (E : PEnergy μ p)

theorem exists_small_energy_large_cutoff {d β : ℝ} (hvol : AhlforsRegular μ d)
    (hβ : d < β) {Γ : E.domain → Measure X} (hPI : E.Poincare Γ β)
    (hΓ : ∀ f, Γ f univ = (E.energy f : ℝ≥0∞)) (hcap : E.CapacityUpperBound β)
    {B ε : ℝ} (hB : 0 < B) (hε : 0 < ε) :
    ∃ L > B, ∀ (y : X) (r : ℝ), 0 < r → ∃ g : E.CompactCore,
      (∀ x, g.toFun x ∈ Icc (0 : ℝ) 1) ∧ EqOn g.toFun (fun _ ↦ 1) (closedBall y (B * r)) ∧
      tsupport g.toFun ⊆ ball y (L * r) ∧ (E.energy g.domainElement : ℝ) ≤ ε * r ^ (d - β) := by
  obtain ⟨C, A, hC, hA, hCut⟩ := E.exists_continuous_ball_cutoff hvol hβ hPI hΓ hcap
  obtain ⟨_, V, hV, hVol⟩ := hvol
  have hLimit : Tendsto (fun R : ℝ ↦ R ^ (d - β)) atTop (𝓝 0) := by
    rw [show d - β = -(β - d) by ring]
    exact tendsto_rpow_neg_atTop (sub_pos.mpr hβ)
  obtain ⟨R, hR, hSmall⟩ := ((eventually_gt_atTop B).and (hLimit.eventually_lt_const
    (div_pos hε (mul_pos hC hV)))).exists
  have hR₀ := hB.trans hR
  have hA₀ := zero_lt_one.trans hA
  let L := 2 * A * R
  have hAR : R < L := by
    have h := mul_lt_mul_of_pos_right hA hR₀
    rw [one_mul] at h
    apply h.trans_le
    dsimp [L]
    nlinarith only [mul_pos hA₀ hR₀]
  refine ⟨L, hR.trans hAR, fun y r hr ↦ ?_⟩
  obtain ⟨g, u, hPlate, hEnergy⟩ := hCut y (R * r) (mul_pos hR₀ hr)
  let K := closedBall y (A * (R * r))
  have hK : IsCompact K := isCompact_closedBall _ _
  let G : E.CompactCore :=
    ⟨g, u, hPlate.2.1, hPlate.1, HasCompactSupport.intro hK hPlate.2.2.2.2⟩
  refine ⟨G, hPlate.2.2.1, ?_, ?_, ?_⟩
  · intro x hx
    exact hPlate.2.2.2.1 (mem_ball.mpr ((mem_closedBall.mp hx).trans_lt
      (mul_lt_mul_of_pos_right hR hr)))
  · have hS : tsupport u ⊆ K := by
      apply closure_minimal _ hK.isClosed
      intro x hx
      by_contra h
      exact hx (hPlate.2.2.2.2 h)
    intro x hx
    apply mem_ball.mpr
    refine (mem_closedBall.mp (hS hx)).trans_lt ?_
    dsimp [L]
    nlinarith only [mul_pos hA₀ (mul_pos hR₀ hr)]
  · have hE₀ : (E.energy g : ℝ≥0∞) ≤ ENNReal.ofReal (C * V * (R * r) ^ (d - β)) :=
      hEnergy.trans ((mul_le_mul_of_nonneg_left (hVol y _ (mul_pos hR₀ hr)).2 bot_le).trans_eq (by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [sub_eq_add_neg, Real.rpow_add (mul_pos hR₀ hr)]
        ring))
    rw [← ENNReal.ofReal_coe_nnreal] at hE₀
    have hE := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hE₀
    refine hE.trans ?_
    rw [Real.mul_rpow hR₀.le hr.le, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right
      (by rw [mul_comm]; exact ((lt_div_iff₀ (mul_pos hC hV)).mp hSmall).le)
      (Real.rpow_nonneg hr.le _)

end WalkDimensions.PEnergy
