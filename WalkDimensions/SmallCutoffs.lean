import WalkDimensions.BallPotential
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Exhaustion by small-energy cutoffs

When the walk exponent exceeds the volume exponent, expanding a ball
makes its capacitary energy tend to zero.
-/

open Filter MeasureTheory Metric Set
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SecondCountableTopology X] {m : Measure X}
  [IsFiniteMeasureOnCompacts m] [m.IsOpenPosMeasure] {p : ℝ} (E : PEnergy m p)

theorem exists_small_energy_cutoff {d β : ℝ} (hvol : AhlforsRegular m d)
    (hβ : d < β) {Γ : E.domain → Measure X} (hPI : E.Poincare Γ β)
    (hΓ : ∀ f, Γ f univ = (E.energy f : ℝ≥0∞)) (hcap : E.CapacityUpperBound β)
    {K : Set X} (hK : IsCompact K) (x : X) {ε : ℝ} (hε : 0 < ε) :
    ∃ (f : E.domain) (u : X → ℝ) (U : Set X),
      Continuous u ∧ HasCompactSupport u ∧ (f : RealLp m p) =ᵐ[m] u ∧
      IsOpen U ∧ K ⊆ U ∧ EqOn u (fun _ ↦ 1) U ∧ (E.energy f : ℝ) < ε := by
  obtain ⟨C, A, hC, _, hcut⟩ := E.exists_continuous_ball_cutoff hvol hβ hPI hΓ hcap
  obtain ⟨_, V, hV, hVbound⟩ := hvol
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.subset_closedBall_lt 0 x
  have hlim : Tendsto (fun r : ℝ ↦ C * V * r ^ (d - β)) atTop (𝓝 0) := by
    have h := tendsto_inv_atTop_zero.comp (tendsto_rpow_atTop (sub_pos.mpr hβ))
    have h' : Tendsto (fun r : ℝ ↦ r ^ (d - β)) atTop (𝓝 0) := by
      apply h.congr'
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
      dsimp only [Function.comp_apply]
      rw [show d - β = -(β - d) by ring, Real.rpow_neg hr]
    simpa only [mul_zero] using h'.const_mul (C * V)
  obtain ⟨r, hr₁, hr₂⟩ := ((eventually_gt_atTop R).and (hlim.eventually_lt_const hε)).exists
  have hr : 0 < r := hR.trans hr₁
  obtain ⟨f, u, hf, hE⟩ := hcut x r hr
  have hfbound : (E.energy f : ℝ≥0∞) ≤ ENNReal.ofReal (C * V * r ^ (d - β)) := by
    calc
      _ ≤ _ := hE
      _ ≤ ENNReal.ofReal (C * r ^ (-β)) * ENNReal.ofReal (V * r ^ d) :=
        mul_le_mul_of_nonneg_left (hVbound x r hr).2 bot_le
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [show C * r ^ (-β) * (V * r ^ d) = C * V * (r ^ (-β) * r ^ d) by ring,
          ← Real.rpow_add hr, sub_eq_neg_add]
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hfbound
  rw [ENNReal.coe_toReal, ENNReal.toReal_ofReal (by positivity)] at hreal
  exact ⟨f, u, ball x r, hf.1, HasCompactSupport.intro (isCompact_closedBall x (A * r)) hf.2.2.2.2,
    hf.2.1, isOpen_ball, hKR.trans (closedBall_subset_ball hr₁), hf.2.2.2.1, hreal.trans_lt hr₂⟩

end WalkDimensions.PEnergy
