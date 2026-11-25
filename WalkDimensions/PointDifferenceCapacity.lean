import WalkDimensions.PointCapacityApproximation
import WalkDimensions.BallPotential
import WalkDimensions.CompactCore
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Point capacity bounded by a unit difference

Large cutoffs have energy tending to zero in the positive Morrey range.
They shift the two prescribed point values by the same constant.
-/

open Filter MeasureTheory Metric Set
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [ProperSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] {m : Measure X} [IsFiniteMeasureOnCompacts m]
  [m.IsOpenPosMeasure] {p : ℝ} (E : PEnergy m p)

theorem singleton_capacity_le_of_unit_point_difference {d β : ℝ}
    (hvol : AhlforsRegular m d) (hβ : d < β) {Γ : E.domain → Measure X}
    (hPI : E.Poincare Γ β) (hΓ : ∀ f, Γ f univ = (E.energy f : ℝ≥0∞))
    (hcap : E.CapacityUpperBound β)
    (f : E.CompactCore) {x y : X} (h : f.toFun x - f.toFun y = 1) :
    E.capacity {x} {y} ≤ (E.energy f.domainElement : ℝ≥0∞) := by
  obtain ⟨C, A, hC, _, hCut⟩ := E.exists_continuous_ball_cutoff hvol hβ hPI hΓ hcap
  obtain ⟨_, V, hV, hVolume⟩ := hvol
  have hp := zero_lt_one.trans E.one_lt
  let e := (β - d) / p
  have he : 0 < e := div_pos (sub_pos.mpr hβ) hp
  let D := |f.toFun y| * (C * V) ^ p⁻¹
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let S := E.rootSeminorm f.domainElement
  have hlim : Tendsto (fun r : ℝ ↦ ENNReal.ofReal ((S + D * r ^ (-e)) ^ p))
      atTop (𝓝 (E.energy f.domainElement : ℝ≥0∞)) := by
    have h := ((tendsto_rpow_neg_atTop he).const_mul D).const_add S
    have h' := ENNReal.tendsto_ofReal (((Real.continuous_rpow_const hp.le).tendsto (S + D * 0)).comp h)
    simpa only [S, Function.comp_def, mul_zero, add_zero, ← E.energy_eq_root_rpow,
      ENNReal.ofReal_coe_nnreal] using h'
  apply ge_of_tendsto hlim
  filter_upwards [eventually_gt_atTop (max (dist y x) 0)] with r hr
  have hr₀ : 0 < r := (le_max_right _ _).trans_lt hr
  have hyx : y ∈ ball x r := mem_ball.mpr ((le_max_left _ _).trans_lt hr)
  obtain ⟨g, u, hPlate, hEnergy⟩ := hCut x r hr₀
  let G : E.CompactCore := ⟨g, u, hPlate.2.1, hPlate.1,
    HasCompactSupport.intro (isCompact_closedBall _ _) hPlate.2.2.2.2⟩
  let F := f.add (G.smul (-f.toFun y))
  have hF (z : X) (hz : z ∈ ball x r) : F.toFun z = f.toFun z - f.toFun y := by
    change f.toFun z + -f.toFun y * u z = _
    rw [hPlate.2.2.2.1 hz, mul_one, sub_eq_add_neg]
  have hx : F.toFun x = 1 := (hF x (mem_ball_self hr₀)).trans h
  have hy : F.toFun y = 0 := (hF y hyx).trans (sub_self _)
  have hcapF := E.singleton_capacity_le_of_point_values F.ae_eq F.continuous hx hy
  apply hcapF.trans
  have hg : (E.energy g : ℝ) ≤ C * V * r ^ (d - β) := by
    have hE : (E.energy g : ℝ≥0∞) ≤ ENNReal.ofReal (C * V * r ^ (d - β)) :=
      hEnergy.trans ((mul_le_mul_of_nonneg_left (hVolume x r hr₀).2 bot_le).trans_eq (by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [sub_eq_add_neg, Real.rpow_add hr₀]
        ring))
    rw [← ENNReal.ofReal_coe_nnreal] at hE
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hE
  have hgRoot : E.rootSeminorm g ≤ (C * V) ^ p⁻¹ * r ^ (-e) := by
    rw [E.rootSeminorm_apply]
    have he' := Real.rpow_le_rpow (NNReal.coe_nonneg _) hg (inv_nonneg.mpr hp.le)
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hr₀.le,
      show (d - β) * p⁻¹ = -e by dsimp [e]; rw [div_eq_mul_inv]; ring] at he'
    exact he'
  have hFroot : E.rootSeminorm F.domainElement ≤ S + D * r ^ (-e) := by
    change E.rootSeminorm (f.domainElement + (-f.toFun y) • g) ≤ _
    apply (E.rootSeminorm.add_le' _ _).trans
    change S + E.rootSeminorm ((-f.toFun y) • g) ≤ _
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_neg]
    dsimp [D]
    rw [mul_assoc]
    exact add_le_add_right (mul_le_mul_of_nonneg_left hgRoot (abs_nonneg _)) _
  rw [← ENNReal.ofReal_coe_nnreal, E.energy_eq_root_rpow]
  exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (apply_nonneg _ _) hFroot hp.le)

end WalkDimensions.PEnergy
