import WalkDimensions.EnergyLatticeIdentity
import WalkDimensions.PointCapacityApproximation

/-!
# Comparison for approximate minimizers with point values

The compact-core lattice identity moves the global energy defect to a
competitor on a smaller support. Clarkson's inequality controls the
difference from a locally minimizing competitor.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {m : Measure X} [IsFiniteMeasureOnCompacts m] {p : ℝ} (E : PEnergy m p)

theorem exists_root_gap_bound :
    ∃ q > (0 : ℝ), ∀ (f g : E.domain) {L M : ℝ}, 0 ≤ L → L ≤ M →
      L ≤ E.rootSeminorm ((1 / 2 : ℝ) • (f + g)) →
      E.rootSeminorm f ≤ M → E.rootSeminorm g ≤ M →
      E.rootSeminorm (f - g) ^ q ≤ (2 * M) ^ q - (2 * L) ^ q := by
  obtain ⟨q, hq, hClarkson⟩ := E.exists_clarkson_power
  refine ⟨q, hq, fun f g L M hL hLM hMid hf hg ↦ ?_⟩
  rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hMid
  have hL' := Real.rpow_le_rpow (show 0 ≤ 2 * L by positivity)
    (show 2 * L ≤ E.rootSeminorm (f + g) by linarith only [hMid]) hq.le
  linarith only [hL', hClarkson f g M (hL.trans hLM) hf hg]

namespace CompactCore

variable {E} [LocallyCompactSpace X]

theorem energy_min_le_add_point_defect (f v : E.CompactCore) {x y : X}
    (hfx : f.toFun x = 1) (hfy : f.toFun y = 0) (hvx : v.toFun x = 0) (hvy : v.toFun y = 0) :
    (E.energy (f.minAddConst v (a := 0) le_rfl).domainElement : ℝ) ≤
      (E.energy v.domainElement : ℝ) + ((E.energy f.domainElement : ℝ) - (E.capacity {x} {y}).toReal) := by
  let F := f.sup v
  have hx : F.toFun x = 1 := by
    rw [sup_apply, hfx, hvx, max_eq_left zero_le_one]
  have hy : F.toFun y = 0 := by
    rw [sup_apply, hfy, hvy, max_self]
  have hcap := E.singleton_capacity_le_of_point_values F.ae_eq F.continuous hx hy
  have hh := ENNReal.toReal_mono ENNReal.coe_ne_top hcap
  rw [ENNReal.coe_toReal] at hh
  have he := congrArg NNReal.toReal (f.energy_sup_add_min v)
  simp only [NNReal.coe_add] at he
  linarith only [he, hh]

end CompactCore
end WalkDimensions.PEnergy
