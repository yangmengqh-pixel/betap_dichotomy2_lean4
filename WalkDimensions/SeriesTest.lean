import WalkDimensions.PointDifferenceCapacity
import WalkDimensions.SeriesEnergy
import WalkDimensions.ResistanceTriangle
import WalkDimensions.EnergyLatticeIdentity

/-!
# A pair of separated test functions gives a series bound
-/

open Function MeasureTheory Metric Set
open scoped ENNReal

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [ProperSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] {m : Measure X} [IsFiniteMeasureOnCompacts m]
  [m.IsOpenPosMeasure] {p : ℝ} (E : PEnergy m p)

theorem pointResistanceLength_ge_series_of_disjoint_tests {d β : ℝ}
    (hvol : AhlforsRegular m d) (hβ : d < β) {Γ : E.domain → Measure X}
    (hPI : E.Poincare Γ β) (hΓ : ∀ f, Γ f univ = (E.energy f : ℝ≥0∞))
    (hcap : E.CapacityUpperBound β)
    (f g : E.CompactCore) {x z : X} (hx : f.toFun x = 1) (hz : g.toFun z = 1)
    (hdisj : Disjoint (support f.toFun) (support g.toFun)) :
    ((E.energy f.domainElement : ℝ) ^ (-(p - 1)⁻¹) +
      (E.energy g.domainElement : ℝ) ^ (-(p - 1)⁻¹)) ≤ E.pointResistanceLength x z := by
  have hxS : x ∈ support f.toFun := by rw [mem_support, hx]; exact one_ne_zero
  have hzS : z ∈ support g.toFun := by rw [mem_support, hz]; exact one_ne_zero
  have hgx : g.toFun x = 0 := notMem_support.mp (Set.disjoint_left.mp hdisj hxS)
  have hfz : f.toFun z = 0 := notMem_support.mp (Set.disjoint_left.mp hdisj.symm hzS)
  have hxz : x ≠ z := by
    intro he
    exact Set.disjoint_left.mp hdisj hxS (he ▸ hzS)
  obtain ⟨A, _, hA, _, hBounds⟩ := E.singleton_capacity_bounds hvol hβ hPI hΓ hcap
  have hcapPos {u v : X} (h : u ≠ v) : 0 < (E.capacity {u} {v}).toReal := by
    have hfi := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hBounds u v h).2
    have hpos : 0 < ENNReal.ofReal (A * dist u v ^ (d - β)) := ENNReal.ofReal_pos.mpr
      (mul_pos hA (Real.rpow_pos_of_pos (dist_pos.mpr h) _))
    exact ENNReal.toReal_pos (hpos.trans_le (hBounds u v h).1).ne' hfi
  have hfE : 0 < (E.energy f.domainElement : ℝ) := by
    have h := ENNReal.toReal_mono ENNReal.coe_ne_top
      (E.singleton_capacity_le_of_point_values f.ae_eq f.continuous hx hfz)
    rw [ENNReal.coe_toReal] at h
    exact (hcapPos hxz).trans_le h
  have hgE : 0 < (E.energy g.domainElement : ℝ) := by
    have h := ENNReal.toReal_mono ENNReal.coe_ne_top
      (E.singleton_capacity_le_of_point_values g.ae_eq g.continuous hz hgx)
    rw [ENNReal.coe_toReal] at h
    exact (hcapPos hxz.symm).trans_le h
  let r := (E.energy f.domainElement : ℝ) ^ (-(p - 1)⁻¹)
  let s := (E.energy g.domainElement : ℝ) ^ (-(p - 1)⁻¹)
  have hr : 0 < r := Real.rpow_pos_of_pos hfE _
  have hs : 0 < s := Real.rpow_pos_of_pos hgE _
  let t := s / (r + s)
  have ht : t ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hs.le (add_pos hr hs).le, (div_le_one (add_pos hr hs)).mpr (le_add_of_nonneg_left hr.le)⟩
  let G := f.smul (1 - t)
  let H := g.smul (-t)
  let W := G.add H
  have hUnit : W.toFun x - W.toFun z = 1 := by
    change ((1 - t) * f.toFun x + (-t) * g.toFun x) -
      ((1 - t) * f.toFun z + (-t) * g.toFun z) = 1
    rw [hx, hz, hgx, hfz]
    ring
  have hcapW := E.singleton_capacity_le_of_unit_point_difference hvol hβ hPI hΓ hcap W hUnit
  have hcapReal := ENNReal.toReal_mono ENNReal.coe_ne_top hcapW
  rw [ENNReal.coe_toReal] at hcapReal
  have hdisj' : Disjoint (support G.toFun) (support H.toFun) := by
    apply hdisj.mono
    · apply support_subset_iff'.mpr
      intro y hy
      change (1 - t) * f.toFun y = 0
      rw [notMem_support.mp hy, mul_zero]
    · apply support_subset_iff'.mpr
      intro y hy
      change -t * g.toFun y = 0
      rw [notMem_support.mp hy, mul_zero]
  have hW := congrArg NNReal.toReal (G.energy_add_of_disjoint_support H hdisj')
  change (E.energy W.domainElement : ℝ) =
    ((E.energy ((1 - t) • f.domainElement) + E.energy ((-t) • g.domainElement) : NNReal) : ℝ) at hW
  rw [NNReal.coe_add, E.energy_smul_real, E.energy_smul_real,
    abs_of_nonneg (sub_nonneg.mpr ht.2), abs_neg, abs_of_nonneg ht.1] at hW
  have he : (-(p - 1)⁻¹) * (1 - p) = 1 := by
    rw [show 1 - p = -(p - 1) by ring, neg_mul_neg, inv_mul_cancel₀ (sub_pos.mpr E.one_lt).ne']
  have hEf : r ^ (1 - p) = (E.energy f.domainElement : ℝ) := by
    dsimp [r]
    rw [← Real.rpow_mul hfE.le, he, Real.rpow_one]
  have hEg : s ^ (1 - p) = (E.energy g.domainElement : ℝ) := by
    dsimp [s]
    rw [← Real.rpow_mul hgE.le, he, Real.rpow_one]
  have hseries := (series_energy_minimum E.one_lt hr hs ht).2.mpr rfl
  have hWE : (E.energy W.domainElement : ℝ) = (r + s) ^ (1 - p) := by
    rw [hW, ← hEf, ← hEg, mul_comm ((1 - t) ^ p), mul_comm (t ^ p)]
    exact hseries
  rw [hWE] at hcapReal
  have hPow := Real.rpow_le_rpow_of_nonpos (hcapPos hxz) hcapReal
    (neg_nonpos.mpr (inv_nonneg.mpr (sub_pos.mpr E.one_lt).le))
  rw [← Real.rpow_mul (add_pos hr hs).le, mul_comm (1 - p), he, Real.rpow_one] at hPow
  change r + s ≤ _
  refine hPow.trans_eq ?_
  rw [pointResistanceLength, resistance, ENNReal.toReal_inv,
    Real.rpow_neg ENNReal.toReal_nonneg, Real.inv_rpow ENNReal.toReal_nonneg]

end WalkDimensions.PEnergy
