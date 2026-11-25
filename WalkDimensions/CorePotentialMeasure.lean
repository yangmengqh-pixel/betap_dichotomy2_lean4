import WalkDimensions.CoreEnergyTruncation
import WalkDimensions.PotentialTruncation
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Distribution of a minimizing potential

The exact truncation energies determine the pushforward of the constructed
core energy measure under a minimizing potential.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal Topology

namespace WalkDimensions

noncomputable def dyadicUpper (a : ℝ) (n : ℕ) : ℝ :=
  oscillationWidth n * ((⌊a / oscillationWidth n⌋ : ℤ) + 1 : ℝ)

theorem lt_dyadicUpper (a : ℝ) (n : ℕ) : a < dyadicUpper a n := by
  have h := (div_lt_iff₀ (oscillationWidth_pos n)).mp (Int.lt_floor_add_one (a / oscillationWidth n))
  exact h.trans_eq (mul_comm _ _)

theorem dyadicUpper_le_add_width (a : ℝ) (n : ℕ) : dyadicUpper a n ≤ a + oscillationWidth n := by
  have h := (le_div_iff₀ (oscillationWidth_pos n)).mp (Int.floor_le (a / oscillationWidth n))
  dsimp [dyadicUpper]
  linarith only [h]

theorem tendsto_dyadicUpper (a : ℝ) : Tendsto (dyadicUpper a) atTop (𝓝[≥] a) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall (fun n ↦ (lt_dyadicUpper a n).le)⟩
  have h := tendsto_oscillationWidth.const_add a
  rw [add_zero] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
    (fun n ↦ (lt_dyadicUpper a n).le) (dyadicUpper_le_add_width a)

namespace PEnergy.CompactCore

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {p : ℝ} {E : PEnergy μ p}

theorem sublevelDistribution_of_unitPlate_minimizer (f : E.CompactCore) {K S : Set X}
    (hS : IsCompact S) (hf : E.UnitPlate K S f.domainElement f.toFun)
    (hmin : ∀ g w, E.UnitPlate K S g w → E.energy f.domainElement ≤ E.energy g)
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) :
    f.sublevelDistribution f a = a * (E.energy f.domainElement : ℝ) := by
  have hdy {b : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) {k : ℕ} {j : ℤ}
      (h : b = oscillationWidth k * (j : ℝ)) :
      f.sublevelDistribution f b = b * (E.energy f.domainElement : ℝ) := by
    obtain ⟨l, hl, hE⟩ := E.exists_minimizer_truncation hS hf hmin hb
    have he : (f.lowerClip hb.1).domainElement = l := by
      apply Subtype.ext
      apply Lp.ext
      exact (f.lowerClip hb.1).ae_eq.trans hl.symm
    change f.sublevelEnergyRoot f b ^ p = _
    rw [f.sublevelEnergyRoot_eq_root_lowerClip_of_dyadic hb.1 h, ← E.energy_eq_root_rpow, he, hE]
  rcases ha.2.eq_or_lt with rfl | ha₁
  · exact hdy ⟨zero_le_one, le_rfl⟩ (k := 0) (j := 1) (by norm_num [oscillationWidth])
  have hF := ((f.sublevelDistribution f).right_continuous' a).tendsto.comp (tendsto_dyadicUpper a)
  have hL := (tendsto_dyadicUpper a).mono_right nhdsWithin_le_nhds
  apply tendsto_nhds_unique_of_eventuallyEq hF (hL.mul_const (E.energy f.domainElement : ℝ))
  filter_upwards [tendsto_oscillationWidth.eventually_lt_const (sub_pos.mpr ha₁)] with n hn
  change f.sublevelDistribution f (dyadicUpper a n) = _
  have hb : dyadicUpper a n ∈ Icc (0 : ℝ) 1 :=
    ⟨ha.1.trans (lt_dyadicUpper a n).le, (dyadicUpper_le_add_width a n).trans
      (by linarith only [hn])⟩
  apply hdy hb (k := n) (j := ⌊a / oscillationWidth n⌋ + 1)
  push_cast
  rfl

theorem map_coreEnergyMeasure_of_unitPlate_minimizer (f : E.CompactCore) {K S : Set X}
    (hS : IsCompact S) (hf : E.UnitPlate K S f.domainElement f.toFun)
    (hmin : ∀ g w, E.UnitPlate K S g w → E.energy f.domainElement ≤ E.energy g) :
    Measure.map f.toFun f.coreEnergyMeasure =
      (E.energy f.domainElement : ℝ≥0∞) • volume.restrict (Icc (0 : ℝ) 1) := by
  have hunit : ∀ x, f.toFun x ∈ Icc (0 : ℝ) 1 := hf.2.2.1
  apply Measure.ext_of_Iic
  intro a
  rw [Measure.map_apply f.continuous.measurable measurableSet_Iic, smul_apply,
    Measure.restrict_apply measurableSet_Iic, smul_eq_mul]
  by_cases ha₀ : a < 0
  · have he : f.toFun ⁻¹' Iic a = ∅ := eq_empty_iff_forall_notMem.mpr
      (fun x hx ↦ ha₀.not_ge ((hunit x).1.trans hx))
    have hi : Iic a ∩ Icc (0 : ℝ) 1 = ∅ := eq_empty_iff_forall_notMem.mpr
      (fun x hx ↦ ha₀.not_ge (hx.2.1.trans hx.1))
    rw [he, hi, measure_empty, measure_empty, mul_zero]
  have ha : 0 ≤ a := le_of_not_gt ha₀
  by_cases ha₁ : a ≤ 1
  · have hi : Iic a ∩ Icc (0 : ℝ) 1 = Icc 0 a := by
      ext t
      exact ⟨fun ht ↦ ⟨ht.2.1, ht.1⟩, fun ht ↦ ⟨ht.2, ht.1, ht.2.trans ha₁⟩⟩
    change f.coreEnergyMeasure {x | f.toFun x ≤ a} = _
    rw [f.coreEnergyMeasure_sublevel f a, f.sublevelDistribution_of_unitPlate_minimizer hS hf hmin ⟨ha, ha₁⟩,
      hi, Real.volume_Icc, sub_zero, ENNReal.ofReal_mul ha, ENNReal.ofReal_coe_nnreal, mul_comm]
  · have ha' : 1 ≤ a := (lt_of_not_ge ha₁).le
    have he : f.toFun ⁻¹' Iic a = univ := eq_univ_of_forall fun x ↦ (hunit x).2.trans ha'
    have hi : Iic a ∩ Icc (0 : ℝ) 1 = Icc 0 1 := inter_eq_right.mpr fun x hx ↦ hx.2.trans ha'
    rw [he, hi, f.coreEnergyMeasure_univ, Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one]

end PEnergy.CompactCore
end WalkDimensions
