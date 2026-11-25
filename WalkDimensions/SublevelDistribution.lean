import WalkDimensions.SublevelEnergy
import Mathlib.MeasureTheory.Measure.Stieltjes

/-!
# Distribution functions of localized energy

For each compactly supported test, the sublevel limits determine a finite
Stieltjes measure on the real line with the full energy as total mass.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {p : ℝ} {E : PEnergy μ p}

theorem CompactCore.exists_abs_le (g : E.CompactCore) : ∃ B : ℝ, 0 ≤ B ∧ ∀ x, |g.toFun x| ≤ B := by
  obtain ⟨B, hB⟩ :=
    (g.compactSupport.isCompact.image (continuous_abs.comp g.continuous)).bddAbove
  refine ⟨max B 0, le_max_right _ _, fun x ↦ ?_⟩
  by_cases hx : x ∈ tsupport g.toFun
  · exact (hB (mem_image_of_mem _ hx)).trans (le_max_left _ _)
  · rw [notMem_support.mp (fun hx' ↦ hx (subset_closure hx')), abs_zero]
    exact le_max_right _ _

theorem CompactCore.sublevelEnergyRoot_eq_full (f g : E.CompactCore) {a : ℝ}
    (ha : ∀ x, g.toFun x ≤ a) :
    f.sublevelEnergyRoot g a = E.rootSeminorm f.domainElement := by
  have he (n : ℕ) : E.rootSeminorm (f.oscillation g a n) = E.rootSeminorm f.domainElement := by
    let r := oscillationWidth n
    have hr : 0 < r := oscillationWidth_pos n
    obtain ⟨w, hw, hwE⟩ :=
      E.exists_sawtooth_energy_eq f.domainElement f.ae_eq f.continuous f.compactSupport hr
    have hw' : w = f.oscillation g a n := by
      apply Subtype.ext
      apply Lp.ext
      filter_upwards [hw, f.oscillation_ae g a n] with x hx hy
      rw [hx, hy]
      change sawtooth r (f.toFun x) = min (sawtooth r (f.toFun x)) (sublevelRamp r a (g.toFun x))
      rw [sublevelRamp_eq_cap hr.le (ha x), min_eq_left (sawtooth_le hr _)]
    rw [← hw', E.rootSeminorm_apply, E.rootSeminorm_apply, hwE]
  simp only [CompactCore.sublevelEnergyRoot, he, ciInf_const]

theorem CompactCore.sublevelEnergyRoot_eq_zero (f g : E.CompactCore) {a b : ℝ}
    (hab : a < b) (hb : ∀ x, b ≤ g.toFun x) :
    f.sublevelEnergyRoot g a = 0 := by
  obtain ⟨n, hn⟩ := (tendsto_oscillationWidth.eventually_lt_const (sub_pos.mpr hab)).exists
  have he : f.oscillation g a n = 0 := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [f.oscillation_ae g a n, Lp.coeFn_zero (α := X) (E := ℝ) (p := ENNReal.ofReal p)
      (μ := μ)] with x hx hy
    change (f.oscillation g a n : RealLp μ p) x = (0 : RealLp μ p) x
    rw [hx, hy, Pi.zero_apply, sublevelRamp_eq_zero
      (show a + oscillationWidth n ≤ g.toFun x by linarith only [hn, hb x]),
      min_eq_right (sawtooth_nonneg _ _)]
  have h := f.sublevelEnergyRoot_le g a n
  rw [he, map_zero] at h
  exact le_antisymm h (f.sublevelEnergyRoot_nonneg g a)

/-- The Stieltjes function obtained by localizing the energy to sublevel sets. -/
noncomputable def CompactCore.sublevelDistribution (f g : E.CompactCore) :
    StieltjesFunction ℝ where
  toFun a := f.sublevelEnergyRoot g a ^ p
  mono' a b hab := Real.rpow_le_rpow (f.sublevelEnergyRoot_nonneg g a)
    (f.monotone_sublevelEnergyRoot g hab) (zero_lt_one.trans E.one_lt).le
  right_continuous' a := by
    change Tendsto (fun t ↦ f.sublevelEnergyRoot g t ^ p) (𝓝[≥] a)
      (𝓝 (f.sublevelEnergyRoot g a ^ p))
    simpa only [Function.comp_def] using
      ((Real.continuous_rpow_const (zero_lt_one.trans E.one_lt).le).tendsto
        (f.sublevelEnergyRoot g a)).comp (f.tendsto_sublevelEnergyRoot_right g a)

theorem CompactCore.tendsto_oscillation_energy (f g : E.CompactCore) (a : ℝ) :
    Tendsto (fun n ↦ (E.energy (f.oscillation g a n) : ℝ)) atTop (𝓝 (f.sublevelDistribution g a)) := by
  change Tendsto (fun n ↦ (E.energy (f.oscillation g a n) : ℝ)) atTop
    (𝓝 (f.sublevelEnergyRoot g a ^ p))
  simpa only [Function.comp_def, ← E.energy_eq_root_rpow] using
    ((Real.continuous_rpow_const (zero_lt_one.trans E.one_lt).le).tendsto
      (f.sublevelEnergyRoot g a)).comp (f.tendsto_sublevelEnergyRoot g a)

theorem CompactCore.tendsto_sublevelDistribution_atBot (f g : E.CompactCore) :
    Tendsto (f.sublevelDistribution g) atBot (𝓝 0) := by
  obtain ⟨B, _, hB⟩ := g.exists_abs_le
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_lt_atBot (-B)] with a ha
  change 0 = f.sublevelEnergyRoot g a ^ p
  rw [f.sublevelEnergyRoot_eq_zero g ha (fun x ↦ (abs_le.mp (hB x)).1),
    Real.zero_rpow (zero_lt_one.trans E.one_lt).ne']

theorem CompactCore.tendsto_sublevelDistribution_atTop (f g : E.CompactCore) :
    Tendsto (f.sublevelDistribution g) atTop (𝓝 (E.energy f.domainElement : ℝ)) := by
  obtain ⟨B, _, hB⟩ := g.exists_abs_le
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop B] with a ha
  change (E.energy f.domainElement : ℝ) = f.sublevelEnergyRoot g a ^ p
  rw [f.sublevelEnergyRoot_eq_full g (fun x ↦ (abs_le.mp (hB x)).2.trans ha), E.energy_eq_root_rpow]

theorem CompactCore.measure_sublevelDistribution_univ (f g : E.CompactCore) :
    (f.sublevelDistribution g).measure univ = (E.energy f.domainElement : ℝ≥0∞) := by
  rw [StieltjesFunction.measure_univ _ (f.tendsto_sublevelDistribution_atBot g)
    (f.tendsto_sublevelDistribution_atTop g), sub_zero, ENNReal.ofReal_coe_nnreal]

end WalkDimensions.PEnergy
