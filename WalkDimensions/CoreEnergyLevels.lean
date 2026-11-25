import WalkDimensions.LocalEnergyBound
import WalkDimensions.EnergyLatticeIdentity

/-!
# Level sets carry no energy for the associated function
-/

open Filter Function MeasureTheory Set
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy.CompactCore

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {p : ℝ} {E : PEnergy μ p}

noncomputable def levelCorrection (f : E.CompactCore) (a : ℝ) (n : ℕ) : E.CompactCore :=
  (f.neg.ramp (oscillationWidth n) (-a)).sub (f.ramp (oscillationWidth n) a)

noncomputable def levelCorrectionCenter (a : ℝ) (n : ℕ) : ℝ :=
  a + sublevelRamp (oscillationWidth n) (-a) 0 - sublevelRamp (oscillationWidth n) a 0

theorem tendsto_levelCorrectionCenter (a : ℝ) :
    Tendsto (levelCorrectionCenter a) atTop (𝓝 a) := by
  have h (b : ℝ) : Tendsto (fun n ↦ sublevelRamp (oscillationWidth n) b 0) atTop (𝓝 0) := by
    refine squeeze_zero (fun n ↦ sublevelRamp_nonneg _ _ _) (fun n ↦ ?_)
      tendsto_oscillationWidth
    exact max_le (min_le_right _ _) (oscillationWidth_pos n).le
  unfold levelCorrectionCenter
  simpa only [add_zero, sub_zero] using ((h (-a)).const_add a).sub (h a)

omit [LocallyCompactSpace X] in
theorem tendsto_graph_levelCorrection (f : E.CompactCore) (a : ℝ) :
    Tendsto (fun n ↦ E.graphSeminorm (f.levelCorrection a n).domainElement) atTop (𝓝 0) := by
  have h := (f.neg.tendsto_graph_ramp (-a)).add (f.tendsto_graph_ramp a)
  rw [add_zero] at h
  refine squeeze_zero (fun _ ↦ apply_nonneg _ _) (fun n ↦ ?_) h
  change E.graphSeminorm ((f.neg.ramp (oscillationWidth n) (-a)).domainElement + -
      (f.ramp (oscillationWidth n) a).domainElement) ≤ _
  rw [← sub_eq_add_neg]
  exact map_sub_le_add _ _ _

theorem sub_levelCorrection_eq (f : E.CompactCore) {a : ℝ} {n : ℕ} {x : X}
    (hx : |f.toFun x - a| < oscillationWidth n) :
    f.toFun x - (f.levelCorrection a n).toFun x = levelCorrectionCenter a n := by
  change f.toFun x - (offsetRamp (oscillationWidth n) (-a) (-f.toFun x) - offsetRamp (oscillationWidth n) a (f.toFun x)) = _
  have hb := abs_lt.mp hx
  have hr : 0 ≤ oscillationWidth n := (oscillationWidth_pos n).le
  unfold offsetRamp levelCorrectionCenter
  by_cases ht : f.toFun x ≤ a
  · rw [sublevelRamp_eq_cap hr ht]
    have h₁ : -a + oscillationWidth n - -f.toFun x ≤ oscillationWidth n := by linarith only [ht]
    have h₂ : 0 ≤ -a + oscillationWidth n - -f.toFun x := by linarith only [hb.1]
    rw [show sublevelRamp (oscillationWidth n) (-a) (-f.toFun x) = -a + oscillationWidth n - -f.toFun x by
      rw [sublevelRamp, min_eq_left h₁, max_eq_left h₂]]
    ring
  · rw [sublevelRamp_eq_cap hr (show -f.toFun x ≤ -a by linarith only [lt_of_not_ge ht])]
    have h₁ : a + oscillationWidth n - f.toFun x ≤ oscillationWidth n := by linarith only [lt_of_not_ge ht]
    have h₂ : 0 ≤ a + oscillationWidth n - f.toFun x := by linarith only [hb.2]
    rw [show sublevelRamp (oscillationWidth n) a (f.toFun x) = a + oscillationWidth n - f.toFun x by
      rw [sublevelRamp, min_eq_left h₁, max_eq_left h₂]]
    ring

theorem coreEnergyMeasure_level (f : E.CompactCore) (a : ℝ) :
    f.coreEnergyMeasure {x | f.toFun x = a} = 0 := by
  let r := oscillationWidth
  let v := f.levelCorrection a
  have hv : Tendsto (fun n ↦ E.rootSeminorm (v n).domainElement) atTop (𝓝 0) :=
    squeeze_zero (fun _ ↦ apply_nonneg _ _) (fun _ ↦ E.rootSeminorm_le_graphSeminorm _)
      (f.tendsto_graph_levelCorrection a)
  have hE : Tendsto (fun n ↦ (E.energy (v n).domainElement : ℝ≥0∞)) atTop (𝓝 0) := by
    have hp := zero_lt_one.trans E.one_lt
    have h := ENNReal.tendsto_ofReal (((Real.continuous_rpow_const hp.le).tendsto 0).comp hv)
    simpa only [Function.comp_def, ← E.energy_eq_root_rpow, ENNReal.ofReal_coe_nnreal,
      Real.zero_rpow hp.ne', ENNReal.ofReal_zero] using h
  apply le_antisymm _ bot_le
  apply ge_of_tendsto hE
  refine Eventually.of_forall fun n ↦ ?_
  let U := {x | |f.toFun x - a| < r n}
  have hU : IsOpen U := isOpen_lt (continuous_abs.comp (f.continuous.sub continuous_const))
    continuous_const
  have hsub : {x | f.toFun x = a} ⊆ U := by
    intro x hx
    change f.toFun x = a at hx
    change |f.toFun x - a| < r n
    rw [hx, sub_self, abs_zero]
    exact oscillationWidth_pos n
  have heq : EqOn (fun x ↦ f.toFun x - (v n).toFun x)
      (fun _ ↦ levelCorrectionCenter a n) U := fun _ hx ↦ f.sub_levelCorrection_eq hx
  exact (measure_mono hsub).trans (f.coreEnergyMeasure_open_le_energy_of_eqOn_sub_const (v n) hU heq)

end WalkDimensions.PEnergy.CompactCore
