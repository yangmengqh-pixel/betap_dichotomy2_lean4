import WalkDimensions.CoreEnergyLevels
import WalkDimensions.SawtoothPeriod

/-!
# Affine locality at dyadic offsets

The fine sawtooths are unchanged by sign changes and translations by
integer multiples of a fixed dyadic width.
-/

open Filter Function MeasureTheory Set TopologicalSpace
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy.CompactCore

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {p : ℝ} {E : PEnergy μ p}

theorem coreEnergyMeasure_compact_eq_of_eqOn_dyadic (f h : E.CompactCore)
    (K : Compacts X) {U : Set X} (hU : IsOpen U) (hKU : (K : Set X) ⊆ U)
    (k : ℕ) (j : ℤ) (s : ℝ) (hs : s = 1 ∨ s = -1)
    (heq : EqOn f.toFun (fun x ↦ s * h.toFun x + oscillationWidth k * (j : ℝ)) U) :
    f.coreEnergyMeasure K = h.coreEnergyMeasure K := by
  obtain ⟨g, hg, hgu⟩ := E.exists_compactCore_sublevel_eq K.isCompact' hU hKU
  rw [f.coreEnergyMeasure_compact g K (-1) hg, h.coreEnergyMeasure_compact g K (-1) hg]
  congr 1
  apply tendsto_nhds_unique_of_eventuallyEq (f.tendsto_oscillation_energy g (-1))
    (h.tendsto_oscillation_energy g (-1))
  filter_upwards [tendsto_oscillationWidth.eventually_lt_const (show (0 : ℝ) < 1 by norm_num),
    eventually_gt_atTop k] with n hn hkn
  have he : f.oscillation g (-1) n = h.oscillation g (-1) n := by
    change (f.oscillationCore g (-1) n).domainElement = (h.oscillationCore g (-1) n).domainElement
    apply domainElement_eq_of_toFun_eq
    funext x
    let r := oscillationWidth n
    change min (sawtooth r (f.toFun x)) (sublevelRamp r (-1) (g.toFun x)) =
      min (sawtooth r (h.toFun x)) (sublevelRamp r (-1) (g.toFun x))
    by_cases hx : x ∈ U
    · rw [heq hx, show sawtooth r (s * h.toFun x + oscillationWidth k * (j : ℝ)) =
        sawtooth r (s * h.toFun x) from sawtooth_add_dyadic hkn _ _]
      rcases hs with rfl | rfl
      · rw [one_mul]
      · rw [neg_one_mul, sawtooth_neg]
    have ho : g.toFun x = 0 := notMem_support.mp (fun hx' ↦ hx (hgu (subset_closure hx')))
    rw [ho, sublevelRamp_eq_zero (show -1 + r ≤ 0 by linarith only [hn]),
      min_eq_right (sawtooth_nonneg _ _), min_eq_right (sawtooth_nonneg _ _)]
  rw [he]

theorem coreEnergyMeasure_eq_on_subset_of_eqOn_dyadic (f h : E.CompactCore) {A U : Set X}
    (hA : MeasurableSet A) (hU : IsOpen U) (hAU : A ⊆ U)
    (k : ℕ) (j : ℤ) (s : ℝ) (hs : s = 1 ∨ s = -1)
    (heq : EqOn f.toFun (fun x ↦ s * h.toFun x + oscillationWidth k * (j : ℝ)) U) :
    f.coreEnergyMeasure A = h.coreEnergyMeasure A := by
  rw [hA.measure_eq_iSup_isCompact f.coreEnergyMeasure, hA.measure_eq_iSup_isCompact h.coreEnergyMeasure]
  refine iSup_congr fun K ↦ iSup_congr fun hKA ↦ iSup_congr fun hK ↦ ?_
  exact f.coreEnergyMeasure_compact_eq_of_eqOn_dyadic h ⟨K, hK⟩ hU (hKA.trans hAU) k j s hs heq

end WalkDimensions.PEnergy.CompactCore
