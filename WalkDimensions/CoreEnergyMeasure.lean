import WalkDimensions.EnergyContent

/-!
# Mass and open-set locality of the core energy measure
-/

open Filter Function MeasureTheory Set TopologicalSpace
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy.CompactCore

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {p : ℝ} {E : PEnergy μ p}

omit [LocallyCompactSpace X] in
theorem sublevelDistribution_le_energy (f g : E.CompactCore) (a : ℝ) :
    f.sublevelDistribution g a ≤ (E.energy f.domainElement : ℝ) := by
  apply ge_of_tendsto (f.tendsto_sublevelDistribution_atTop g)
  exact (eventually_ge_atTop a).mono fun _ h ↦ (f.sublevelDistribution g).mono' h

theorem coreEnergyMeasure_compact_le_energy (f : E.CompactCore) (K : Compacts X) :
    f.coreEnergyMeasure K ≤ (E.energy f.domainElement : ℝ≥0∞) := by
  obtain ⟨g, hg, _⟩ := E.exists_compactCore_sublevel_eq K.isCompact' isOpen_univ (subset_univ _)
  rw [f.coreEnergyMeasure_compact g K (-1) hg, ← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal (f.sublevelDistribution_le_energy g (-1))

omit [LocallyCompactSpace X] in
theorem sublevelDistribution_eq_energy_of_tsupport_subset (f g : E.CompactCore) (a : ℝ)
    (hSub : tsupport f.toFun ⊆ {x | g.toFun x ≤ a}) :
    f.sublevelDistribution g a = (E.energy f.domainElement : ℝ) := by
  apply tendsto_nhds_unique_of_forall (f.tendsto_oscillation_energy g a) tendsto_const_nhds
  intro n
  let r := oscillationWidth n
  have hr := oscillationWidth_pos n
  obtain ⟨w, hw, hWE⟩ :=
    E.exists_sawtooth_energy_eq f.domainElement f.ae_eq f.continuous f.compactSupport hr
  have he : f.oscillation g a n = w := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [f.oscillation_ae g a n, hw] with x hx hy
    rw [hx, hy]
    change min (sawtooth r (f.toFun x)) (sublevelRamp r a (g.toFun x)) = sawtooth r (f.toFun x)
    by_cases h : x ∈ tsupport f.toFun
    · rw [sublevelRamp_eq_cap hr.le (hSub h), min_eq_left (sawtooth_le hr _)]
    · rw [notMem_support.mp (fun hz ↦ h (subset_closure hz)), sawtooth_zero,
        min_eq_left (sublevelRamp_nonneg _ _ _)]
  rw [he, hWE]

theorem coreEnergyMeasure_tsupport (f : E.CompactCore) :
    f.coreEnergyMeasure (tsupport f.toFun) = (E.energy f.domainElement : ℝ≥0∞) := by
  let K : Compacts X := ⟨tsupport f.toFun, f.compactSupport.isCompact⟩
  obtain ⟨g, hg, _⟩ := E.exists_compactCore_sublevel_eq K.isCompact' isOpen_univ (subset_univ _)
  change f.coreEnergyMeasure K = _
  rw [f.coreEnergyMeasure_compact g K (-1) hg,
    f.sublevelDistribution_eq_energy_of_tsupport_subset g (-1) (hg.symm ▸ subset_rfl),
    ENNReal.ofReal_coe_nnreal]

theorem coreEnergyMeasure_univ (f : E.CompactCore) :
    f.coreEnergyMeasure univ = (E.energy f.domainElement : ℝ≥0∞) := by
  apply le_antisymm
  · rw [isOpen_univ.measure_eq_iSup_isCompact f.coreEnergyMeasure]
    exact iSup_le fun K ↦ iSup_le fun _ ↦ iSup_le fun hK ↦
      f.coreEnergyMeasure_compact_le_energy ⟨K, hK⟩
  · rw [← f.coreEnergyMeasure_tsupport]
    exact measure_mono (subset_univ _)

instance (f : E.CompactCore) : IsFiniteMeasure f.coreEnergyMeasure :=
  ⟨by rw [f.coreEnergyMeasure_univ]; exact ENNReal.coe_lt_top⟩

theorem coreEnergyMeasure_compact_eq_of_eqOn (f h : E.CompactCore)
    (K : Compacts X) {U : Set X} (hU : IsOpen U) (hKU : (K : Set X) ⊆ U)
    (heq : EqOn f.toFun h.toFun U) :
    f.coreEnergyMeasure K = h.coreEnergyMeasure K := by
  obtain ⟨g, hg, hgu⟩ := E.exists_compactCore_sublevel_eq K.isCompact' hU hKU
  rw [f.coreEnergyMeasure_compact g K (-1) hg, h.coreEnergyMeasure_compact g K (-1) hg]
  congr 1
  apply tendsto_nhds_unique_of_eventuallyEq (f.tendsto_oscillation_energy g (-1))
    (h.tendsto_oscillation_energy g (-1))
  filter_upwards [tendsto_oscillationWidth.eventually_lt_const (show (0 : ℝ) < 1 by norm_num)]
    with n hn
  have he : f.oscillation g (-1) n = h.oscillation g (-1) n := by
    change (f.oscillationCore g (-1) n).domainElement = (h.oscillationCore g (-1) n).domainElement
    apply domainElement_eq_of_toFun_eq
    funext x
    let r := oscillationWidth n
    change min (sawtooth r (f.toFun x)) (sublevelRamp r (-1) (g.toFun x)) =
      min (sawtooth r (h.toFun x)) (sublevelRamp r (-1) (g.toFun x))
    by_cases hx : x ∈ U
    · rw [heq hx]
    have ho : g.toFun x = 0 := notMem_support.mp (fun hx' ↦ hx (hgu (subset_closure hx')))
    rw [ho, sublevelRamp_eq_zero (show -1 + r ≤ 0 by linarith only [hn]),
      min_eq_right (sawtooth_nonneg _ _), min_eq_right (sawtooth_nonneg _ _)]
  rw [he]

theorem coreEnergyMeasure_eq_on_open (f h : E.CompactCore) {U : Set X} (hU : IsOpen U)
    (heq : EqOn f.toFun h.toFun U) :
    f.coreEnergyMeasure U = h.coreEnergyMeasure U := by
  rw [hU.measure_eq_iSup_isCompact f.coreEnergyMeasure, hU.measure_eq_iSup_isCompact h.coreEnergyMeasure]
  refine iSup_congr fun K ↦ iSup_congr fun hKU ↦ iSup_congr fun hK ↦ ?_
  exact f.coreEnergyMeasure_compact_eq_of_eqOn h ⟨K, hK⟩ hU hKU heq

theorem coreEnergyMeasure_eq_on_subset_of_eqOn (f h : E.CompactCore) {A U : Set X}
    (hA : MeasurableSet A) (hU : IsOpen U) (hAU : A ⊆ U) (heq : EqOn f.toFun h.toFun U) :
    f.coreEnergyMeasure A = h.coreEnergyMeasure A := by
  rw [hA.measure_eq_iSup_isCompact f.coreEnergyMeasure, hA.measure_eq_iSup_isCompact h.coreEnergyMeasure]
  refine iSup_congr fun K ↦ iSup_congr fun hKA ↦ iSup_congr fun hK ↦ ?_
  exact f.coreEnergyMeasure_compact_eq_of_eqOn h ⟨K, hK⟩ hU (hKA.trans hAU) heq

end WalkDimensions.PEnergy.CompactCore
