import WalkDimensions.CoreEnergyMeasure

/-!
# Local energy bounded by the energy of an extension

On an open set where two functions differ by a constant, localizing the
first function is bounded by the full energy of the second.
-/

open Filter Function MeasureTheory Set TopologicalSpace
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy.CompactCore

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {p : ℝ} {E : PEnergy μ p}

theorem coreEnergyMeasure_compact_le_energy_of_ae_sub_const (f : E.CompactCore)
    (h : E.domain) {v : X → ℝ} (hv : (h : RealLp μ p) =ᵐ[μ] v)
    (K : Compacts X) {U : Set X} (hU : IsOpen U) (hKU : (K : Set X) ⊆ U)
    {c : ℝ} (heq : ∀ᵐ x ∂μ, x ∈ U → f.toFun x - v x = c) :
    f.coreEnergyMeasure K ≤ (E.energy h : ℝ≥0∞) := by
  obtain ⟨g, hg, hgu⟩ := E.exists_compactCore_sublevel_eq K.isCompact' hU hKU
  rw [f.coreEnergyMeasure_compact g K (-1) hg, ← ENNReal.ofReal_coe_nnreal, E.energy_eq_root_rpow]
  apply ENNReal.ofReal_le_ofReal
  change f.sublevelEnergyRoot g (-1) ^ p ≤ _
  apply Real.rpow_le_rpow (f.sublevelEnergyRoot_nonneg g (-1)) _ (zero_lt_one.trans E.one_lt).le
  have hlim : Tendsto (fun n ↦ E.rootSeminorm (g.ramp (oscillationWidth n) (-1)).domainElement +
      E.rootSeminorm h) atTop (𝓝 (E.rootSeminorm h)) := by
    simpa only [zero_add] using (g.tendsto_root_ramp (-1)).add_const (E.rootSeminorm h)
  apply le_of_tendsto_of_tendsto (f.tendsto_sublevelEnergyRoot g (-1)) hlim
  filter_upwards [tendsto_oscillationWidth.eventually_lt_const (show (0 : ℝ) < 1 by norm_num)]
    with n hn
  let r := oscillationWidth n
  let R := g.ramp r (-1)
  have hR₀ : sublevelRamp r (-1) 0 = 0 := sublevelRamp_eq_zero (by linarith only [hn])
  let φ (t : ℝ) := sawtooth r (t + c) - sawtooth r c
  have hφ : LipschitzWith 1 φ := by
    apply lipschitzWith_iff_dist_le_mul.mpr
    intro x y
    have hh := lipschitzWith_iff_dist_le_mul.mp (lipschitzWith_sawtooth r) (x + c) (y + c)
    simpa only [φ, Real.dist_eq, add_sub_add_right_eq_sub, sub_sub_sub_cancel_right] using hh
  have hφ₀ : φ 0 = 0 := by simp [φ]
  obtain ⟨H, hHref, hHE⟩ := E.exists_lipschitz_one_comp h hv φ hφ hφ₀
  have hH : E.rootSeminorm H ≤ E.rootSeminorm h := by
    rw [E.rootSeminorm_apply, E.rootSeminorm_apply]
    exact Real.rpow_le_rpow (NNReal.coe_nonneg _) (NNReal.coe_le_coe.mpr hHE)
      (inv_nonneg.mpr (zero_lt_one.trans E.one_lt).le)
  obtain ⟨V, hV, hVE⟩ := E.exists_min_add_const R.domainElement H R.ae_eq hHref (sawtooth_nonneg r c)
  have hEq : V = f.oscillation g (-1) n := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [hV, f.oscillation_ae g (-1) n, heq] with x hx hy hConst
    rw [hx, hy]
    change min (offsetRamp r (-1) (g.toFun x)) (φ (v x) + sawtooth r c) =
      min (sawtooth r (f.toFun x)) (sublevelRamp r (-1) (g.toFun x))
    dsimp only [φ]
    rw [offsetRamp, hR₀, sub_zero, sub_add_cancel, min_comm]
    by_cases hx : x ∈ U
    · have hh := hConst hx
      rw [sub_eq_iff_eq_add.mp hh, add_comm c]
    · have hzero : g.toFun x = 0 := notMem_support.mp (fun hy ↦ hx (hgu (subset_closure hy)))
      rw [hzero, hR₀, min_eq_right (sawtooth_nonneg _ _), min_eq_right (sawtooth_nonneg _ _)]
  change E.rootSeminorm (f.oscillation g (-1) n) ≤ E.rootSeminorm R.domainElement + _
  rw [← hEq]
  exact hVE.trans (add_le_add_right hH _)

theorem coreEnergyMeasure_open_le_energy_of_ae_sub_const (f : E.CompactCore)
    (h : E.domain) {v : X → ℝ} (hv : (h : RealLp μ p) =ᵐ[μ] v)
    {U : Set X} (hU : IsOpen U) {c : ℝ}
    (heq : ∀ᵐ x ∂μ, x ∈ U → f.toFun x - v x = c) :
    f.coreEnergyMeasure U ≤ (E.energy h : ℝ≥0∞) := by
  rw [hU.measure_eq_iSup_isCompact f.coreEnergyMeasure]
  exact iSup_le fun K ↦ iSup_le fun hKU ↦ iSup_le fun hK ↦
    f.coreEnergyMeasure_compact_le_energy_of_ae_sub_const h hv ⟨K, hK⟩ hU hKU heq

theorem coreEnergyMeasure_compact_le_energy_of_eqOn_sub_const (f h : E.CompactCore)
    (K : Compacts X) {U : Set X} (hU : IsOpen U) (hKU : (K : Set X) ⊆ U)
    {c : ℝ} (heq : EqOn (fun x ↦ f.toFun x - h.toFun x) (fun _ ↦ c) U) :
    f.coreEnergyMeasure K ≤ (E.energy h.domainElement : ℝ≥0∞) :=
  f.coreEnergyMeasure_compact_le_energy_of_ae_sub_const h.domainElement h.ae_eq K hU hKU
    (Eventually.of_forall fun _ hx ↦ heq hx)

theorem coreEnergyMeasure_open_le_energy_of_eqOn_sub_const (f h : E.CompactCore)
    {U : Set X} (hU : IsOpen U) {c : ℝ}
    (heq : EqOn (fun x ↦ f.toFun x - h.toFun x) (fun _ ↦ c) U) :
    f.coreEnergyMeasure U ≤ (E.energy h.domainElement : ℝ≥0∞) := by
  rw [hU.measure_eq_iSup_isCompact f.coreEnergyMeasure]
  exact iSup_le fun K ↦ iSup_le fun hKU ↦ iSup_le fun hK ↦
    f.coreEnergyMeasure_compact_le_energy_of_eqOn_sub_const h ⟨K, hK⟩ hU hKU heq

end WalkDimensions.PEnergy.CompactCore
