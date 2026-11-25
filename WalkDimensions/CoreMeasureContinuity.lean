import WalkDimensions.CoreEnergyMidpoint

/-!
# Setwise continuity of core energy measures

A compact subset accounts for almost all the limiting measure of a Borel
set. The local midpoint bound controls the mass of the discarded part.
-/

open Filter Function MeasureTheory Set TopologicalSpace
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy.CompactCore

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {p : ℝ} {E : PEnergy μ p}

private theorem tendsto_energy_of_root_sub {f : E.CompactCore} {g : ℕ → E.CompactCore}
    (hRoot : Tendsto (fun n ↦ E.rootSeminorm ((g n).domainElement - f.domainElement))
      atTop (𝓝 0)) :
    Tendsto (fun n ↦ (E.energy (g n).domainElement : ℝ))
      atTop (𝓝 (E.energy f.domainElement : ℝ)) := by
  have h (n : ℕ) : E.rootSeminorm (f.domainElement - (g n).domainElement) =
      E.rootSeminorm ((g n).domainElement - f.domainElement) := by
    rw [← neg_sub ((g n).domainElement) f.domainElement, map_neg_eq_map]
  have hRoot' : Tendsto (fun n ↦ E.rootSeminorm (f.domainElement - (g n).domainElement))
      atTop (𝓝 0) := by simpa only [h] using hRoot
  simpa only [sub_sub_cancel] using E.tendsto_energy_sub_of_root_tendsto_zero f.domainElement
    (fun n ↦ f.domainElement - (g n).domainElement) hRoot'

theorem coreEnergyMeasure_real_lt_eventually {f : E.CompactCore} {g : ℕ → E.CompactCore}
    (hLp : Tendsto (fun n ↦ ‖((g n).domainElement : RealLp μ p) -
      (f.domainElement : RealLp μ p)‖) atTop (𝓝 0))
    (hRoot : Tendsto (fun n ↦ E.rootSeminorm ((g n).domainElement - f.domainElement))
      atTop (𝓝 0)) {A : Set X} (hA : MeasurableSet A)
    {b : ℝ} (hb : (f.coreEnergyMeasure A).toReal < b) :
    ∀ᶠ n in atTop, ((g n).coreEnergyMeasure A).toReal < b := by
  let C := (2 : ℝ) ^ p
  have hC : 0 < C := Real.rpow_pos_of_pos (by norm_num) _
  let δ := (b - (f.coreEnergyMeasure A).toReal) / (C + 1)
  have hδ : 0 < δ := div_pos (sub_pos.mpr hb) (by positivity)
  obtain ⟨L, hLA, hL, hnear⟩ := hA.exists_isCompact_lt_add (μ := f.coreEnergyMeasure)
    (measure_ne_top _ _) (ENNReal.ofReal_ne_zero_iff.mpr hδ)
  let K : Compacts X := ⟨L, hL⟩
  have hLm : MeasurableSet L := hL.isClosed.measurableSet
  have hDiff : (f.coreEnergyMeasure (A \ L)).toReal < δ := by
    have h := (ENNReal.toReal_lt_toReal (measure_ne_top _ _)
      (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, ENNReal.ofReal_ne_top⟩)).mpr hnear
    rw [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hδ.le] at h
    rw [measure_diff hLA hLm.nullMeasurableSet (measure_ne_top _ _),
      ENNReal.toReal_sub_of_le (measure_mono hLA) (measure_ne_top _ _)]
    linarith only [h]
  let d (n : ℕ) := (g n).sub f
  have hd (n : ℕ) : (d n).domainElement = (g n).domainElement - f.domainElement := by
    change (g n).domainElement + -f.domainElement = _
    rw [sub_eq_add_neg]
  have hEt : Tendsto (fun n ↦ (E.energy (d n).domainElement : ℝ)) atTop (𝓝 0) := by
    have hR : Tendsto (fun n ↦ E.rootSeminorm (d n).domainElement) atTop (𝓝 0) := by
      simpa only [hd] using hRoot
    simpa only [← E.energy_eq_root_rpow, Real.zero_rpow (zero_lt_one.trans E.one_lt).ne'] using
      hR.rpow_const (Or.inr (zero_lt_one.trans E.one_lt).le)
  have hKevent := coreEnergyMeasure_compact_lt_eventually (f := f) (g := g)
    hLp hRoot K (lt_add_of_pos_right _ hδ)
  filter_upwards [hKevent, hEt.eventually_lt_const hδ] with n hn hnE
  have hEq : (g n).coreEnergyMeasure (A \ L) =
      (f.add (d n)).coreEnergyMeasure (A \ L) := by
    apply (g n).coreEnergyMeasure_eq_on_subset_of_eqOn (f.add (d n)) (hA.diff hLm)
      isOpen_univ (subset_univ _)
    intro x _
    change (g n).toFun x = f.toFun x + ((g n).toFun x - f.toFun x)
    ring
  have hBound : ((g n).coreEnergyMeasure (A \ L)).toReal ≤ C * δ := by
    rw [hEq]
    exact ((f.coreEnergyMeasure_add_le_two_pow_max (d n) (hA.diff hLm)).trans
      (mul_le_mul_of_nonneg_left (max_le hDiff.le (by
        apply le_trans _ hnE.le
        have h := ENNReal.toReal_mono (measure_ne_top (d n).coreEnergyMeasure univ)
          (measure_mono (μ := (d n).coreEnergyMeasure) (subset_univ (A \ L)))
        rwa [coreEnergyMeasure_univ, ENNReal.coe_toReal] at h)) hC.le))
  have hAdd :
      ((g n).coreEnergyMeasure A).toReal =
        ((g n).coreEnergyMeasure L).toReal + ((g n).coreEnergyMeasure (A \ L)).toReal := by
    rw [measure_diff hLA hLm.nullMeasurableSet (measure_ne_top _ _),
      ENNReal.toReal_sub_of_le (measure_mono hLA) (measure_ne_top _ _)]
    ring
  have hMon := ENNReal.toReal_mono (measure_ne_top f.coreEnergyMeasure A)
    (measure_mono (μ := f.coreEnergyMeasure) hLA)
  have hδeq : δ * (C + 1) = b - (f.coreEnergyMeasure A).toReal :=
    div_mul_cancel₀ _ (by positivity)
  change ((g n).coreEnergyMeasure L).toReal < (f.coreEnergyMeasure L).toReal + δ at hn
  rw [hAdd]
  nlinarith only [hn, hBound, hMon, hδeq]

theorem tendsto_coreEnergyMeasure_real {f : E.CompactCore} {g : ℕ → E.CompactCore}
    (hLp : Tendsto (fun n ↦ ‖((g n).domainElement : RealLp μ p) -
      (f.domainElement : RealLp μ p)‖) atTop (𝓝 0))
    (hRoot : Tendsto (fun n ↦ E.rootSeminorm ((g n).domainElement - f.domainElement))
      atTop (𝓝 0)) {A : Set X} (hA : MeasurableSet A) :
    Tendsto (fun n ↦ ((g n).coreEnergyMeasure A).toReal)
      atTop (𝓝 (f.coreEnergyMeasure A).toReal) := by
  apply tendsto_order.2
  refine ⟨fun b hb ↦ ?_, fun b hb ↦ coreEnergyMeasure_real_lt_eventually hLp hRoot hA hb⟩
  let δ := ((f.coreEnergyMeasure A).toReal - b) / 2
  have hδ : 0 < δ := half_pos (sub_pos.mpr hb)
  have hE := (tendsto_energy_of_root_sub hRoot).eventually_const_lt (sub_lt_self _ hδ)
  have hC := coreEnergyMeasure_real_lt_eventually hLp hRoot hA.compl
    (lt_add_of_pos_right _ hδ)
  filter_upwards [hE, hC] with n hn hn'
  have hEq (z : E.CompactCore) :
      (z.coreEnergyMeasure Aᶜ).toReal =
        (E.energy z.domainElement : ℝ) - (z.coreEnergyMeasure A).toReal := by
    rw [measure_compl hA (measure_ne_top _ _),
      ENNReal.toReal_sub_of_le (measure_mono (subset_univ _)) (measure_ne_top _ _),
      z.coreEnergyMeasure_univ, ENNReal.coe_toReal]
  rw [hEq (g n), hEq f] at hn'
  dsimp only [δ] at hn hn'
  linarith only [hn, hn']

theorem tendsto_localEnergyRoot {f : E.CompactCore} {g : ℕ → E.CompactCore}
    (hLp : Tendsto (fun n ↦ ‖((g n).domainElement : RealLp μ p) -
      (f.domainElement : RealLp μ p)‖) atTop (𝓝 0))
    (hRoot : Tendsto (fun n ↦ E.rootSeminorm ((g n).domainElement - f.domainElement))
      atTop (𝓝 0)) {A : Set X} (hA : MeasurableSet A) :
    Tendsto (fun n ↦ (g n).localEnergyRoot A) atTop (𝓝 (f.localEnergyRoot A)) :=
  (tendsto_coreEnergyMeasure_real hLp hRoot hA).rpow_const
    (Or.inr (inv_nonneg.mpr (zero_lt_one.trans E.one_lt).le))

end WalkDimensions.PEnergy.CompactCore
