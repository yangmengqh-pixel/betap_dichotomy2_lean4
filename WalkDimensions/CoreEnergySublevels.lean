import WalkDimensions.CoreEnergyMeasure
import WalkDimensions.ThinTruncation

/-!
# Sublevel values and localization of the core measure
-/

open Filter Function MeasureTheory Set TopologicalSpace
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy.CompactCore

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {p : ℝ} {E : PEnergy μ p}

theorem coreEnergyMeasure_sublevel (f g : E.CompactCore) (a : ℝ) :
    f.coreEnergyMeasure {x | g.toFun x ≤ a} = ENNReal.ofReal (f.sublevelDistribution g a) := by
  let S := tsupport f.toFun
  let A := {x | g.toFun x ≤ a}
  have hS : MeasurableSet S := isClosed_closure.measurableSet
  have hSnull : f.coreEnergyMeasure Sᶜ = 0 := by
    rw [measure_compl hS (measure_ne_top _ _), f.coreEnergyMeasure_univ, f.coreEnergyMeasure_tsupport,
      tsub_self]
  have hKA : IsCompact (S ∩ A) :=
    f.compactSupport.isCompact.inter_right (isClosed_le g.continuous continuous_const)
  have hnull : f.coreEnergyMeasure (A \ S) = 0 :=
    measure_mono_null (fun _ hx ↦ hx.2) hSnull
  have hcover : A ⊆ (S ∩ A) ∪ (A \ S) := by
    intro x hx
    by_cases hy : x ∈ S
    · exact Or.inl ⟨hy, hx⟩
    · exact Or.inr ⟨hx, hy⟩
  have he : f.coreEnergyMeasure A = f.coreEnergyMeasure (S ∩ A) := by
    apply le_antisymm _ (measure_mono inter_subset_right)
    exact (measure_mono hcover).trans ((measure_union_le _ _).trans_eq (by rw [hnull, add_zero]))
  let K : Compacts X := ⟨S ∩ A, hKA⟩
  obtain ⟨h, hh, _⟩ := E.exists_compactCore_sublevel_eq K.isCompact' isOpen_univ (subset_univ _)
  change f.coreEnergyMeasure A = _
  rw [he, show S ∩ A = (K : Set X) from rfl, f.coreEnergyMeasure_compact h K (-1) hh]
  congr 1
  apply le_antisymm
  · apply f.sublevelDistribution_le_of_sublevel_subset
    intro x _ hx
    change x ∈ {y | h.toFun y ≤ -1} at hx
    rw [hh] at hx
    exact hx.2
  · apply f.sublevelDistribution_le_of_sublevel_subset
    intro x hx hy
    change x ∈ {y | h.toFun y ≤ -1}
    rw [hh]
    exact ⟨hx, hy⟩

theorem coreEnergyMeasure_zeroLevel (f : E.CompactCore) :
    f.coreEnergyMeasure {x | f.toFun x = 0} = 0 := by
  let r (n : ℕ) := 1 / ((n : ℝ) + 1)
  have hr (n : ℕ) : 0 < r n := by dsimp [r]; positivity
  obtain ⟨v, hv, hV⟩ := E.exists_thin_truncations f.domainElement f.ae_eq f.compactSupport
  let V (n : ℕ) : E.CompactCore :=
    { domainElement := v n
      toFun := symmetricClip (r n) ∘ f.toFun
      ae_eq := hv n
      continuous := (symmetricClip_lipschitz (r n)).continuous.comp f.continuous
      compactSupport := f.compactSupport.comp_left (symmetricClip_zero (hr n).le) }
  have hroot : Tendsto (fun n ↦ E.rootSeminorm (v n)) atTop (𝓝 0) :=
    squeeze_zero (fun _ ↦ apply_nonneg _ _) (fun n ↦ E.rootSeminorm_le_graphSeminorm (v n)) hV
  have hp := zero_lt_one.trans E.one_lt
  have hmass : Tendsto (fun n ↦ (E.energy (v n) : ℝ≥0∞)) atTop (𝓝 0) := by
    have htend := ((Real.continuous_rpow_const hp.le).tendsto 0).comp hroot
    have he := ENNReal.tendsto_ofReal htend
    simpa only [Function.comp_def, Real.zero_rpow hp.ne', ENNReal.ofReal_zero,
      ← E.energy_eq_root_rpow, ENNReal.ofReal_coe_nnreal] using he
  apply le_antisymm _ zero_le
  apply ge_of_tendsto hmass
  refine Eventually.of_forall fun n ↦ ?_
  let U := {x | |f.toFun x| < r n}
  have hU : IsOpen U := isOpen_lt (continuous_abs.comp f.continuous) continuous_const
  have hZU : {x | f.toFun x = 0} ⊆ U := fun x hx ↦ by
    change |f.toFun x| < r n
    change f.toFun x = 0 at hx
    rw [hx, abs_zero]
    exact hr n
  have hEq : EqOn f.toFun (V n).toFun U := by
    intro x hx
    change |f.toFun x| < r n at hx
    have h := abs_lt.mp hx
    change f.toFun x = symmetricClip (r n) (f.toFun x)
    rw [symmetricClip, max_eq_left h.1.le, min_eq_left h.2.le]
  calc
    f.coreEnergyMeasure {x | f.toFun x = 0} ≤ f.coreEnergyMeasure U := measure_mono hZU
    _ = (V n).coreEnergyMeasure U := f.coreEnergyMeasure_eq_on_open (V n) hU hEq
    _ ≤ (V n).coreEnergyMeasure univ := measure_mono (subset_univ _)
    _ = (E.energy (v n) : ℝ≥0∞) := (V n).coreEnergyMeasure_univ

end WalkDimensions.PEnergy.CompactCore
