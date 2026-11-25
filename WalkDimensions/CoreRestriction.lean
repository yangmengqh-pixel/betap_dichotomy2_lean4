import WalkDimensions.CoreEnergyMeasure

/-!
# Cutting a core function along a separated open region
-/

open Filter Function MeasureTheory Set
open scoped ENNReal

namespace WalkDimensions.PEnergy.CompactCore

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {p : ℝ} {E : PEnergy μ p}

omit [LocallyCompactSpace X] in
theorem exists_core_mul (f g : E.CompactCore) :
    ∃ w : E.CompactCore, w.toFun = f.toFun * g.toFun := by
  have hF : MemLp (f.domainElement : RealLp μ p) ∞ μ :=
    (f.continuous.memLp_of_hasCompactSupport (p := ∞) f.compactSupport).ae_eq f.ae_eq.symm
  have hG : MemLp (g.domainElement : RealLp μ p) ∞ μ :=
    (g.continuous.memLp_of_hasCompactSupport (p := ∞) g.compactSupport).ae_eq g.ae_eq.symm
  obtain ⟨w, hw, _⟩ := E.algebra f.domainElement g.domainElement hF.eLpNorm_lt_top hG.eLpNorm_lt_top
  have hae : (w : RealLp μ p) =ᵐ[μ] f.toFun * g.toFun := by
    filter_upwards [hw, f.ae_eq, g.ae_eq] with x hx hf hg
    rw [hx, hf, hg, Pi.mul_apply]
  exact ⟨⟨w, _, hae, f.continuous.mul g.continuous, f.compactSupport.mul_right⟩, rfl⟩

theorem exists_core_restrict_of_compact_support_inter (f : E.CompactCore) {U : Set X}
    (hU : IsOpen U) (hK : IsCompact (tsupport f.toFun ∩ U)) :
    ∃ w : E.CompactCore, w.toFun = U.indicator f.toFun ∧ tsupport w.toFun ⊆ U ∧
      E.energy w.domainElement ≤ E.energy f.domainElement := by
  classical
  obtain ⟨g, u, hu, huc, hgu, _, hu₁, hUs⟩ :=
    E.exists_core_cutoff_of_isCompact_subset_isOpen hK hU inter_subset_right
  let G : E.CompactCore := ⟨g, u, hgu, hu, huc⟩
  obtain ⟨w, hw⟩ := f.exists_core_mul G
  have hs : tsupport w.toFun ⊆ tsupport u := by
    apply closure_mono
    intro x hx
    by_contra hy
    have hz : u x = 0 := notMem_support.mp hy
    apply hx
    rw [hw, Pi.mul_apply]
    change f.toFun x * u x = 0
    rw [hz, mul_zero]
  have hwU : tsupport w.toFun ⊆ U := hs.trans hUs
  have he : w.toFun = U.indicator f.toFun := by
    funext x
    by_cases hx : x ∈ U
    · rw [indicator_of_mem hx, hw, Pi.mul_apply]
      change f.toFun x * u x = f.toFun x
      by_cases hx' : x ∈ tsupport f.toFun
      · rw [hu₁ ⟨hx', hx⟩, mul_one]
      · rw [notMem_support.mp (fun hz ↦ hx' (subset_closure hz)), zero_mul]
    · rw [indicator_of_notMem hx]
      exact notMem_support.mp (fun hz ↦ hx (hwU (subset_closure hz)))
  have hlocal : w.coreEnergyMeasure U = f.coreEnergyMeasure U :=
    w.coreEnergyMeasure_eq_on_open f hU (fun x hx ↦ by rw [he, indicator_of_mem hx])
  have henergy : (E.energy w.domainElement : ℝ≥0∞) ≤ (E.energy f.domainElement : ℝ≥0∞) := by
    calc
      _ = w.coreEnergyMeasure (tsupport w.toFun) := w.coreEnergyMeasure_tsupport.symm
      _ ≤ w.coreEnergyMeasure U := measure_mono hwU
      _ = f.coreEnergyMeasure U := hlocal
      _ ≤ f.coreEnergyMeasure univ := measure_mono (subset_univ _)
      _ = _ := f.coreEnergyMeasure_univ
  exact ⟨w, he, hwU, ENNReal.coe_le_coe.mp henergy⟩

end WalkDimensions.PEnergy.CompactCore
