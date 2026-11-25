import WalkDimensions.EnergyDerivativeProduct
import WalkDimensions.CoreEnergyLevels
import WalkDimensions.EnergyLocality

/-!
# Finite sums and truncation of compact-core cutoffs
-/

open Filter Function MeasureTheory Set
open scoped ENNReal

namespace WalkDimensions.PEnergy.CompactCore

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {m : Measure X} [IsFiniteMeasureOnCompacts m] {p : ℝ} {E : PEnergy m p}

noncomputable def finsetSum {ι : Type*} (t : Finset ι) (f : ι → E.CompactCore) : E.CompactCore where
  domainElement := ∑ i ∈ t, (f i).domainElement
  toFun x := ∑ i ∈ t, (f i).toFun x
  ae_eq := E.coeFn_finsetSum t (fun i ↦ (f i).domainElement) (fun i ↦ (f i).toFun)
    (fun i _ ↦ (f i).ae_eq)
  continuous := continuous_finsetSum _ (fun i _ ↦ (f i).continuous)
  compactSupport := by
    classical
    induction t using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact (HasCompactSupport.zero : HasCompactSupport (0 : X → ℝ))
    | insert i t hi ih =>
      simp only [Finset.sum_insert hi]
      exact (f i).compactSupport.add ih

noncomputable def minOne (f : E.CompactCore) : E.CompactCore :=
  f.mapLipschitz (fun a : ℝ ↦ min a 1) (LipschitzWith.id.min_const 1) (by norm_num)

@[simp] theorem minOne_apply (f : E.CompactCore) (x : X) : f.minOne.toFun x = min (f.toFun x) 1 := rfl

@[simp] theorem finsetSum_apply {ι : Type*} (t : Finset ι) (f : ι → E.CompactCore) (x : X) :
    (finsetSum t f).toFun x = ∑ i ∈ t, (f i).toFun x := rfl

variable [LocallyCompactSpace X]

theorem energyMeasure_apply_inter_of_support (f : E.CompactCore) {A B : Set X}
    (hB : MeasurableSet B) (hs : support f.toFun ⊆ B) :
    E.energyMeasure f.domainElement A = E.energyMeasure f.domainElement (A ∩ B) := by
  rw [E.energyMeasure_core f, ← measure_inter_add_sdiff A hB]
  have hs' : A \ B ⊆ {x | f.toFun x = 0} := fun x hx ↦
    notMem_support.mp (fun h ↦ hx.2 (hs h))
  rw [measure_mono_null hs' (f.coreEnergyMeasure_level 0), add_zero]

theorem energyMeasure_minOne_le (f : E.CompactCore) {A : Set X} (hA : MeasurableSet A) :
    E.energyMeasure f.minOne.domainElement A ≤ E.energyMeasure f.domainElement A := by
  let B := {x | f.toFun x ≤ 1}
  have hB : MeasurableSet B := (isClosed_le f.continuous continuous_const).measurableSet
  have hZ : f.minOne.coreEnergyMeasure (A \ B) = 0 := by
    apply measure_mono_null _ (f.minOne.coreEnergyMeasure_level 1)
    intro x hx
    change min (f.toFun x) 1 = 1
    exact min_eq_right (le_of_not_ge hx.2)
  have he : f.minOne.coreEnergyMeasure (A ∩ B) = f.coreEnergyMeasure (A ∩ B) := by
    apply f.minOne.coreEnergyMeasure_eq_of_eqOn_sub_const f (hA.inter hB) (a := 0)
    intro x hx
    change min (f.toFun x) 1 - f.toFun x = 0
    rw [min_eq_left hx.2, sub_self]
  rw [E.energyMeasure_core f.minOne, E.energyMeasure_core f,
    ← measure_inter_add_sdiff A hB (μ := f.minOne.coreEnergyMeasure), hZ, add_zero, he]
  exact measure_mono inter_subset_left

theorem energyMeasureRoot_minOne_le (f : E.CompactCore) {A : Set X} (hA : MeasurableSet A) :
    E.energyMeasureRoot A hA f.minOne.domainElement ≤ E.energyMeasureRoot A hA f.domainElement := by
  change E.energyMeasureLaws.root A hA f.minOne.domainElement ≤ E.energyMeasureLaws.root A hA f.domainElement
  rw [E.energyMeasureLaws.root_apply, E.energyMeasureLaws.root_apply, measureReal_def, measureReal_def]
  exact Real.rpow_le_rpow ENNReal.toReal_nonneg
    (ENNReal.toReal_mono (measure_ne_top _ _) (f.energyMeasure_minOne_le hA))
    (inv_nonneg.mpr (zero_lt_one.trans E.one_lt).le)

end WalkDimensions.PEnergy.CompactCore
