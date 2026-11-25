import WalkDimensions.CoreEnergyDyadic
import WalkDimensions.SawtoothCells

/-!
# The local measure of an oscillation

A dyadic sawtooth agrees locally with an isometry away from its vertices.
The value sets at the vertices carry no energy for either function.
-/

open Filter Function MeasureTheory Set TopologicalSpace
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy.CompactCore

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {p : ℝ} {E : PEnergy μ p}

theorem coreEnergyMeasure_eq_of_eqOn_sawtooth_dyadic (f h : E.CompactCore)
    {A U : Set X} (hA : MeasurableSet A) (hU : IsOpen U) (hAU : A ⊆ U) (n : ℕ)
    (heq : EqOn h.toFun (sawtooth (oscillationWidth n) ∘ f.toFun) U) :
    h.coreEnergyMeasure A = f.coreEnergyMeasure A := by
  let r := oscillationWidth n
  have hr := oscillationWidth_pos n
  let O (i : ℤ × Bool) := U ∩ f.toFun ⁻¹' interior (sawtoothCell r i)
  let S (i : ℤ × Bool) := A ∩ O i
  have hO (i : ℤ × Bool) : IsOpen (O i) :=
    hU.inter (isOpen_interior.preimage f.continuous)
  have hS (i : ℤ × Bool) : MeasurableSet (S i) := hA.inter (hO i).measurableSet
  have hRestr (i : ℤ × Bool) :
      h.coreEnergyMeasure.restrict (S i) = f.coreEnergyMeasure.restrict (S i) := by
    ext B hB
    rw [Measure.restrict_apply hB, Measure.restrict_apply hB]
    apply h.coreEnergyMeasure_eq_on_subset_of_eqOn_dyadic f (hB.inter (hS i)) (hO i)
      (fun x hx ↦ hx.2.2) n (sawtoothOffsetIndex i) (sawtoothSign i) (sawtoothSign_eq i)
    intro x hx
    rw [heq hx.1]
    exact sawtooth_eq_affine_of_mem_cell hr (interior_subset hx.2)
  have hRestrUnion := Measure.restrict_iUnion_congr.2 hRestr
  let B := ⋃ i, S i
  have hB : MeasurableSet B := MeasurableSet.iUnion hS
  have hBeq : h.coreEnergyMeasure B = f.coreEnergyMeasure B := by
    simpa only [Measure.restrict_apply_univ, B] using
      congrArg (fun ν : Measure X ↦ ν univ) hRestrUnion
  have hmiss (x : X) (hx : x ∈ A \ B) : ∃ j : ℤ, f.toFun x = r * (j : ℝ) := by
    obtain ⟨i, hi⟩ := exists_mem_sawtoothCell hr (f.toFun x)
    rcases mem_interior_sawtoothCell_or_eq_grid i hi with hu | hu
    · exact (hx.2 (mem_iUnion.mpr ⟨i, hx.1, hAU hx.1, hu⟩)).elim
    · exact hu
  have hFnull : f.coreEnergyMeasure (A \ B) = 0 := by
    apply measure_mono_null (t := ⋃ j : ℤ, {x | f.toFun x = r * (j : ℝ)})
    · exact fun x hx ↦ mem_iUnion.mpr (hmiss x hx)
    · exact measure_iUnion_null fun j ↦ f.coreEnergyMeasure_level _
  have hHnull : h.coreEnergyMeasure (A \ B) = 0 := by
    apply measure_mono_null (t := {x | h.toFun x = 0} ∪ {x | h.toFun x = r})
    · intro x hx
      obtain ⟨j, hj⟩ := hmiss x hx
      have hh := heq (hAU hx.1)
      change h.toFun x = sawtooth r (f.toFun x) at hh
      rw [hj] at hh
      exact (sawtooth_of_grid hr j).imp (hh.trans ·) (hh.trans ·)
    · exact measure_union_null (h.coreEnergyMeasure_level 0) (h.coreEnergyMeasure_level r)
  have hBA : B ⊆ A := iUnion_subset fun _ ↦ inter_subset_left
  have hEq (ν : Measure X) (hn : ν (A \ B) = 0) : ν A = ν B := by
    apply le_antisymm _ (measure_mono hBA)
    have hAB : A ⊆ B ∪ (A \ B) := fun x hx ↦ by
      by_cases h : x ∈ B
      · exact Or.inl h
      · exact Or.inr ⟨hx, h⟩
    exact (measure_mono hAB).trans ((measure_union_le B (A \ B)).trans_eq (by rw [hn, add_zero]))
  rw [hEq _ hHnull, hEq _ hFnull, hBeq]

end WalkDimensions.PEnergy.CompactCore
