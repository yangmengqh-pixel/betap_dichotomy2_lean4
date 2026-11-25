import WalkDimensions.CoreEnergyScaling
import WalkDimensions.ClarksonComplements

/-!
# Localized Clarkson estimates

On each pair of affine cells the two sums and differences agree, up to
sign and additive constants, with the original sum and difference.
-/

open Filter Function MeasureTheory Set TopologicalSpace
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy.CompactCore

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {p : ℝ} {E : PEnergy μ p}

noncomputable def pairMeasure (f g : E.CompactCore) : Measure X :=
  (f.add g).coreEnergyMeasure + (f.sub g).coreEnergyMeasure

private theorem pairMeasure_eq_of_eqOn_affines (f g v w : E.CompactCore)
    {A : Set X} (hA : MeasurableSet A) {s t a b : ℝ} (hs : s = 1 ∨ s = -1)
    (ht : t = 1 ∨ t = -1) (hv : EqOn v.toFun (fun x ↦ s * f.toFun x + a) A)
    (hw : EqOn w.toFun (fun x ↦ t * g.toFun x + b) A) :
    v.pairMeasure w A = f.pairMeasure g A := by
  have he (x : X) (hx : x ∈ A) :
      (v.add w).toFun x = s * f.toFun x + t * g.toFun x + (a + b) := by
    change v.toFun x + w.toFun x = _
    rw [hv hx, hw hx]
    ring
  have hd (x : X) (hx : x ∈ A) :
      (v.sub w).toFun x = s * f.toFun x - t * g.toFun x + (a - b) := by
    change v.toFun x - w.toFun x = _
    rw [hv hx, hw hx]
    ring
  have hSame (hst : s = t) :
      (v.add w).coreEnergyMeasure A = (f.add g).coreEnergyMeasure A ∧
      (v.sub w).coreEnergyMeasure A = (f.sub g).coreEnergyMeasure A := by
    constructor
    · apply (v.add w).coreEnergyMeasure_eq_of_eqOn_affine (f.add g) hA hs (c := a + b)
      intro x hx
      change (v.add w).toFun x = s * (f.toFun x + g.toFun x) + (a + b)
      rw [he x hx, ← hst, mul_add]
    · apply (v.sub w).coreEnergyMeasure_eq_of_eqOn_affine (f.sub g) hA hs (c := a - b)
      intro x hx
      change (v.sub w).toFun x = s * (f.toFun x - g.toFun x) + (a - b)
      rw [hd x hx, ← hst, mul_sub]
  have hOpp (hst : t = -s) :
      (v.add w).coreEnergyMeasure A = (f.sub g).coreEnergyMeasure A ∧
      (v.sub w).coreEnergyMeasure A = (f.add g).coreEnergyMeasure A := by
    constructor
    · apply (v.add w).coreEnergyMeasure_eq_of_eqOn_affine (f.sub g) hA hs (c := a + b)
      intro x hx
      change (v.add w).toFun x = s * (f.toFun x - g.toFun x) + (a + b)
      rw [he x hx, hst, mul_sub, neg_mul, sub_eq_add_neg]
    · apply (v.sub w).coreEnergyMeasure_eq_of_eqOn_affine (f.add g) hA hs (c := a - b)
      intro x hx
      change (v.sub w).toFun x = s * (f.toFun x + g.toFun x) + (a - b)
      rw [hd x hx, hst, mul_add, neg_mul, sub_neg_eq_add]
  have signs : s = t ∨ t = -s := by
    rcases hs with hs' | hs' <;> rcases ht with ht' | ht' <;> simp [hs', ht']
  simp only [pairMeasure, Measure.coe_add, Pi.add_apply]
  rcases signs with h | h
  · rw [(hSame h).1, (hSame h).2]
  · rw [(hOpp h).1, (hOpp h).2, add_comm]

theorem pairMeasure_eq_of_eqOn_sawtooths (f g v w : E.CompactCore)
    {A : Set X} (hA : MeasurableSet A) {r : ℝ} (hr : 0 < r)
    (hv : EqOn v.toFun (sawtooth r ∘ f.toFun) A)
    (hw : EqOn w.toFun (sawtooth r ∘ g.toFun) A) :
    v.pairMeasure w A = f.pairMeasure g A := by
  let S (i : (ℤ × Bool) × (ℤ × Bool)) :=
    A ∩ (f.toFun ⁻¹' sawtoothCell r i.1 ∩ g.toFun ⁻¹' sawtoothCell r i.2)
  have hS (i) : MeasurableSet (S i) := hA.inter
    (((isClosed_sawtoothCell r i.1).measurableSet.preimage f.continuous.measurable).inter
      ((isClosed_sawtoothCell r i.2).measurableSet.preimage g.continuous.measurable))
  have hRestr (i) : (v.pairMeasure w).restrict (S i) = (f.pairMeasure g).restrict (S i) := by
    ext B hB
    rw [Measure.restrict_apply hB, Measure.restrict_apply hB]
    apply pairMeasure_eq_of_eqOn_affines f g v w (hB.inter (hS i))
      (sawtoothSign_eq i.1) (sawtoothSign_eq i.2) (a := r * (sawtoothOffsetIndex i.1 : ℝ))
      (b := r * (sawtoothOffsetIndex i.2 : ℝ))
    · intro x hx
      rw [hv hx.2.1]
      exact sawtooth_eq_affine_of_mem_cell hr hx.2.2.1
    · intro x hx
      rw [hw hx.2.1]
      exact sawtooth_eq_affine_of_mem_cell hr hx.2.2.2
  have hUnion : (⋃ i, S i) = A := by
    apply le_antisymm (iUnion_subset fun _ ↦ inter_subset_left)
    intro x hx
    obtain ⟨i, hi⟩ := exists_mem_sawtoothCell hr (f.toFun x)
    obtain ⟨j, hj⟩ := exists_mem_sawtoothCell hr (g.toFun x)
    exact mem_iUnion.mpr ⟨(i, j), hx, hi, hj⟩
  have hEq := Measure.restrict_iUnion_congr.2 hRestr
  rw [hUnion] at hEq
  simpa only [Measure.restrict_apply_univ] using congrArg (fun ν : Measure X ↦ ν univ) hEq

theorem oscillationCore_eq_sawtooth_on_sublevel (f g : E.CompactCore) (a : ℝ) (n : ℕ) :
    EqOn (f.oscillationCore g a n).toFun (sawtooth (oscillationWidth n) ∘ f.toFun)
      {x | g.toFun x ≤ a} := by
  intro x hx
  have hr := oscillationWidth_pos n
  change min (sawtooth (oscillationWidth n) (f.toFun x))
    (sublevelRamp (oscillationWidth n) a (g.toFun x)) = _
  rw [sublevelRamp_eq_cap hr.le (show g.toFun x ≤ a from hx), min_eq_left (sawtooth_le hr _)]
  rfl

theorem pairMeasure_univ (f g : E.CompactCore) :
    f.pairMeasure g univ =
      (E.energy (f.domainElement + g.domainElement) : ℝ≥0∞) +
        (E.energy (f.domainElement - g.domainElement) : ℝ≥0∞) := by
  simp only [pairMeasure, Measure.coe_add, Pi.add_apply, coreEnergyMeasure_univ, add, sub,
    neg, ← sub_eq_add_neg]

end WalkDimensions.PEnergy.CompactCore
