import WalkDimensions.TransportMassBounds
import WalkDimensions.ThinTruncation

/-!
# The signed energy derivative of a clipped local deviation
-/

open Filter Function MeasureTheory Set
open scoped ENNReal

namespace WalkDimensions.PEnergy.CompactCore

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [LocallyCompactSpace X] {m : Measure X} [IsFiniteMeasureOnCompacts m] {p : ℝ} {E : PEnergy m p}

noncomputable def clip (f : E.CompactCore) {a : ℝ} (ha : 0 ≤ a) : E.CompactCore :=
  f.mapLipschitz (symmetricClip a) (symmetricClip_lipschitz a) (symmetricClip_zero ha)

omit [LocallyCompactSpace X] in
@[simp] theorem clip_apply (f : E.CompactCore) {a : ℝ} (ha : 0 ≤ a) (x : X) :
    (f.clip ha).toFun x = symmetricClip a (f.toFun x) := rfl

theorem energyDerivativeMeasure_apply_eq_zero_of_const_on (u v : E.CompactCore)
    {S : Set X} (hS : MeasurableSet S) {c : ℝ} (hv : EqOn v.toFun (fun _ ↦ c) S) :
    E.energyDerivativeMeasure u.domainElement v.domainElement S = 0 := by
  let η := E.energyDerivativeMeasure u.domainElement v.domainElement
  have hzero : η.totalVariation S = 0 := u.energyDerivativeMeasure_variation_zero_of_const_on v hS hv
  have h := η.eNorm_measure_le_variation S
  rw [← η.totalVariation_eq_variation, hzero, Real.eNorm_eq_ofReal_abs,
    nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at h
  exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))

/-- On the band where a deviation is not clipped, its derivative is the
energy measure of the original function. The constant pieces contribute zero. -/
theorem energyDerivativeMeasure_restrict_clip (f v : E.CompactCore)
    {B : Set X} (hB : MeasurableSet B) {c a : ℝ} (ha : 0 ≤ a)
    (hv : EqOn v.toFun (fun x ↦ f.toFun x - c) B) :
    let S := {x | |f.toFun x - c| ≤ a}
    (E.energyDerivativeMeasure f.domainElement (v.clip ha).domainElement).restrict B =
      ((E.energyMeasure f.domainElement).restrict (B ∩ S)).toSignedMeasure := by
  let S := {x | |f.toFun x - c| ≤ a}
  let L := {x | f.toFun x - c < -a}
  let R := {x | a < f.toFun x - c}
  have hS : MeasurableSet S :=
    (isClosed_le (f.continuous.sub continuous_const).abs continuous_const).measurableSet
  have hL : MeasurableSet L :=
    (isOpen_lt (f.continuous.sub continuous_const) continuous_const).measurableSet
  have hR : MeasurableSet R :=
    (isOpen_lt continuous_const (f.continuous.sub continuous_const)).measurableSet
  let D := E.energyDerivativeMeasure f.domainElement (v.clip ha).domainElement
  let Γ := E.energyMeasure f.domainElement
  change D.restrict B = (Γ.restrict (B ∩ S)).toSignedMeasure
  ext A hA
  rw [VectorMeasure.restrict_apply D hB hA, Measure.toSignedMeasure_apply_measurable hA,
    measureReal_def, Measure.restrict_apply hA]
  let U := A ∩ B
  have hU := hA.inter hB
  have hInside : D (U ∩ S) = (Γ (U ∩ S)).toReal := by
    have hEq : EqOn (fun x ↦ (v.clip ha).toFun x - f.toFun x) (fun _ ↦ -c) (U ∩ S) := by
      intro x hx
      obtain ⟨hx₁, hx₂⟩ := abs_le.mp (show |f.toFun x - c| ≤ a from hx.2)
      change (v.clip ha).toFun x - f.toFun x = -c
      rw [clip_apply, hv hx.1.2, symmetricClip, max_eq_left hx₁, min_eq_left hx₂]
      ring
    have hM := E.energyDerivativeMeasure_eq_of_eqOn_sub_const f (v.clip ha) f (hU.inter hS) hEq
    exact hM.trans (E.energyDerivativeMeasure_self f.domainElement (hU.inter hS))
  have hNeg : D (U ∩ L) = 0 := by
    apply f.energyDerivativeMeasure_apply_eq_zero_of_const_on _ (hU.inter hL) (c := -a)
    intro x hx
    have hx' : f.toFun x - c < -a := hx.2
    rw [clip_apply, hv hx.1.2, symmetricClip, max_eq_right hx'.le, min_eq_left (by linarith)]
  have hPos : D (U ∩ R) = 0 := by
    apply f.energyDerivativeMeasure_apply_eq_zero_of_const_on _ (hU.inter hR) (c := a)
    intro x hx
    have hx' : a < f.toFun x - c := hx.2
    rw [clip_apply, hv hx.1.2, symmetricClip, max_eq_left (by linarith), min_eq_right hx'.le]
  have hLR : L ∪ R = Sᶜ := by
    ext x
    change f.toFun x - c < -a ∨ a < f.toFun x - c ↔ ¬ |f.toFun x - c| ≤ a
    rw [abs_le, not_and_or]
    simp only [not_le]
  have hdis : Disjoint (U ∩ L) (U ∩ R) := by
    apply disjoint_left.mpr
    intro x hx hy
    have h₁ : f.toFun x - c < -a := hx.2
    have h₂ : a < f.toFun x - c := hy.2
    linarith
  have hout := VectorMeasure.of_union (v := D) hdis (hU.inter hL) (hU.inter hR)
  rw [← inter_union_distrib_left, hLR, hNeg, hPos, zero_add] at hout
  have hdis' : Disjoint (U ∩ S) (U ∩ Sᶜ) := disjoint_compl_right.mono inter_subset_right inter_subset_right
  have he := VectorMeasure.of_union (v := D) hdis' (hU.inter hS) (hU.inter hS.compl)
  rw [← inter_union_distrib_left, union_compl_self, inter_univ, hInside, hout, add_zero] at he
  change D U = (Γ (A ∩ (B ∩ S))).toReal
  rwa [← inter_assoc]

end WalkDimensions.PEnergy.CompactCore
