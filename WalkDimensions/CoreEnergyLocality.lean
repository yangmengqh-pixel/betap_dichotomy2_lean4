import WalkDimensions.CoreMeasureConvergence
import WalkDimensions.CorePotentialMeasure

/-!
# Locality on Borel sets

A thin correction makes the difference constant on an open neighbourhood
of each compact test set. Its value can be chosen dyadic, and the correction
vanishes in the graph norm.
-/

open Filter Function MeasureTheory Set TopologicalSpace
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy.CompactCore

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {p : ℝ} {E : PEnergy μ p}

set_option maxHeartbeats 500000 in
private theorem coreEnergyMeasure_compact_ge_of_eqOn_sub_const (f g : E.CompactCore)
    (K : Compacts X) {a : ℝ} (h : EqOn (fun x ↦ f.toFun x - g.toFun x) (fun _ ↦ a) K) :
    g.coreEnergyMeasure K ≤ f.coreEnergyMeasure K := by
  obtain ⟨U, hU, hKU, _, hC⟩ := exists_open_between_and_isCompact_closure
    K.isCompact' isOpen_univ (subset_univ _)
  obtain ⟨e, v, hv, hvC, hev, _, hv1, _⟩ :=
    E.exists_core_cutoff_of_isCompact_subset_isOpen hC isOpen_univ (subset_univ _)
  let w : E.CompactCore := ⟨e, v, hev, hv, hvC⟩
  let r := oscillationWidth
  let d := f.sub g
  let c (n : ℕ) := dyadicUpper a n - levelCorrectionCenter a n
  let z (n : ℕ) := (f.sub (d.levelCorrection a n)).add (w.smul (c n))
  have hc : Tendsto c atTop (𝓝 0) := by
    simpa only [c, sub_self] using ((tendsto_dyadicUpper a).mono_right nhdsWithin_le_nhds).sub
      (tendsto_levelCorrectionCenter a)
  have hE (n : ℕ) :
      (z n).domainElement - f.domainElement =
        c n • w.domainElement - (d.levelCorrection a n).domainElement := by
    change f.domainElement + -(d.levelCorrection a n).domainElement +
      c n • w.domainElement - f.domainElement = _
    abel
  have hZG : Tendsto (fun n ↦ E.graphSeminorm ((z n).domainElement - f.domainElement))
      atTop (𝓝 0) := by
    have hS : Tendsto (fun n ↦ |c n| * E.graphSeminorm w.domainElement) atTop (𝓝 0) := by
      simpa only [abs_zero, zero_mul] using hc.abs.mul_const (E.graphSeminorm w.domainElement)
    have hR := hS.add (d.tendsto_graph_levelCorrection a)
    rw [add_zero] at hR
    refine squeeze_zero (fun _ ↦ apply_nonneg _ _) (fun n ↦ ?_) hR
    rw [hE n]
    refine (map_sub_le_add E.graphSeminorm _ _).trans_eq ?_
    rw [map_smul_eq_mul, Real.norm_eq_abs]
  let err (n : ℕ) : E.domain := (z n).domainElement - f.domainElement
  have hGr : Tendsto (fun n ↦ E.graphSeminorm (err n)) atTop (𝓝 0) := hZG
  have hZroot : Tendsto (fun n ↦ E.rootSeminorm (err n)) atTop (𝓝 0) :=
    squeeze_zero (fun n ↦ apply_nonneg E.rootSeminorm (err n))
      (fun n ↦ E.rootSeminorm_le_graphSeminorm (err n)) hGr
  have hZLp : Tendsto (fun n ↦ ‖(err n : RealLp μ p)‖) atTop (𝓝 0) :=
    squeeze_zero (fun n ↦ show 0 ≤ ‖(err n : RealLp μ p)‖ from ENNReal.toReal_nonneg)
      (fun n ↦ E.norm_le_graphSeminorm (err n)) hGr
  have hEq (n : ℕ) : (z n).coreEnergyMeasure K = g.coreEnergyMeasure K := by
    let V := U ∩ {x | |d.toFun x - a| < r n}
    have hV : IsOpen V := hU.inter
      (isOpen_lt (continuous_abs.comp (d.continuous.sub continuous_const)) continuous_const)
    have hKV : (K : Set X) ⊆ V := by
      intro x hx
      refine ⟨hKU hx, ?_⟩
      have ha : d.toFun x = a := h hx
      change |d.toFun x - a| < r n
      rw [ha, sub_self, abs_zero]
      exact oscillationWidth_pos n
    let j : ℤ := ⌊a / r n⌋ + 1
    have hj : r n * (j : ℝ) = dyadicUpper a n := by simp only [j, r, dyadicUpper, Int.cast_add, Int.cast_one]
    apply (z n).coreEnergyMeasure_compact_eq_of_eqOn_dyadic g K hV hKV n j 1 (Or.inl rfl)
    intro x hx
    have hvx := hv1 (subset_closure hx.1)
    have hD := d.sub_levelCorrection_eq hx.2
    have hD' : d.toFun x = f.toFun x - g.toFun x := rfl
    change f.toFun x - (d.levelCorrection a n).toFun x + c n * v x =
      1 * g.toFun x + r n * (j : ℝ)
    rw [one_mul, hj, hvx, mul_one]
    rw [hD'] at hD
    dsimp only [c]
    linarith only [hD]
  by_contra! hgt
  have hto := (ENNReal.toReal_lt_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mpr hgt
  obtain ⟨n, hn⟩ := (coreEnergyMeasure_compact_lt_eventually (f := f) (g := z) hZLp hZroot K hto).exists
  rw [hEq n] at hn
  exact lt_irrefl _ hn

theorem coreEnergyMeasure_eq_of_eqOn_sub_const (f g : E.CompactCore)
    {A : Set X} (hA : MeasurableSet A) {a : ℝ}
    (h : EqOn (fun x ↦ f.toFun x - g.toFun x) (fun _ ↦ a) A) :
    f.coreEnergyMeasure A = g.coreEnergyMeasure A := by
  rw [hA.measure_eq_iSup_isCompact f.coreEnergyMeasure, hA.measure_eq_iSup_isCompact g.coreEnergyMeasure]
  refine iSup_congr fun K ↦ iSup_congr fun hKA ↦ iSup_congr fun hK ↦ ?_
  apply le_antisymm
  · apply g.coreEnergyMeasure_compact_ge_of_eqOn_sub_const f ⟨K, hK⟩ (a := -a)
    intro x hx
    have h' := h (hKA hx)
    change g.toFun x - f.toFun x = -a
    change f.toFun x - g.toFun x = a at h'
    linarith only [h']
  · exact f.coreEnergyMeasure_compact_ge_of_eqOn_sub_const g ⟨K, hK⟩ (h.mono hKA)

theorem coreEnergyMeasure_neg (f : E.CompactCore) : f.neg.coreEnergyMeasure = f.coreEnergyMeasure := by
  ext A hA
  exact f.neg.coreEnergyMeasure_eq_on_subset_of_eqOn_dyadic f hA isOpen_univ (subset_univ _) 0 0 (-1)
    (Or.inr rfl) (fun _ _ ↦ by simp [neg, Pi.neg_apply])

end WalkDimensions.PEnergy.CompactCore
