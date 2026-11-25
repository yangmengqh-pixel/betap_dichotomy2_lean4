import WalkDimensions.TimedPaths
import Mathlib.MeasureTheory.Measure.Regular

/-!
# Finite approximations of the excursions into an open set of times
-/

open Filter Function MeasureTheory Set
open scoped ENNReal

namespace WalkDimensions

/-- A bounded open set of times is approximated in measure by finitely
many disjoint component intervals with endpoints outside it. -/
theorem exists_finset_excursions {U : Set ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hU : IsOpen U) (hUT : U ⊆ Ioo 0 T) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ s : Finset (ℝ × ℝ),
      (∀ i ∈ s, 0 ≤ i.1 ∧ i.1 < i.2 ∧ i.2 ≤ T ∧ i.1 ∉ U ∧ i.2 ∉ U ∧ Ioo i.1 i.2 ⊆ U) ∧
      (∀ i ∈ s, ∀ j ∈ s, i ≠ j → i.2 ≤ j.1 ∨ j.2 ≤ i.1) ∧
      volume (U \ ⋃ i ∈ s, Ioc i.1 i.2) < ε := by
  classical
  have hvol : volume U ≠ ∞ :=
    measure_ne_top_of_subset (hUT.trans Ioo_subset_Icc_self) isCompact_Icc.measure_lt_top.ne
  obtain ⟨K, hKU, hK, hApp⟩ := hU.measurableSet.exists_isCompact_sdiff_lt
    (μ := (volume : Measure ℝ)) hvol hε.ne'
  let P := {i : ℝ × ℝ | 0 ≤ i.1 ∧ i.1 < i.2 ∧ i.2 ≤ T ∧
    i.1 ∉ U ∧ i.2 ∉ U ∧ Ioo i.1 i.2 ⊆ U}
  have h₀ : (0 : ℝ) ∉ U := fun h ↦ lt_irrefl _ (hUT h).1
  have h₁ : T ∉ U := fun h ↦ lt_irrefl _ (hUT h).2
  have hIntervals (t : ℝ) (ht : t ∈ U) : ∃ i ∈ P, t ∈ Ioo i.1 i.2 := by
    let A := Uᶜ ∩ Icc 0 t
    let B := Uᶜ ∩ Icc t T
    have hA : IsCompact A := isCompact_Icc.inter_left hU.isClosed_compl
    have hB : IsCompact B := isCompact_Icc.inter_left hU.isClosed_compl
    have hAne : A.Nonempty := ⟨0, h₀, le_rfl, (hUT ht).1.le⟩
    have hBne : B.Nonempty := ⟨T, h₁, (hUT ht).2.le, le_rfl⟩
    let a := sSup A
    let b := sInf B
    have ha : a ∈ A := hA.sSup_mem hAne
    have hb : b ∈ B := hB.sInf_mem hBne
    have hat : a < t := lt_of_le_of_ne ha.2.2 (fun h ↦ ha.1 (h ▸ ht))
    have htb : t < b := lt_of_le_of_ne hb.2.1 (fun h ↦ hb.1 (h ▸ ht))
    refine ⟨(a, b), ⟨ha.2.1, hat.trans htb, hb.2.2, ha.1, hb.1, ?_⟩, ⟨hat, htb⟩⟩
    intro z hz
    by_contra hn
    rcases le_total z t with hzt | htz
    · have hzA : z ∈ A := ⟨hn, ha.2.1.trans hz.1.le, hzt⟩
      exact hz.1.not_ge (le_csSup hA.bddAbove hzA)
    · have hzB : z ∈ B := ⟨hn, htz, hz.2.le.trans hb.2.2⟩
      exact hz.2.not_ge (csInf_le hB.bddBelow hzB)
  have hCover : K ⊆ ⋃ i : P, Ioo i.val.1 i.val.2 := by
    intro t ht
    obtain ⟨i, hi, ht'⟩ := hIntervals t (hKU ht)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, ht'⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun i : P ↦ Ioo i.val.1 i.val.2) (fun _ ↦ isOpen_Ioo) hCover
  let s := t.image Subtype.val
  have hs (i : ℝ × ℝ) (hi : i ∈ s) : i ∈ P := by
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact j.property
  refine ⟨s, hs, ?_, hApp.trans_le' (measure_mono ?_)⟩
  · intro i hi j hj hne
    have hiP := hs i hi
    have hjP := hs j hj
    by_contra! hOverlap
    have hStart : i.1 = j.1 := by
      rcases lt_trichotomy i.1 j.1 with hlt | he | hgt
      · exact False.elim (hjP.2.2.2.1 (hiP.2.2.2.2.2 ⟨hlt, hOverlap.1⟩))
      · exact he
      · exact False.elim (hiP.2.2.2.1 (hjP.2.2.2.2.2 ⟨hgt, hOverlap.2⟩))
    have hEnd : i.2 = j.2 := by
      rcases lt_trichotomy i.2 j.2 with hlt | he | hgt
      · exact False.elim (hiP.2.2.2.2.1 (hjP.2.2.2.2.2 ⟨hOverlap.1, hlt⟩))
      · exact he
      · exact False.elim (hjP.2.2.2.2.1 (hiP.2.2.2.2.2 ⟨hOverlap.2, hgt⟩))
    exact hne (Prod.ext hStart hEnd)
  · apply sdiff_subset_sdiff_right
    intro z hz
    obtain ⟨i, hi, hz'⟩ := mem_iUnion₂.mp (ht hz)
    exact mem_iUnion₂.mpr ⟨i.val, Finset.mem_image.mpr ⟨i, hi, rfl⟩, Ioo_subset_Ioc_self hz'⟩

end WalkDimensions
