import WalkDimensions.OpenTimeIntervals

/-!
# Replacing finitely many disjoint time intervals of a path
-/

open Filter Function MeasureTheory Set
open scoped ENNReal

namespace WalkDimensions.TimedPath

variable {X : Type*} [MetricSpace X] {x y : X}

private theorem disjoint_Ioc_of_separated {i j : ℝ × ℝ}
    (h : i.2 ≤ j.1 ∨ j.2 ≤ i.1) : Disjoint (Ioc i.1 i.2) (Ioc j.1 j.2) := by
  rcases h with h | h
  · exact Ioc_disjoint_Ioc_of_le h
  · exact (Ioc_disjoint_Ioc_of_le h).symm

/-- Replace disjoint, ordered intervals, charging the new paths to the
total time spent on the replaced intervals. -/
theorem exists_splice (γ : TimedPath x y) (g : X → ℝ≥0∞) {L : ℝ} (hL : 0 ≤ L)
    (K : ℝ≥0∞) (s : Finset (ℝ × ℝ)) {a b : ℝ} (hab : a ≤ b)
    (hI : ∀ i ∈ s, a ≤ i.1 ∧ i.1 < i.2 ∧ i.2 ≤ b)
    (hdis : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → i.2 ≤ j.1 ∨ j.2 ≤ i.1)
    (hReplace : ∀ i ∈ s, ∃ w : TimedPath (γ.toFun i.1) (γ.toFun i.2),
      w.duration ≤ L * (i.2 - i.1) ∧ w.cost g ≤ K * ENNReal.ofReal (i.2 - i.1)) :
    let U := ⋃ i ∈ s, Ioc i.1 i.2
    ∃ w : TimedPath (γ.toFun a) (γ.toFun b),
      w.duration ≤ b - a + L * (volume U).toReal ∧
        w.cost g ≤ (∫⁻ t in Ioc a b \ U, g (γ.toFun t) ∂volume) + K * volume U := by
  classical
  induction s using Finset.strongInductionOn generalizing a with
  | _ s ih =>
    by_cases hs : s.Nonempty
    · obtain ⟨i, hi, hmin⟩ := s.exists_min_image Prod.fst hs
      let t := s.erase i
      have ht : t ⊂ s := Finset.erase_ssubset hi
      have hts : t ⊆ s := ht.le
      have hi' := hI i hi
      have hiBefore (j : ℝ × ℝ) (hj : j ∈ t) : i.2 ≤ j.1 := by
        have hne := (Finset.mem_erase.mp hj).1
        exact (hdis i hi j (hts hj) hne.symm).resolve_right
          (fun h ↦ (hmin j (hts hj)).not_gt ((hI j (hts hj)).2.1.trans_le h))
      obtain ⟨w, hwT, hwC⟩ := hReplace i hi
      let U := ⋃ j ∈ t, Ioc j.1 j.2
      have hUmeas : MeasurableSet U := MeasurableSet.biUnion (Finset.finite_toSet t).countable (fun _ _ ↦ measurableSet_Ioc)
      obtain ⟨v, hvT, hvC⟩ := ih t ht (a := i.2) hi'.2.2
        (fun j hj ↦ ⟨hiBefore j hj, (hI j (hts hj)).2⟩)
        (fun j hj k hk ↦ hdis j (hts hj) k (hts hk))
        (fun j hj ↦ hReplace j (hts hj))
      change v.duration ≤ b - i.2 + L * (volume U).toReal at hvT
      change v.cost g ≤ (∫⁻ r in Ioc i.2 b \ U, g (γ.toFun r) ∂volume) + K * volume U at hvC
      let V := ⋃ j ∈ s, Ioc j.1 j.2
      have hV : V = Ioc i.1 i.2 ∪ U := by
        dsimp only [V, U, t]
        conv_lhs => rw [← Finset.insert_erase hi]
        simp only [Finset.set_biUnion_insert]
      have hUV : U ⊆ Ioc i.2 b := by
        intro r hr
        obtain ⟨j, hj, hrt⟩ := mem_iUnion₂.mp hr
        exact ⟨(hiBefore j hj).trans_lt hrt.1, hrt.2.trans (hI j (hts hj)).2.2⟩
      have hvolU : volume U ≠ ∞ :=
        measure_ne_top_of_subset hUV (by rw [Real.volume_Ioc]; finiteness)
      have hDisUV : Disjoint (Ioc i.1 i.2) U :=
        (Ioc_disjoint_Ioc_of_le le_rfl).mono_right hUV
      have hvolV : volume V = ENNReal.ofReal (i.2 - i.1) + volume U := by
        rw [hV, measure_union hDisUV hUmeas, Real.volume_Ioc]
      have hRemain : Ioc a b \ V = Ioc a i.1 ∪ (Ioc i.2 b \ U) := by
        rw [hV]
        ext r
        simp only [Set.mem_sdiff, mem_union, mem_Ioc]
        constructor
        · rintro ⟨⟨ha, hb⟩, h⟩
          by_cases hr : r ≤ i.1
          · exact Or.inl ⟨ha, hr⟩
          · exact Or.inr ⟨⟨lt_of_not_ge (fun hr' ↦ h (Or.inl ⟨lt_of_not_ge hr, hr'⟩)), hb⟩,
              fun hu ↦ h (Or.inr hu)⟩
        · rintro (⟨ha, hi⟩ | ⟨⟨hi, hb⟩, hu⟩)
          · exact ⟨⟨ha, hi.trans (hi'.2.1.le.trans hi'.2.2)⟩,
              fun h ↦ h.elim (fun hj ↦ hj.1.not_ge hi)
              (fun hv ↦ (hUV hv).1.not_ge (hi.trans hi'.2.1.le))⟩
          · exact ⟨⟨(hi'.1.trans hi'.2.1.le).trans_lt hi, hb⟩,
              fun h ↦ h.elim (fun hj ↦ hi.not_ge hj.2) hu⟩
      refine ⟨((γ.segment hi'.1).append w).append v, ?_, ?_⟩
      · change i.1 - a + w.duration + v.duration ≤ b - a + L * (volume V).toReal
        rw [hvolV, ENNReal.toReal_add ENNReal.ofReal_ne_top hvolU,
          ENNReal.toReal_ofReal (sub_nonneg.mpr hi'.2.1.le)]
        linarith only [hwT, hvT, hi'.2.1]
      · change (((γ.segment hi'.1).append w).append v).cost g ≤
          (∫⁻ r in Ioc a b \ V, g (γ.toFun r) ∂volume) + K * volume V
        rw [cost_append, cost_append, cost_segment, hRemain,
          Measure.restrict_union ((Ioc_disjoint_Ioc_of_le hi'.2.1.le).mono_right sdiff_subset)
            (measurableSet_Ioc.diff hUmeas), lintegral_add_measure, hvolV, mul_add]
        exact (add_le_add (add_le_add_right hwC _) hvC).trans_eq (by ac_rfl)
    · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      subst s
      refine ⟨γ.segment hab, ?_, ?_⟩
      · simp [segment]
      · simp [cost_segment]

end WalkDimensions.TimedPath
