import WalkDimensions.ObstacleWeights
import WalkDimensions.PathSplicing

/-!
# Selecting and replacing a short obstacle excursion
-/

open Filter Function MeasureTheory Set
open scoped ENNReal

namespace WalkDimensions.TimedPath

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}
  {x y : X}

theorem exists_short_obstacle_level (γ : TimedPath x y) (g : X → ℝ≥0∞)
    {q T M τ B : ℝ} (hM : 0 < M) (hB : 0 ≤ B) {k : ℕ} (hk : 0 < k)
    (hγ : γ.cost (obstacleWeight m g q T M τ k) ≤ ENNReal.ofReal B) :
    ∃ i < k, volume (Ioc 0 γ.duration ∩ γ.toFun ⁻¹' obstacleSet m g q T M τ i) ≤
      ENNReal.ofReal (B / M ^ (i + 1)) := by
  let E (i : ℕ) := obstacleSet m g q T M τ i
  let V (i : ℕ) := Ioc 0 γ.duration ∩ γ.toFun ⁻¹' E i
  let F (i : ℕ) (t : ℝ) := (E i).indicator (fun _ ↦ ENNReal.ofReal (M ^ (i + 1))) (γ.toFun t)
  let A (i : ℕ) := M ^ (i + 1) * (volume (V i)).toReal
  have hF (i : ℕ) : Measurable (F i) :=
    (measurable_const.indicator (isOpen_obstacleSet g q T M τ i).measurableSet).comp γ.lipschitz.continuous.measurable
  have hVfin (i : ℕ) : volume (V i) ≠ ∞ :=
    measure_ne_top_of_subset inter_subset_left (by rw [Real.volume_Ioc]; finiteness)
  have hEq (i : ℕ) : (∫⁻ t in Ioc 0 γ.duration, F i t ∂volume) = ENNReal.ofReal (A i) := by
    have he : F i = (γ.toFun ⁻¹' E i).indicator (fun _ ↦ ENNReal.ofReal (M ^ (i + 1))) := by
      funext t
      by_cases ht : γ.toFun t ∈ E i <;> simp [F, ht]
    have hpre : MeasurableSet (γ.toFun ⁻¹' E i) :=
      (isOpen_obstacleSet g q T M τ i).measurableSet.preimage γ.lipschitz.continuous.measurable
    rw [he, lintegral_indicator hpre, setLIntegral_const, Measure.restrict_apply hpre, inter_comm,
      ← show volume (V i) = _ from rfl, ← ENNReal.ofReal_toReal (hVfin i),
      ← ENNReal.ofReal_mul (pow_nonneg hM.le _)]
  have hA₀ (i : ℕ) : 0 ≤ A i := by dsimp only [A]; positivity
  have hk₀ : (0 : ℝ) < k := by exact_mod_cast hk
  change (∫⁻ t in Ioc 0 γ.duration, ((k : ℝ≥0∞)⁻¹ : ℝ≥0∞) * ∑ i ∈ Finset.range k, F i t ∂volume) ≤ _ at hγ
  rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr (by exact_mod_cast hk.ne')),
    lintegral_finsetSum _ (fun i _ ↦ hF i)] at hγ
  simp_rw [hEq] at hγ
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ hA₀ i), ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_inv_of_pos hk₀, ← ENNReal.ofReal_mul (inv_nonneg.mpr hk₀.le),
    ENNReal.ofReal_le_ofReal_iff hB] at hγ
  have hSum : (∑ i ∈ Finset.range k, A i) ≤ (k : ℝ) * B := by
    rw [mul_comm, ← div_eq_mul_inv] at hγ
    exact ((div_le_iff₀ hk₀).mp hγ).trans_eq (mul_comm _ _)
  by_contra! hn
  have hN (i : ℕ) (hi : i ∈ Finset.range k) : B < A i := by
    have h := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top (hVfin i)).mpr (hn i (Finset.mem_range.mp hi))
    rw [ENNReal.toReal_ofReal (div_nonneg hB (pow_nonneg hM.le _))] at h
    exact ((div_lt_iff₀ (pow_pos hM (i + 1))).mp h).trans_eq (mul_comm _ _)
  have hlt := Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr hk.ne') hN
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, not_lt_of_ge hSum] using hlt

omit [MeasurableSpace X] [BorelSpace X] in
/-- Replace all but arbitrarily little time in an open obstacle, while
retaining the bound on the duration and cost of the replacement paths. -/
theorem exists_splice_of_open_obstacle (γ : TimedPath x y) (g : X → ℝ≥0∞) (hg : ∀ z, g z ≤ 1)
    {E : Set X} (hE : IsOpen E) (hx : x ∉ E) (hy : y ∉ E)
    {A K : ℝ≥0∞} (hOutside : ∀ z ∉ E, g z ≤ A)
    {L : ℝ} (hL : 0 ≤ L)
    (hReplace : ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ γ.duration →
      γ.toFun a ∉ E → γ.toFun b ∉ E →
      b - a ≤ (volume (Ioc 0 γ.duration ∩ γ.toFun ⁻¹' E)).toReal →
      ∃ w : TimedPath (γ.toFun a) (γ.toFun b),
        w.duration ≤ L * (b - a) ∧ w.cost g ≤ K * ENNReal.ofReal (b - a))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    let V := Ioc 0 γ.duration ∩ γ.toFun ⁻¹' E
    ∃ w : TimedPath x y, w.duration ≤ γ.duration + L * (volume V).toReal ∧
      w.cost g ≤ A * ENNReal.ofReal γ.duration + ε + K * volume V := by
  let V := Ioc 0 γ.duration ∩ γ.toFun ⁻¹' E
  let U := Ioo 0 γ.duration ∩ γ.toFun ⁻¹' E
  have hU : IsOpen U := isOpen_Ioo.inter (hE.preimage γ.lipschitz.continuous)
  have hUV : U = V := by
    ext t
    constructor
    · exact fun h ↦ ⟨Ioo_subset_Ioc_self h.1, h.2⟩
    · intro ⟨ht, htE⟩
      exact ⟨⟨ht.1, ht.2.lt_of_ne (fun he ↦ hy (by simpa only [mem_preimage, he, γ.target] using htE))⟩, htE⟩
  obtain ⟨s, hs, hdis, hεs⟩ := exists_finset_excursions γ.duration_nonneg hU inter_subset_left hε
  let W := ⋃ i ∈ s, Ioc i.1 i.2
  let W' := ⋃ i ∈ s, Ioo i.1 i.2
  have hW' : W' ⊆ V :=
    iUnion₂_subset fun i hi ↦ (hs i hi).2.2.2.2.2.trans (hUV ▸ subset_rfl)
  have hVolW : volume W ≤ volume V := by
    classical
    have h₀ : W ⊆ W' ∪ (↑(s.image Prod.snd) : Set ℝ) := by
      intro t ht
      obtain ⟨i, hi, hti⟩ := mem_iUnion₂.mp ht
      rcases hti.2.lt_or_eq with hlt | he
      · exact Or.inl (mem_iUnion₂.mpr ⟨i, hi, hti.1, hlt⟩)
      · exact Or.inr (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨i, hi, he.symm⟩))
    apply (measure_mono h₀).trans
    have hf : volume (↑(s.image Prod.snd) : Set ℝ) = 0 :=
      (Finset.finite_toSet _).measure_zero _
    exact (measure_union_le _ _).trans (by rw [hf, add_zero]; exact measure_mono hW')
  have hVfin : volume V ≠ ∞ :=
    measure_ne_top_of_subset inter_subset_left (by rw [Real.volume_Ioc]; finiteness)
  have hOutsideTime (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ γ.duration) (ht : t ∉ U) :
      γ.toFun t ∉ E := by
    intro h
    rcases eq_or_lt_of_le ht₀ with he | hpos
    · exact hx (by simpa only [← he, γ.source] using h)
    rcases ht₁.lt_or_eq with hlt | he
    · exact ht ⟨⟨hpos, hlt⟩, h⟩
    · exact hy (by simpa only [he, γ.target] using h)
  have hR (i : ℝ × ℝ) (hi : i ∈ s) :
      ∃ w : TimedPath (γ.toFun i.1) (γ.toFun i.2), w.duration ≤ L * (i.2 - i.1) ∧
        w.cost g ≤ K * ENNReal.ofReal (i.2 - i.1) := by
    obtain ⟨h₀, hlt, hT, hOut₁, hOut₂, hIn⟩ := hs i hi
    apply hReplace i.1 i.2 h₀ hlt hT (hOutsideTime i.1 h₀ (hlt.le.trans hT) hOut₁)
      (hOutsideTime i.2 (h₀.trans hlt.le) hT hOut₂)
    have h := ENNReal.toReal_mono hVfin (measure_mono (hIn.trans (hUV ▸ subset_rfl)))
    rwa [Real.volume_Ioo, ENNReal.toReal_ofReal (sub_nonneg.mpr hlt.le)] at h
  obtain ⟨w, hwT, hwC⟩ := γ.exists_splice g hL K s γ.duration_nonneg
    (fun i hi ↦ ⟨(hs i hi).1, (hs i hi).2.1, (hs i hi).2.2.1⟩) hdis hR
  have hRemain : (∫⁻ t in Ioc 0 γ.duration \ W, g (γ.toFun t) ∂volume) ≤
      A * ENNReal.ofReal γ.duration + ε := by
    let S := Ioc 0 γ.duration \ W
    have hWm : MeasurableSet W := MeasurableSet.biUnion (Finset.finite_toSet s).countable
      (fun _ _ ↦ measurableSet_Ioc)
    have hSm : MeasurableSet S := measurableSet_Ioc.diff hWm
    have hVm : MeasurableSet V := hUV ▸ hU.measurableSet
    have hPart : (volume.restrict S) = volume.restrict (S \ V) + volume.restrict (S ∩ V) := by
      have h := Measure.restrict_add_restrict_compl (μ := volume.restrict S) hVm
      rw [Measure.restrict_restrict hVm, Measure.restrict_restrict hVm.compl, inter_comm V S,
        inter_comm Vᶜ S, ← Set.sdiff_eq, add_comm] at h
      exact h.symm
    rw [hPart, lintegral_add_measure]
    apply add_le_add
    · calc
        _ ≤ ∫⁻ t in S \ V, A ∂volume := by
          apply setLIntegral_mono' (hSm.diff hVm)
          intro t ht
          apply hOutside
          intro he
          exact ht.2 ⟨ht.1.1, he⟩
        _ ≤ ∫⁻ t in Ioc 0 γ.duration, A ∂volume :=
          lintegral_mono_set (sdiff_subset.trans sdiff_subset)
        _ = _ := by rw [setLIntegral_const, Real.volume_Ioc, sub_zero]
    · apply (setLIntegral_mono' (hSm.inter hVm) (fun t _ ↦ hg _)).trans
        (le_of_lt (hεs.trans_le' ?_))
      rw [setLIntegral_const, one_mul]
      apply measure_mono
      exact fun t ht ↦ ⟨hUV.symm ▸ ht.2, ht.1.2⟩
  have hTransfer {a b c d : X} (ha : a = c) (hb : b = d)
      (w : TimedPath a b) {T : ℝ} {B : ℝ≥0∞} (hT : w.duration ≤ T) (hB : w.cost g ≤ B) :
      ∃ v : TimedPath c d, v.duration ≤ T ∧ v.cost g ≤ B := by
    subst c
    subst d
    exact ⟨w, hT, hB⟩
  apply hTransfer γ.source γ.target w
  · simpa only [sub_zero] using hwT.trans (add_le_add_right
      (mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hVfin hVolW) hL) _)
  · exact hwC.trans (add_le_add hRemain (mul_le_mul_of_nonneg_left hVolW bot_le))

end WalkDimensions.TimedPath
