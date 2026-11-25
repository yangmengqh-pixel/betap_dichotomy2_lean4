import WalkDimensions.ChainPaths
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Group.LIntegral

/-!
# Unit-speed bounds and weighted costs on timed paths
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal NNReal Topology

namespace WalkDimensions

variable {X : Type*} [MetricSpace X]

/-- A connection of finite duration with speed bounded by one. -/
structure TimedPath (x y : X) where
  duration : ℝ
  duration_nonneg : 0 ≤ duration
  toFun : ℝ → X
  lipschitz : LipschitzWith 1 toFun
  source : toFun 0 = x
  target : toFun duration = y

namespace TimedPath

variable {x y z : X}

@[simp] noncomputable def refl (x : X) : TimedPath x x :=
  ⟨0, le_rfl, fun _ ↦ x, (LipschitzWith.const x).weaken zero_le_one, rfl, rfl⟩

theorem dist_le_duration (γ : TimedPath x y) : dist x y ≤ γ.duration := by
  simpa only [γ.target, γ.source, NNReal.coe_one, one_mul, Real.dist_eq,
    sub_zero, abs_of_nonneg γ.duration_nonneg, dist_comm x y] using
    γ.lipschitz.dist_le_mul γ.duration 0

theorem dist_source_le_of_mem (γ : TimedPath x y) {t : ℝ} (ht : t ∈ Icc 0 γ.duration) :
    dist (γ.toFun t) x ≤ t := by
  simpa only [γ.source, NNReal.coe_one, one_mul, Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
    using γ.lipschitz.dist_le_mul t 0

/-- A segment with its initial time moved to zero. -/
def segment (γ : TimedPath x y) {a b : ℝ} (hab : a ≤ b) :
    TimedPath (γ.toFun a) (γ.toFun b) where
  duration := b - a
  duration_nonneg := sub_nonneg.mpr hab
  toFun t := γ.toFun (t + a)
  lipschitz := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    simpa only [Real.dist_eq, add_sub_add_right_eq_sub] using γ.lipschitz.dist_le_mul (s + a) (t + a)
  source := by rw [zero_add]
  target := by rw [sub_add_cancel]

/-- Leave the first endpoint of the second path at the time of the first
endpoint of concatenation. -/
noncomputable def append (γ : TimedPath x y) (η : TimedPath y z) : TimedPath x z where
  duration := γ.duration + η.duration
  duration_nonneg := add_nonneg γ.duration_nonneg η.duration_nonneg
  toFun t := if t ≤ γ.duration then γ.toFun t else η.toFun (t - γ.duration)
  lipschitz := by
    apply LipschitzWith.of_dist_le_mul
    suffices h : ∀ s t : ℝ, s ≤ t → dist (if s ≤ γ.duration then γ.toFun s else η.toFun (s - γ.duration))
        (if t ≤ γ.duration then γ.toFun t else η.toFun (t - γ.duration)) ≤ t - s by
      intro s t
      simp only [NNReal.coe_one, one_mul, Real.dist_eq]
      rcases le_total s t with hst | hts
      · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hst)]
        exact h s t hst
      · rw [abs_of_nonneg (sub_nonneg.mpr hts), dist_comm]
        exact h t s hts
    intro s t hst
    by_cases h₁ : t ≤ γ.duration
    · rw [ite_eq_left (hst.trans h₁), ite_eq_left h₁]
      simpa only [NNReal.coe_one, one_mul, Real.dist_eq, abs_sub_comm s,
        abs_of_nonneg (sub_nonneg.mpr hst)] using γ.lipschitz.dist_le_mul s t
    · rw [ite_eq_right h₁]
      by_cases h₂ : s ≤ γ.duration
      · rw [ite_eq_left h₂]
        have ha : dist (γ.toFun s) y ≤ γ.duration - s := by
          simpa only [γ.target, NNReal.coe_one, one_mul, Real.dist_eq, abs_sub_comm s,
            abs_of_nonneg (sub_nonneg.mpr h₂)] using γ.lipschitz.dist_le_mul s γ.duration
        have hb : dist y (η.toFun (t - γ.duration)) ≤ t - γ.duration := by
          simpa only [η.source, NNReal.coe_one, one_mul, Real.dist_eq, abs_sub_comm (0 : ℝ),
            sub_zero, abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge h₁))] using
            η.lipschitz.dist_le_mul 0 (t - γ.duration)
        exact (dist_triangle _ y _).trans ((add_le_add ha hb).trans_eq (by ring))
      · rw [ite_eq_right h₂]
        have he : (s - γ.duration) - (t - γ.duration) = s - t := by ring
        simpa only [NNReal.coe_one, one_mul, Real.dist_eq, he, abs_sub_comm s,
          abs_of_nonneg (sub_nonneg.mpr hst)] using η.lipschitz.dist_le_mul (s - γ.duration) (t - γ.duration)
  source := by rw [ite_eq_left γ.duration_nonneg, γ.source]
  target := by
    by_cases hη : η.duration = 0
    · rw [hη, add_zero, ite_eq_left le_rfl, γ.target]
      exact η.source.symm.trans (hη ▸ η.target)
    · rw [ite_eq_right (by linarith only [lt_of_le_of_ne η.duration_nonneg (Ne.symm hη)]),
        add_sub_cancel_left, η.target]

/-- Weighted time integral, with one time endpoint omitted for additivity. -/
noncomputable def cost (γ : TimedPath x y) (g : X → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ t in Ioc 0 γ.duration, g (γ.toFun t) ∂volume

theorem cost_le_const (γ : TimedPath x y) {g : X → ℝ≥0∞} {M : ℝ≥0∞}
    (hg : ∀ t ∈ Ioc 0 γ.duration, g (γ.toFun t) ≤ M) :
    γ.cost g ≤ M * ENNReal.ofReal γ.duration := by
  apply (setLIntegral_mono' measurableSet_Ioc hg).trans_eq
  rw [setLIntegral_const, Real.volume_Ioc, sub_zero]

private theorem setLIntegral_Ioc_translate (g : ℝ → ℝ≥0∞) (a b c : ℝ) :
    (∫⁻ t in Ioc a b, g (t + c) ∂volume) = ∫⁻ t in Ioc (a + c) (b + c), g t ∂volume := by
  have hmap := (measurePreserving_add_right volume c).restrict_preimage (measurableSet_Ioc (a := a + c) (b := b + c))
  have hpre : (fun t : ℝ ↦ t + c) ⁻¹' Ioc (a + c) (b + c) = Ioc a b := by
    ext t
    simp only [mem_preimage, mem_Ioc, add_lt_add_iff_right, add_le_add_iff_right]
  change MeasurePreserving (fun t : ℝ ↦ t + c)
    (volume.restrict ((fun t : ℝ ↦ t + c) ⁻¹' Ioc (a + c) (b + c))) _ at hmap
  rw [hpre] at hmap
  exact hmap.lintegral_comp_emb (MeasurableEquiv.addRight c).measurableEmbedding g

theorem cost_segment (γ : TimedPath x y) {a b : ℝ} (hab : a ≤ b) (g : X → ℝ≥0∞) :
    (γ.segment hab).cost g = ∫⁻ t in Ioc a b, g (γ.toFun t) ∂volume := by
  simpa only [cost, segment, zero_add, sub_add_cancel, Function.comp_apply] using
    setLIntegral_Ioc_translate (g ∘ γ.toFun) 0 (b - a) a

theorem cost_append (γ : TimedPath x y) (η : TimedPath y z) (g : X → ℝ≥0∞) :
    (γ.append η).cost g = γ.cost g + η.cost g := by
  change (∫⁻ t in Ioc 0 (γ.duration + η.duration), g ((γ.append η).toFun t) ∂volume) = _
  rw [← Ioc_union_Ioc_eq_Ioc γ.duration_nonneg (le_add_of_nonneg_right η.duration_nonneg),
    Measure.restrict_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc, lintegral_add_measure]
  congr 1
  · apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with t ht
    change g (if t ≤ γ.duration then γ.toFun t else η.toFun (t - γ.duration)) = _
    rw [ite_eq_left ht.2]
  · calc
      _ = ∫⁻ t in Ioc γ.duration (γ.duration + η.duration), g (η.toFun (t - γ.duration)) ∂volume := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with t ht
        change g (if t ≤ γ.duration then γ.toFun t else η.toFun (t - γ.duration)) = _
        rw [ite_eq_right ht.1.not_ge]
      _ = η.cost g := by
        simpa only [cost, Function.comp_apply, ← sub_eq_add_neg, sub_self, add_sub_cancel_left]
          using setLIntegral_Ioc_translate (g ∘ η.toFun) γ.duration (γ.duration + η.duration) (-γ.duration)

end TimedPath

variable [ProperSpace X]

theorem ChainCondition.exists_timedPath (hCC : ChainCondition X) (x y : X) :
    ∃ γ : TimedPath x y, γ.duration = intrinsicDistance x y := by
  let T := intrinsicDistance x y
  have hT : 0 ≤ T := dist_nonneg.trans (dist_le_intrinsicDistance hCC x y)
  by_cases he : x = y
  · subst y
    exact ⟨TimedPath.refl x, (intrinsicDistance_self hCC x).symm⟩
  have hT₀ := (dist_pos.mpr he).trans_le (dist_le_intrinsicDistance hCC x y)
  change 0 < T at hT₀
  obtain ⟨θ, hθ⟩ := hCC.exists_lipschitz_path x y
  let q (t : ℝ) := projIcc (0 : ℝ) 1 zero_le_one (t / T)
  let γ (t : ℝ) := θ (q t)
  have hq (s t : ℝ) : |(q s : ℝ) - q t| ≤ |s - t| / T := by
    have h := (LipschitzWith.projIcc (show (0 : ℝ) ≤ 1 by norm_num)).dist_le_mul (s / T) (t / T)
    simpa only [Real.dist_eq, Subtype.dist_eq, NNReal.coe_one, one_mul, ← sub_div, abs_div,
      abs_of_pos hT₀] using h
  refine ⟨⟨T, hT, γ, LipschitzWith.of_dist_le_mul (fun s t ↦ ?_), ?_, ?_⟩, rfl⟩
  · simpa only [NNReal.coe_one, one_mul, Real.dist_eq] using ((hθ (q s) (q t)).trans
      ((mul_le_mul_of_nonneg_left (hq s t) hT).trans_eq (by field_simp [hT₀.ne'])))
  · change θ (projIcc (0 : ℝ) 1 zero_le_one (0 / T)) = _
    rw [zero_div, projIcc_of_mem _ (left_mem_Icc.mpr zero_le_one)]
    exact θ.source
  · change θ (projIcc (0 : ℝ) 1 zero_le_one (T / T)) = _
    rw [div_self hT₀.ne', projIcc_of_mem _ (right_mem_Icc.mpr zero_le_one)]
    exact θ.target

end WalkDimensions
