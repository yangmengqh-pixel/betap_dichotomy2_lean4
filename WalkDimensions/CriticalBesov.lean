import WalkDimensions.LargeScale
import WalkDimensions.SingularComparison

/-!
# The lower bound for the critical Besov exponent

Lemma 3.1(i) of arXiv:2611.02422v1 follows by testing a compactly
supported Lipschitz function.
-/

open MeasureTheory Metric Set
open scoped ENNReal NNReal

namespace WalkDimensions

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {m : Measure X} [ProperSpace X] [SecondCountableTopology X] [SFinite m]
  [IsFiniteMeasureOnCompacts m] [m.IsOpenPosMeasure]

theorem inBesov_one_of_lipschitz {p : ℝ} (hp : 0 < p) (hvol : VolumeDoubling m)
    {u : X → ℝ} {K : ℝ≥0} (hLip : LipschitzWith K u) (hc : HasCompactSupport u) :
    InBesov m p 1 u := by
  obtain ⟨D, _, hD⟩ := hvol
  let V := thickening 1 (tsupport u)
  have hVfin : m V ≠ ∞ := measure_ne_top_of_subset
    (thickening_subset_cthickening 1 (tsupport u))
    (IsCompact.measure_lt_top (μ := m) (hc.isCompact.cthickening (r := 1))).ne
  have hLp : MemLp u (ENNReal.ofReal p) m := hLip.continuous.memLp_of_hasCompactSupport hc
  have hmoment : (∫⁻ x, ENNReal.ofReal |u x| ^ p ∂m) < ∞ := by
    simpa only [← Real.eNorm_eq_ofReal_abs, ENNReal.toReal_ofReal hp.le] using
      lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top
        (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top hLp.eLpNorm_lt_top
  let L := (K : ℝ≥0∞) ^ p * m V
  let M := (2 : ℝ≥0∞) ^ p * (1 + ENNReal.ofReal D) * ∫⁻ x, ENNReal.ofReal |u x| ^ p ∂m
  have hLfin : L ≠ ∞ := ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.coe_ne_top) hVfin
  have hMfin : M ≠ ∞ := ENNReal.mul_ne_top (ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg hp.le (by norm_num))
    (ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, ENNReal.ofReal_ne_top⟩)) hmoment.ne
  refine ⟨hLp, lt_of_le_of_lt (iSup_le fun r ↦ ?_)
    (ENNReal.add_ne_top.mpr ⟨hLfin, hMfin⟩).lt_top⟩
  rw [mul_one]
  have hr : 0 < (r : ℝ) := r.property
  by_cases hr₁ : (r : ℝ) ≤ 1
  · apply le_trans _ (le_add_of_nonneg_right (bot_le : 0 ≤ M))
    rw [← besovEnergy_thickening_support hp zero_lt_one hr₁ u]
    have hbound (x : X) : ballMoment m p u r x ≤
        (K : ℝ≥0∞) ^ p * (ENNReal.ofReal r) ^ p := by
      have hpoint : ∀ᵐ y ∂normalizedBall m x r,
          ENNReal.ofReal |u x - u y| ^ p ≤ (K : ℝ≥0∞) ^ p * (ENNReal.ofReal r) ^ p := by
        have hpos : (normalizedBall m x r) (ball x r)ᶜ = 0 := by
          rw [normalizedBall, smul_apply, Measure.restrict_apply measurableSet_ball.compl,
            compl_inter_self, measure_empty, smul_zero]
        filter_upwards [ae_iff.mpr hpos] with y hy
        have hxy : dist x y ≤ (r : ℝ) := by
          rw [dist_comm]
          exact (mem_ball.mp (show y ∈ ball x r from hy)).le
        have h := (lipschitzWith_iff_dist_le_mul.mp hLip x y).trans
          (mul_le_mul_of_nonneg_left hxy K.coe_nonneg)
        rw [Real.dist_eq] at h
        apply (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal h) hp.le).trans_eq
        rw [ENNReal.ofReal_mul K.coe_nonneg, ENNReal.ofReal_coe_nnreal,
          ENNReal.mul_rpow_of_nonneg _ _ hp.le]
      calc
        _ ≤ ∫⁻ _ : X, (K : ℝ≥0∞) ^ p * (ENNReal.ofReal r) ^ p ∂normalizedBall m x r :=
          lintegral_mono_ae hpoint
        _ = _ := by rw [lintegral_const, normalizedBall_univ x hr, mul_one]
    have hpower : 0 < (ENNReal.ofReal (r : ℝ)) ^ p :=
      ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hr) ENNReal.ofReal_ne_top
    have hfin : (ENNReal.ofReal (r : ℝ)) ^ p ≠ ∞ :=
      ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.ofReal_ne_top
    unfold besovEnergy
    rw [ENNReal.rpow_neg]
    calc
      _ ≤ ((ENNReal.ofReal (r : ℝ)) ^ p)⁻¹ *
          (∫⁻ _ in V, (K : ℝ≥0∞) ^ p * (ENNReal.ofReal r) ^ p ∂m) :=
        mul_le_mul_of_nonneg_left (lintegral_mono hbound) bot_le
      _ = L := by
        rw [setLIntegral_const]
        calc
          _ = (((ENNReal.ofReal (r : ℝ)) ^ p)⁻¹ * (ENNReal.ofReal r) ^ p) * L := by
            dsimp only [L]
            ac_rfl
          _ = _ := by rw [ENNReal.inv_mul_cancel hpower.ne' hfin, one_mul]
  · apply le_trans _ (le_add_of_nonneg_left (bot_le : 0 ≤ L))
    have hlarge : 1 ≤ ENNReal.ofReal (r : ℝ) :=
      by simpa using ENNReal.ofReal_le_ofReal (le_of_lt (lt_of_not_ge hr₁))
    have hdrop : besovEnergy m p p univ u r ≤ besovEnergy m p 0 univ u r := by
      simp only [besovEnergy, neg_zero, ENNReal.rpow_zero, one_mul]
      exact mul_le_of_le_one_left' (ENNReal.rpow_le_one_of_one_le_of_neg hlarge (neg_neg_of_pos hp))
    exact hdrop.trans (besovEnergy_zero_scale_le_of_doubling hp.le hr hD hLip.continuous.measurable)

/-- The walk-space geometry supplies a nonconstant test function at the
first-order Besov exponent. -/
theorem one_le_criticalBesovExponent [Nonempty X] {p : ℝ}
    (hp : 0 < p) (hvol : VolumeDoubling m) (hunbounded : ¬ Bornology.IsBounded (univ : Set X)) :
    1 ≤ criticalBesovExponent m p := by
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  let u : X → ℝ := fun y ↦ max (1 - dist y x) 0
  have hLip : LipschitzWith 1 u := by
    have hdist : LipschitzWith 1 (fun y : X ↦ dist y x) := LipschitzWith.dist_left x
    have hdiff : LipschitzWith 1 (fun y : X ↦ 1 - dist y x) := by
      simpa only [zero_add] using (LipschitzWith.const (α := X) (1 : ℝ)).sub hdist
    exact hdiff.max_const _
  have hc : HasCompactSupport u := by
    apply HasCompactSupport.intro (isCompact_closedBall x 1)
    intro y hy
    exact max_eq_right (sub_nonpos.mpr (le_of_not_ge hy))
  have hx : u x = 1 := by simp [u]
  obtain ⟨y, hy⟩ : ∃ y : X, y ∉ closedBall x 1 := by
    by_contra! hall
    exact hunbounded ((isCompact_closedBall x 1).isBounded.subset (fun y _ ↦ hall y))
  have hy₀ : u y = 0 := max_eq_right (sub_nonpos.mpr (le_of_not_ge hy))
  have hnonconst : ¬ ∃ c : ℝ, u =ᵐ[m] fun _ ↦ c := by
    rintro ⟨c, h⟩
    have he := Measure.eq_of_ae_eq h hLip.continuous continuous_const
    exact one_ne_zero (hx.symm.trans ((congrFun he x).trans ((congrFun he y).symm.trans hy₀)))
  simpa only [ENNReal.ofReal_one] using le_criticalBesovExponent zero_lt_one
    (inBesov_one_of_lipschitz hp hvol hLip hc) hnonconst

end WalkDimensions
