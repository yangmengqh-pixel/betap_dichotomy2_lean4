import WalkDimensions.ChainOscillation
import WalkDimensions.CoreCapacityCutoffs
import WalkDimensions.DensityTangents
import WalkDimensions.HarmonicBand

/-!
# Singularity of the energy measure on a region of harmonicity
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SecondCountableTopology X] {m : Measure X}
  [m.Regular] [m.IsOpenPosMeasure] [SFinite m]
  {p : ℝ} (E : PEnergy m p)

theorem harmonic_energyMeasure_restrict_mutuallySingular {β : ℝ}
    (hβ : p < β) (hvol : VolumeDoubling m) (hCC : ChainCondition X)
    (hPI : E.Poincare E.energyMeasure β) (hcap : E.CapacityUpperBound β)
    (f : E.domain) {U : Set X} (hU : IsOpen U)
    (hHarm : ∀ v : E.CompactCore, support v.toFun ⊆ U →
      E.energyDerivativeMeasure f v.domainElement univ = 0) :
    ((E.energyMeasure f).restrict U).MutuallySingular m := by
  by_contra hNot
  let ν := E.energyMeasure f
  let κ := m.withDensity (ν.rnDeriv m)
  have hκ : κ ≤ ν := Measure.withDensity_rnDeriv_le ν m
  have hκm : κ ≪ m := withDensity_absolutelyContinuous m _
  have : IsFiniteMeasure κ := isFiniteMeasure_of_le ν hκ
  obtain ⟨x, hx, a, ha, hν, hκTang⟩ :=
    hvol.exists_uniform_mass_tangent_of_not_singular ν hU.measurableSet hNot
  have hp := zero_lt_one.trans E.one_lt
  have hβ₀ := hp.trans hβ
  have hα : 0 < (p - 1) / p := div_pos (sub_pos.mpr E.one_lt) hp
  obtain ⟨C, A, hC, hA, hCut⟩ := E.exists_compact_core_cutoff_of_capacity hcap hvol
  obtain ⟨R₀, hR₀, hR₀U⟩ := Metric.isOpen_iff.mp hU x hx
  obtain ⟨D, hD, hVD⟩ := hvol
  let R := A + 1
  have hR : 0 < R := by dsimp [R]; linarith
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt R (show (1 : ℝ) < 2 by norm_num)
  let K := 2 * a * D ^ k
  have hK : 0 < K := by dsimp only [K]; positivity
  let L := 2 * K ^ ((p - 1) / p) * C ^ p⁻¹
  have hL : 0 < L := by dsimp only [L]; positivity
  let e := a / (4 * L)
  have he : 0 < e := by dsimp only [e]; positivity
  obtain ⟨s, hs, hsν⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (hν a ha)
  have hScale : ∀ᶠ r in 𝓝[>] (0 : ℝ), R * r ∈ Ioo (0 : ℝ) s ∧ A * r < R₀ := by
    filter_upwards [Ioo_mem_nhdsGT (lt_min (div_pos hs hR)
      (div_pos hR₀ (zero_lt_one.trans hA)))] with r hr
    refine ⟨⟨mul_pos hR hr.1, ?_⟩, ?_⟩
    · rw [mul_comm]
      exact (lt_div_iff₀ hR).mp (hr.2.trans_le (min_le_left _ _))
    · rw [mul_comm]
      exact (lt_div_iff₀ (zero_lt_one.trans hA)).mp (hr.2.trans_le (min_le_right _ _))
  let w := (Lp.aestronglyMeasurable (f : RealLp m p)).aemeasurable.mk (f : RealLp m p)
  have hw : Measurable w := (Lp.aestronglyMeasurable (f : RealLp m p)).aemeasurable.measurable_mk
  have hfw : (f : RealLp m p) =ᵐ[m] w :=
    (Lp.aestronglyMeasurable (f : RealLp m p)).aemeasurable.ae_eq_mk
  obtain ⟨r, hr, ⟨hrν, hrU⟩, hrκ, c, hc⟩ :=
    (eventually_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0)).and
    (hScale.and ((hκTang (a / 4) (by positivity)).and
      (E.eventually_exists_small_normalized_oscillation hβ ⟨D, hD, hVD⟩ hPI hCC f x ha hν
        (e ^ p / 4) (by positivity)))) |>.exists
  have hr₀ : 0 < r := hr
  let B := ball x r
  let Q := closedBall x (A * r)
  have hQB : B ⊆ Q := ball_subset_closedBall.trans
    (closedBall_subset_closedBall (le_mul_of_one_le_left hr₀.le hA.le))
  have hQU : Q ⊆ U := (closedBall_subset_ball hrU).trans hR₀U
  have hBpos : 0 < (m B).toReal :=
    ENNReal.toReal_pos (measure_ball_pos m x hr₀).ne' measure_ball_ne_top
  let T := ball x (R * r)
  have hQT : Q ⊆ T := closedBall_subset_ball (by dsimp [R]; linarith)
  have hVol : (m T).toReal ≤ D ^ k * (m B).toReal := by
    have h := (measure_mono (ball_subset_ball (mul_le_mul_of_nonneg_right hk.le hr₀.le)) :
      m T ≤ m (ball x ((2 : ℝ) ^ k * r))).trans (measure_ball_two_pow_le hVD x hr₀ k)
    have h' := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      measure_ball_ne_top) h
    rwa [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hD.le] at h'
  have hνQ : (ν Q).toReal ≤ K * (m B).toReal := by
    have h : (ν Q).toReal - a * (m Q).toReal ≤ a * (m T).toReal :=
      (abs_le.mp (hsν hrν Q hQT isClosed_closedBall.measurableSet)).2
    have h' := ENNReal.toReal_mono measure_ball_ne_top (measure_mono (μ := m) hQT)
    have h'' := mul_le_mul_of_nonneg_left h' ha.le
    have h''' := mul_le_mul_of_nonneg_left hVol (show 0 ≤ 2 * a by positivity)
    dsimp only [K]
    nlinarith only [h, h'', h''']
  obtain ⟨χ, hχ, hχ₁, hχSupp, hχE⟩ := hCut x r hr₀
  let t := e * r ^ (β / p)
  have ht : 0 < t := by dsimp only [t]; positivity
  let W := {y | |w y - c| < t}
  let S := B ∩ W
  have hW : MeasurableSet W :=
    measurableSet_lt (continuous_abs.measurable.comp (hw.sub measurable_const)) measurable_const
  have hS : MeasurableSet S := measurableSet_ball.inter hW
  have hUpper := E.ac_mass_in_band_le_of_harmonic hw hfw χ (isCompact_closedBall _ _)
    measurableSet_ball hQB hχ hχ₁ (subset_closure.trans (hχSupp.trans ball_subset_closedBall))
    (fun v hv ↦ hHarm v (hv.trans hQU)) κ hκ hκm c ht
  have hRoot : E.rootSeminorm χ.domainElement ≤ (C * r ^ (-β) * (m B).toReal) ^ p⁻¹ := by
    rw [E.rootSeminorm_apply]
    exact Real.rpow_le_rpow (NNReal.coe_nonneg _) hχE (inv_nonneg.mpr hp.le)
  have hUpper' : (κ S).toReal ≤ a / 4 * (m B).toReal := by
    apply hUpper.trans
    calc
      _ ≤ 2 * t * (K * (m B).toReal) ^ ((p - 1) / p) *
          (C * r ^ (-β) * (m B).toReal) ^ p⁻¹ := by
        gcongr
      _ = a / 4 * (m B).toReal := by
        have hpExp : (p - 1) / p + p⁻¹ = 1 := by field_simp; ring
        have hrExp : β / p + (-β) * p⁻¹ = 0 := by ring
        have heL : e * L = a / 4 := by dsimp only [e]; field_simp
        dsimp only [t]
        rw [Real.mul_rpow hK.le hBpos.le, Real.mul_rpow (by positivity) hBpos.le,
          Real.mul_rpow hC.le (Real.rpow_nonneg hr₀.le _), ← Real.rpow_mul hr₀.le]
        calc
          _ = (e * L) * (r ^ (β / p) * r ^ (-β * p⁻¹)) *
              ((m B).toReal ^ ((p - 1) / p) * (m B).toReal ^ p⁻¹) := by
            dsimp only [L]
            ring
          _ = _ := by
            rw [heL, ← Real.rpow_add hr₀, hrExp, Real.rpow_zero, mul_one,
              ← Real.rpow_add hBpos, hpExp, Real.rpow_one]
  have hBad : (m (B \ W)).toReal ≤ (m B).toReal / 4 := by
    have hPow : t ^ p = e ^ p * r ^ β := by
      dsimp only [t]
      rw [Real.mul_rpow he.le (by positivity), ← Real.rpow_mul hr₀.le, div_mul_cancel₀ _ hp.ne']
    have h₁ : ENNReal.ofReal (t ^ p) * m (B \ W) ≤
        ∫⁻ y in B, ENNReal.ofReal |w y - c| ^ p ∂m := by
      rw [← setLIntegral_const]
      apply (setLIntegral_mono' (measurableSet_ball.diff hW) (fun y hy ↦ ?_)).trans
        (lintegral_mono_set diff_subset)
      rw [← ENNReal.ofReal_rpow_of_pos ht]
      exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (le_of_not_gt hy.2)) hp.le
    have h₂ : (∫⁻ y in B, ENNReal.ofReal |w y - c| ^ p ∂m) ≤
        ENNReal.ofReal (e ^ p / 4 * r ^ β) * m B := by
      refine LE.le.trans_eq ?_ rfl
      convert hc using 1
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_of_ae (s := B) hfw] with y hy
      rw [hy]
    have h₃ := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_ne_top)
      (h₁.trans h₂)
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofReal (by positivity)] at h₃
    apply (le_of_mul_le_mul_left _ (show 0 < t ^ p by positivity))
    convert h₃ using 1
    rw [hPow]
    ring
  have hMass : (m B).toReal = (m S).toReal + (m (B \ W)).toReal := by
    have h₀ : m B = m S + m (B \ W) := by
      simpa only [S, inter_comm] using (measure_inter_add_sdiff B hW (μ := m)).symm
    rw [h₀, ENNReal.toReal_add (measure_ne_top_of_subset inter_subset_left measure_ball_ne_top)
      (measure_ne_top_of_subset diff_subset measure_ball_ne_top)]
  have hmS : 3 / 4 * (m B).toReal ≤ (m S).toReal := by linarith only [hMass, hBad]
  have hLower := (abs_le.mp (hrκ S inter_subset_left hS)).1
  nlinarith only [hLower, hUpper', mul_le_mul_of_nonneg_left hmS ha.le, mul_pos ha hBpos]

end WalkDimensions.PEnergy
