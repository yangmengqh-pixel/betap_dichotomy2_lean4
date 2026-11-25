import WalkDimensions.BallDifferentiation
import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv

/-!
# Uniform estimates on subsets at Radon–Nikodym density points
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal Topology

namespace WalkDimensions

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SecondCountableTopology X] {m : Measure X}
  [IsFiniteMeasureOnCompacts m] [m.IsOpenPosMeasure] [SigmaFinite m]

/-- At almost every point the finite measure is approximated by its density times
the volume, uniformly on measurable subsets of a shrinking ball. -/
theorem VolumeDoubling.ae_uniform_mass_tangent (hvol : VolumeDoubling m)
    (ν : Measure X) [IsFiniteMeasure ν] :
    ∀ᵐ x ∂m, ∀ ε > (0 : ℝ), ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ∀ S ⊆ ball x r, MeasurableSet S →
        |(ν S).toReal - (ν.rnDeriv m x).toReal * (m S).toReal| ≤ ε * (m (ball x r)).toReal := by
  have : IsUnifLocDoublingMeasure m := hvol.isUnifLocDoublingMeasure
  obtain ⟨D, hD, hVD⟩ := hvol
  let σ := ν.singularPart m
  let g (x : X) := (ν.rnDeriv m x).toReal
  have hg : Integrable g m := Measure.integrable_toReal_rnDeriv
  have hSing := Measure.mutuallySingular_singularPart ν m
  have hSingRN := hSing.rnDeriv_ae_eq_zero
  have hσ : ∀ᵐ x ∂m, Tendsto (fun r : ℝ ↦ σ (closedBall x r) / m (closedBall x r))
      (𝓝[>] 0) (𝓝 0) := by
    filter_upwards [(IsUnifLocDoublingMeasure.vitaliFamily m 1).ae_tendsto_rnDeriv σ, hSingRN] with x hx hy
    have ht := IsUnifLocDoublingMeasure.tendsto_closedBall_filterAt (K := 1) m
      (fun _ : ℝ ↦ x) id (l := 𝓝[>] (0 : ℝ)) tendsto_id (by
        filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi (0 : ℝ))] with r hr
        exact mem_closedBall_self (by simpa only [one_mul, id_eq] using (show 0 < r from hr).le))
    have h := hx.comp ht
    change Tendsto (fun r : ℝ ↦ σ (closedBall x r) / m (closedBall x r))
      (𝓝[>] 0) (𝓝 (σ.rnDeriv m x)) at h
    change σ.rnDeriv m x = 0 at hy
    rwa [hy] at h
  filter_upwards [hσ, IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub m hg.locallyIntegrable 1] with x hσx hx
  have hx' := hx (fun _ : ℝ ↦ x) id tendsto_id (by
    filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi (0 : ℝ))] with r hr
    exact mem_closedBall_self (by simpa only [one_mul, id_eq] using (show 0 < r from hr).le))
  change Tendsto (fun r : ℝ ↦ ⨍ y in closedBall x r, ‖g y - g x‖ ∂m) (𝓝[>] 0) (𝓝 0) at hx'
  intro ε hε
  let e := ε / (2 * D)
  have he : 0 < e := div_pos hε (mul_pos (by norm_num) hD)
  have hPos : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r := eventually_mem_nhdsWithin
  filter_upwards [hPos, hσx.eventually_lt_const (ENNReal.ofReal_pos.mpr he),
    hx'.eventually_lt_const he] with r hr hσsmall hgsmall
  let B := ball x r
  let C := closedBall x r
  have hBpos : 0 < m B := measure_ball_pos m _ hr
  have hCT : m C ≠ ∞ := measure_closedBall_lt_top.ne
  have hCpos : 0 < m C := hBpos.trans_le (measure_mono ball_subset_closedBall)
  have hCpos' : 0 < (m C).toReal := ENNReal.toReal_pos hCpos.ne' hCT
  have hCB : (m C).toReal ≤ D * (m B).toReal := by
    have h := (measure_mono (closedBall_subset_ball (show r < 2 * r by linarith)) :
      m C ≤ m (ball x (2 * r))).trans (hVD x r hr)
    have h' := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_ne_top) h
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hD.le] at h'
  have hσbound : (σ C).toReal ≤ e * (m C).toReal := by
    have h := (ENNReal.div_lt_iff (Or.inl hCpos.ne') (Or.inl hCT)).mp hσsmall
    have h' := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hCT) h.le
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal he.le] at h'
  have hGbound : (∫ y in C, |g y - g x| ∂m) ≤ e * (m C).toReal := by
    rw [setAverage_eq, smul_eq_mul, measureReal_def, inv_mul_eq_div] at hgsmall
    simp only [Real.norm_eq_abs] at hgsmall
    exact (div_lt_iff₀ hCpos').mp hgsmall |>.le
  intro S hSB hS
  have hSC := hSB.trans (ball_subset_closedBall : B ⊆ C)
  have hST : m S ≠ ∞ := measure_ne_top_of_subset hSC hCT
  have hA : ((m.withDensity (ν.rnDeriv m)) S).toReal = ∫ y in S, g y ∂m := by
    have ht := setIntegral_withDensity_eq_setIntegral_toReal_smul
      (Measure.measurable_rnDeriv ν m)
      (ae_restrict_of_ae (Measure.rnDeriv_lt_top ν m)) (fun _ : X ↦ (1 : ℝ)) hS
    simpa only [setIntegral_const, smul_eq_mul, mul_one, measureReal_def, g] using ht
  have hEq : (ν S).toReal = (σ S).toReal + ∫ y in S, g y ∂m := by
    rw [← hA, ← ENNReal.toReal_add (measure_ne_top σ S) (measure_ne_top _ S)]
    exact congrArg ENNReal.toReal (congrArg (fun η : Measure X ↦ η S) (Measure.haveLebesgueDecomposition_add ν m))
  rw [hEq]
  have hI : (∫ y in S, g y ∂m) - g x * (m S).toReal = ∫ y in S, g y - g x ∂m := by
    rw [integral_sub hg.integrableOn (integrableOn_const hST), setIntegral_const,
      smul_eq_mul, measureReal_def, mul_comm (m S).toReal]
  rw [add_sub_assoc, hI]
  have hGint : IntegrableOn (fun y ↦ |g y - g x|) C m := by
    change Integrable _ (m.restrict C)
    have hsub : IntegrableOn (fun y ↦ g y - g x) C m :=
      hg.integrableOn.sub (integrableOn_const hCT)
    simpa only [Real.norm_eq_abs] using hsub.norm
  have hSmon := ENNReal.toReal_mono (measure_ne_top σ C) (measure_mono hSC)
  calc
    _ ≤ (σ S).toReal + |∫ y in S, g y - g x ∂m| := by
      exact (abs_add_le _ _).trans_eq (by rw [abs_of_nonneg ENNReal.toReal_nonneg])
    _ ≤ (σ C).toReal + ∫ y in C, |g y - g x| ∂m := by
      apply add_le_add hSmon
      have hNorm := norm_integral_le_integral_norm (μ := m.restrict S) (fun y ↦ g y - g x)
      simp only [Real.norm_eq_abs] at hNorm
      exact hNorm.trans (setIntegral_mono_set hGint
        (Eventually.of_forall fun _ ↦ abs_nonneg _) (Eventually.of_forall hSC))
    _ ≤ e * (m C).toReal + e * (m C).toReal := add_le_add hσbound hGbound
    _ ≤ ε * (m B).toReal := by
      have h := mul_le_mul_of_nonneg_left hCB he.le
      have heD : e * D = ε / 2 := by dsimp only [e]; field_simp
      rw [← mul_assoc, heD] at h
      linarith only [h]

theorem VolumeDoubling.exists_uniform_mass_tangent_of_not_singular (hvol : VolumeDoubling m)
    (ν : Measure X) [IsFiniteMeasure ν] {U : Set X} (hU : MeasurableSet U)
    (h : ¬ (ν.restrict U).MutuallySingular m) :
    let κ := m.withDensity (ν.rnDeriv m)
    ∃ x ∈ U, ∃ a : ℝ, 0 < a ∧
      (∀ ε > (0 : ℝ), ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ S ⊆ ball x r, MeasurableSet S →
        |(ν S).toReal - a * (m S).toReal| ≤ ε * (m (ball x r)).toReal) ∧
      (∀ ε > (0 : ℝ), ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ S ⊆ ball x r, MeasurableSet S →
        |(κ S).toReal - a * (m S).toReal| ≤ ε * (m (ball x r)).toReal) := by
  let κ := m.withDensity (ν.rnDeriv m)
  have hPos : ¬ (∀ᵐ x ∂m, x ∈ U → ν.rnDeriv m x = 0) := by
    intro h₀
    apply h
    apply (Measure.rnDeriv_eq_zero _ _).mp
    filter_upwards [Measure.rnDeriv_restrict ν m hU, h₀] with x hx h₁
    change _ = 0
    rw [hx]
    by_cases hmem : x ∈ U
    · rw [indicator_of_mem hmem, h₁ hmem]
    · rw [indicator_of_notMem hmem]
  by_contra hcontra
  apply hPos
  filter_upwards [hvol.ae_uniform_mass_tangent ν, hvol.ae_uniform_mass_tangent κ,
    Measure.rnDeriv_withDensity m (Measure.measurable_rnDeriv ν m), Measure.rnDeriv_lt_top ν m]
    with x hx hxκ hEq hfin hmem
  by_contra hne
  have hEq' : κ.rnDeriv m x = ν.rnDeriv m x := hEq
  rw [hEq'] at hxκ
  exact hcontra ⟨x, hmem, (ν.rnDeriv m x).toReal, ENNReal.toReal_pos hne hfin.ne, hx, hxκ⟩

end WalkDimensions
