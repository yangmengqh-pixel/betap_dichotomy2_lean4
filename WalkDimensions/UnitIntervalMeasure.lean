import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-!
# A characterization of Lebesgue measure on the unit interval

Lemma 3.7 of arXiv:2611.02422v1.
-/

open Filter MeasureTheory Set
open scoped ENNReal

namespace WalkDimensions

/-- A finite measure supported on ([0,1]) that annihilates the
derivatives of (C^1) functions vanishing at both endpoints is its
total mass times restricted Lebesgue measure. Endpoint derivatives
are taken within the closed interval. -/
theorem measure_eq_smul_volume_of_integral_derivWithin_eq_zero (μ : Measure ℝ)
    [IsFiniteMeasure μ] (hs : μ (Icc (0 : ℝ) 1)ᶜ = 0)
    (hann : ∀ φ : ℝ → ℝ, ContDiffOn ℝ 1 φ (Icc 0 1) → φ 0 = 0 → φ 1 = 0 →
      (∫ t, derivWithin φ (Icc 0 1) t ∂μ) = 0) :
    μ = μ univ • (volume.restrict (Icc (0 : ℝ) 1)) := by
  have : (μ univ • volume.restrict (Icc (0 : ℝ) 1)).Regular :=
    Measure.Regular.smul (measure_ne_top μ univ)
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  let a := ∫ t in (0 : ℝ)..1, f t
  let g : ℝ → ℝ := fun t ↦ f t - a
  let φ : ℝ → ℝ := fun t ↦ ∫ s in (0 : ℝ)..t, g s
  have hg : Continuous g := f.continuous.sub continuous_const
  have hd (t : ℝ) : HasDerivAt φ (g t) t := (hg.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hderiv : deriv φ = g := funext fun t ↦ (hd t).deriv
  have hdiff : ContDiff ℝ 1 φ :=
    contDiff_one_iff_deriv.2 ⟨fun t ↦ (hd t).differentiableAt, hderiv.symm ▸ hg⟩
  have hφ₀ : φ 0 = 0 := intervalIntegral.integral_same
  have hφ₁ : φ 1 = 0 := by
    have hf : IntervalIntegrable (fun t : ℝ ↦ f t) volume 0 1 :=
      f.continuous.intervalIntegrable 0 1
    have hc : IntervalIntegrable (fun _ : ℝ ↦ a) volume 0 1 := intervalIntegrable_const
    calc
      φ 1 = (∫ t in (0 : ℝ)..1, f t) - ∫ _ in (0 : ℝ)..1, a :=
        intervalIntegral.integral_sub hf hc
      _ = 0 := by simp [a]
  have hae : ∀ᵐ t ∂μ, t ∈ Icc (0 : ℝ) 1 := ae_iff.mpr hs
  have hzero : (∫ t, g t ∂μ) = 0 := by
    rw [← hann φ hdiff.contDiffOn hφ₀ hφ₁]
    apply integral_congr_ae
    filter_upwards [hae] with t ht
    exact ((hd t).hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc_zero_one t ht)).symm
  have hfi : Integrable (fun t ↦ f t) μ :=
    f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  rw [show (∫ t, g t ∂μ) = (∫ t, f t ∂μ) - μ.real univ * a by
    rw [integral_sub hfi (integrable_const a), integral_const, smul_eq_mul]] at hzero
  rw [integral_smul_measure, smul_eq_mul, ← Measure.real, ← sub_eq_zero]
  convert hzero using 3
  change (∫ x in Icc (0 : ℝ) 1, f x ∂volume) = ∫ x in (0 : ℝ)..1, f x
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]

end WalkDimensions
