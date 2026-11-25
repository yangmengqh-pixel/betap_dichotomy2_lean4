import WalkDimensions.UnitIntervalMeasure
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# First variation of the capacitary pushforward

The differentiation step in the proof of (3.6) in arXiv:2611.02422v1.
-/

open Filter MeasureTheory Set Metric
open scoped Topology ENNReal

namespace WalkDimensions

private theorem integral_eq_zero_of_power_perturbation_min {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {g : X → ℝ} {B p : ℝ} (hp : 1 < p)
    (hg : AEStronglyMeasurable g μ) (hB : 0 ≤ B) (hbounded : ∀ᵐ x ∂μ, |g x| ≤ B)
    (hmin : ∀ ε : ℝ, μ.real univ ≤ ∫ x, |1 + ε * g x| ^ p ∂μ) :
    (∫ x, g x ∂μ) = 0 := by
  let F := fun ε : ℝ ↦ fun x : X ↦ |1 + ε * g x| ^ p
  let G := fun ε : ℝ ↦ fun x : X ↦ p * (1 + ε * g x) ^ (p - 1) * g x
  let δ := 1 / (2 * (B + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hϵ (ε : ℝ) (hε : ε ∈ ball (0 : ℝ) δ) (x : X) (hx : |g x| ≤ B) :
      0 < 1 + ε * g x ∧ 1 + ε * g x ≤ 3 / 2 := by
    have hε' : |ε| < δ := by simpa only [mem_ball, Real.dist_eq, sub_zero] using hε
    have hprod : |ε * g x| ≤ δ * B := by
      rw [abs_mul]
      exact mul_le_mul hε'.le hx (abs_nonneg _) hδ.le
    have hδB : δ * B ≤ 1 / 2 := by
      dsimp only [δ]
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ (by positivity : 0 < 2 * (B + 1))).2
      linarith
    have h := abs_le.mp (hprod.trans hδB)
    exact ⟨by linarith only [h.1], by linarith only [h.2]⟩
  have hdiff : ∀ᵐ x ∂μ, ∀ ε ∈ ball (0 : ℝ) δ, HasDerivAt (F · x) (G ε x) ε := by
    filter_upwards [hbounded] with x hx
    intro ε hε
    have hpos := (hϵ ε hε x hx).1
    have href : HasDerivAt (fun t : ℝ ↦ 1 + t * g x) (g x) ε := by
      simpa only [id_eq, one_mul, zero_add] using
        (((hasDerivAt_id ε).mul_const (g x)).const_add 1)
    have hd := href.rpow_const (p := p) (Or.inl hpos.ne')
    have he : (fun t : ℝ ↦ (1 + t * g x) ^ p) =ᶠ[𝓝 ε] (fun t ↦ F t x) := by
      have hn : ∀ᶠ t : ℝ in 𝓝 ε, 0 < 1 + t * g x :=
        (continuous_const.add (continuous_id.mul continuous_const)).continuousAt.eventually
          (lt_mem_nhds hpos)
      filter_upwards [hn] with t ht
      exact congrArg (fun a : ℝ ↦ a ^ p) (abs_of_pos ht).symm
    convert hd.congr_of_eventuallyEq he.symm using 1
    dsimp only [G]
    ring
  have hG₀ : G 0 = fun x ↦ p * g x := by
    funext x
    simp [G]
  have hmeas : ∀ᶠ ε in 𝓝 (0 : ℝ), AEStronglyMeasurable (F ε) μ := by
    apply Eventually.of_forall
    intro ε
    exact ((continuous_const.add (continuous_const.mul continuous_id)).abs.rpow_const
      (fun _ ↦ Or.inr (zero_lt_one.trans hp).le)).comp_aestronglyMeasurable hg
  have hF₀ : F 0 = fun _ ↦ (1 : ℝ) := by
    funext x
    simp [F]
  let C := p * ((3 / 2 : ℝ) ^ (p - 1)) * B
  have hboundG : ∀ᵐ x ∂μ, ∀ ε ∈ ball (0 : ℝ) δ, ‖G ε x‖ ≤ C := by
    filter_upwards [hbounded] with x hx
    intro ε hε
    obtain ⟨hpos, hle⟩ := hϵ ε hε x hx
    have hp₀ := zero_lt_one.trans hp
    have hk : 0 ≤ p * (1 + ε * g x) ^ (p - 1) :=
      mul_nonneg hp₀.le (Real.rpow_nonneg hpos.le _)
    rw [Real.norm_eq_abs]
    dsimp only [G]
    rw [abs_mul, abs_of_nonneg hk]
    change p * (1 + ε * g x) ^ (p - 1) * |g x| ≤ p * ((3 / 2 : ℝ) ^ (p - 1)) * B
    have hpow := Real.rpow_le_rpow hpos.le hle (sub_nonneg.mpr hp.le)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hpow hp₀.le) hx (abs_nonneg _)
      (mul_nonneg hp₀.le (Real.rpow_nonneg (by norm_num) _))
  have hGmeas : AEStronglyMeasurable (G 0) μ := by
    rw [hG₀]
    exact aestronglyMeasurable_const.mul hg
  have hderiv := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := G) (bound := fun _ ↦ C) (ball_mem_nhds _ hδ) hmeas
    (hF₀ ▸ integrable_const (1 : ℝ)) hGmeas hboundG (integrable_const C) hdiff).2
  have hlmin : IsLocalMin (fun ε ↦ ∫ x, F ε x ∂μ) 0 := by
    apply (show IsMinOn (fun ε ↦ ∫ x, F ε x ∂μ) univ 0 from ?_).isLocalMin univ_mem
    intro ε _
    change (∫ x, F 0 x ∂μ) ≤ ∫ x, F ε x ∂μ
    rw [hF₀, integral_const, smul_eq_mul, mul_one]
    exact hmin ε
  have hzero := hderiv.deriv.symm.trans hlmin.deriv_eq_zero
  rw [hG₀, integral_const_mul] at hzero
  exact (mul_eq_zero.mp hzero).resolve_left (zero_lt_one.trans hp).ne'

/-- The variational inequality induced by perturbing a capacitary
potential by a function of its value implies the pushforward identity. -/
theorem measure_eq_smul_volume_of_power_perturbation_min (μ : Measure ℝ) [IsFiniteMeasure μ]
    {p : ℝ} (hp : 1 < p) (hs : μ (Icc (0 : ℝ) 1)ᶜ = 0)
    (hmin : ∀ φ : ℝ → ℝ, ContDiffOn ℝ 1 φ (Icc 0 1) → φ 0 = 0 → φ 1 = 0 →
      ∀ ε : ℝ, μ.real univ ≤ ∫ t, |1 + ε * derivWithin φ (Icc 0 1) t| ^ p ∂μ) :
    μ = μ univ • volume.restrict (Icc (0 : ℝ) 1) := by
  apply measure_eq_smul_volume_of_integral_derivWithin_eq_zero μ hs
  intro φ hφ hφ₀ hφ₁
  let g := derivWithin φ (Icc (0 : ℝ) 1)
  have hc : ContinuousOn g (Icc (0 : ℝ) 1) :=
    hφ.continuousOn_derivWithin uniqueDiffOn_Icc_zero_one le_rfl
  have hae : ∀ᵐ t ∂μ, t ∈ Icc (0 : ℝ) 1 := ae_iff.mpr hs
  have hμ : μ.restrict (Icc (0 : ℝ) 1) = μ := Measure.restrict_eq_self_of_ae_mem hae
  have hm : AEMeasurable g μ := hμ ▸ hc.aemeasurable measurableSet_Icc
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  apply integral_eq_zero_of_power_perturbation_min μ hp hm.aestronglyMeasurable
    (B := max B 0) (le_max_right _ _) _ (hmin φ hφ hφ₀ hφ₁)
  filter_upwards [hae] with t ht
  exact (by simpa only [Real.norm_eq_abs] using hB t ht : |g t| ≤ B).trans (le_max_left _ _)

end WalkDimensions
