import WalkDimensions.AverageHolder
import WalkDimensions.AverageOscillation
import WalkDimensions.BallIntegration
import WalkDimensions.Doubling

/-!
# Hölder regularity from a Besov bound

Two nearby averages are controlled by the mixed increments on the
averaging balls. The volume bound converts this to a dyadic Morrey estimate.
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal

namespace WalkDimensions

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  [SecondCountableTopology X] {m : Measure X} [IsFiniteMeasureOnCompacts m] [m.IsOpenPosMeasure]

theorem exists_holder_representative_of_besov_bound {p d β : ℝ} (hp : 1 ≤ p)
    (hvol : AhlforsRegular m d) (hβ : d < β) {u : X → ℝ}
    (huLp : MemLp u (ENNReal.ofReal p) m)
    {M : ℝ≥0∞} (hM : M ≠ ∞)
    (hB : ∀ s > (0 : ℝ), besovEnergy m p β univ u s ≤ M) :
    ∃ H : ℝ, 0 ≤ H ∧ ∃ v : X → ℝ, Continuous v ∧ u =ᵐ[m] v ∧
      ∀ x y, |v x - v y| ≤ H * dist x y ^ ((β - d) / p) := by
  have hp' : 0 < p := zero_lt_one.trans_le hp
  have he : 0 < (β - d) / p := div_pos (sub_pos.mpr hβ) hp'
  have hVD := hvol.volumeDoubling
  obtain ⟨_, V, hV, hVbound⟩ := hvol
  have hVDcopy := hVD
  obtain ⟨D, hD, hDvol⟩ := hVDcopy
  let C := V * D ^ 2 * (4 : ℝ) ^ β * M.toReal
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have havg (x z : X) (r : ℝ) (hr : 0 < r) (hxz : dist x z ≤ r) :
      |(⨍ y in ball x r, u y ∂m) - (⨍ y in ball z (2 * r), u y ∂m)| ≤
        C ^ p⁻¹ * r ^ ((β - d) / p) := by
    let S := ball x r
    let T := ball z (2 * r)
    have hr₂ : 0 < 2 * r := by positivity
    have hSpos := (measure_ball_pos m x hr).ne'
    have hTpos := (measure_ball_pos m z hr₂).ne'
    have hSfin : m S ≠ ∞ := measure_ball_ne_top
    have hTfin : m T ≠ ∞ := measure_ball_ne_top
    have hST : S ⊆ T := by
      intro y hy
      apply mem_ball.mpr
      exact (dist_triangle y x z).trans_lt (by linarith only [mem_ball.mp hy, hxz])
    let F (y t : X) := ENNReal.ofReal |u y - u t| ^ p
    have hpoint (y : X) (hy : y ∈ S) :
        ∫⁻ t in T, F y t ∂m ≤ (ENNReal.ofReal D) ^ 2 * m T * ballMoment m p u (4 * r) y := by
      have hyT := mem_ball.mp (hST hy)
      have hTB : T ⊆ ball y (4 * r) := by
        intro t ht
        apply mem_ball.mpr
        exact (dist_triangle t z y).trans_lt (by rw [dist_comm z y]; linarith only [mem_ball.mp ht, hyT])
      have hball : m (ball y (4 * r)) ≤ (ENNReal.ofReal D) ^ 2 * m T := by
        apply measure_ball_le_of_dist_le hDvol hr₂ 2
        norm_num
        linarith only [hyT, hr]
      have hnorm : m (ball y (4 * r)) * ballMoment m p u (4 * r) y =
          ∫⁻ t in ball y (4 * r), F y t ∂m := by
        have hpos : 0 < 4 * r := by positivity
        unfold ballMoment normalizedBall
        rw [lintegral_smul_measure, smul_eq_mul, ← mul_assoc,
          ENNReal.mul_inv_cancel (measure_ball_pos m y hpos).ne' measure_ball_ne_top, one_mul]
      exact (lintegral_mono_set hTB).trans ((le_of_eq hnorm.symm).trans (mul_le_mul_of_nonneg_right hball bot_le))
    have hInv : (m S)⁻¹ ≤ ENNReal.ofReal (V / r ^ d) := by
      have h := ENNReal.inv_le_inv.mpr (hVbound x r hr).1
      rw [← ENNReal.ofReal_inv_of_pos (div_pos (Real.rpow_pos_of_pos hr _) hV), inv_div] at h
      exact h
    have hmoment :
        (∫⁻ y, ballMoment m p u (4 * r) y ∂m) ≤ (ENNReal.ofReal (4 * r)) ^ β * M := by
      have h := mul_le_mul_of_nonneg_left (hB (4 * r) (by positivity))
        (bot_le : 0 ≤ (ENNReal.ofReal (4 * r)) ^ β)
      rw [besovEnergy, Measure.restrict_univ, ← mul_assoc, ← ENNReal.rpow_add] at h
      · simpa only [add_neg_cancel, ENNReal.rpow_zero, one_mul] using h
      · exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
      · exact ENNReal.ofReal_ne_top
    have hJ := ofReal_abs_sub_setAverage_rpow_le hp huLp hSpos hTpos hSfin hTfin
    change _ ≤ ((m S)⁻¹ * (m T)⁻¹) * (∫⁻ y in S, (∫⁻ t in T, F y t ∂m) ∂m) at hJ
    have hle : ENNReal.ofReal |(⨍ y in S, u y ∂m) - (⨍ y in T, u y ∂m)| ^ p ≤
        ENNReal.ofReal (C * r ^ (β - d)) := by
      refine hJ.trans ?_
      have hlocal := lintegral_mono_ae ((ae_restrict_mem (μ := m) measurableSet_ball).mono fun y hy ↦ hpoint y hy)
      apply (mul_le_mul_of_nonneg_left hlocal bot_le).trans
      rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hTfin)]
      have hcancel : (m S)⁻¹ * (m T)⁻¹ * ((ENNReal.ofReal D) ^ 2 * m T *
          (∫⁻ y in S, ballMoment m p u (4 * r) y ∂m)) =
          (m S)⁻¹ * (ENNReal.ofReal D) ^ 2 *
          (∫⁻ y in S, ballMoment m p u (4 * r) y ∂m) := by
        calc
          _ = ((m T)⁻¹ * m T) * ((m S)⁻¹ * (ENNReal.ofReal D) ^ 2 *
              (∫⁻ y in S, ballMoment m p u (4 * r) y ∂m)) := by ac_rfl
          _ = _ := by rw [ENNReal.inv_mul_cancel hTpos hTfin, one_mul]
      rw [hcancel]
      calc
        _ ≤ (ENNReal.ofReal (V / r ^ d) * (ENNReal.ofReal D) ^ 2) *
            ((ENNReal.ofReal (4 * r)) ^ β * M) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hInv bot_le) ((lintegral_mono_set (subset_univ S)).trans
            (by rwa [Measure.restrict_univ])) bot_le bot_le
        _ = _ := by
          rw [← ENNReal.ofReal_pow (by positivity : 0 ≤ D),
            ENNReal.ofReal_rpow_of_pos (by positivity : 0 < 4 * r), ← ENNReal.ofReal_toReal hM,
            ← ENNReal.ofReal_mul (by positivity : 0 ≤ (4 * r) ^ β),
            ← ENNReal.ofReal_mul (by positivity : 0 ≤ V / r ^ d),
            ← ENNReal.ofReal_mul (by positivity : 0 ≤ V / r ^ d * D ^ 2)]
          congr 1
          rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hr.le, Real.rpow_sub hr]
          dsimp [C]
          ring
    rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp'.le,
      ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ C * r ^ (β - d))] at hle
    have hrpow := Real.rpow_le_rpow (Real.rpow_nonneg (abs_nonneg _) p) hle (inv_nonneg.mpr hp'.le)
    rw [← Real.rpow_mul (abs_nonneg _), mul_inv_cancel₀ hp'.ne', Real.rpow_one,
      Real.mul_rpow hC (by positivity), ← Real.rpow_mul hr.le, ← div_eq_mul_inv] at hrpow
    exact hrpow
  obtain ⟨H, hH, hHolder⟩ := exists_holder_bound_at_lebesgue_points hVD he
  obtain ⟨S, hS, hBound⟩ :=
    hHolder (huLp.locallyIntegrable (ENNReal.one_le_ofReal.mpr hp)) (Real.rpow_nonneg hC _) havg
  have hK : 0 ≤ H * C ^ p⁻¹ := mul_nonneg hH.le (Real.rpow_nonneg hC _)
  exact ⟨_, hK, exists_holder_representative_of_full_measure hS he hK hBound⟩

end WalkDimensions
