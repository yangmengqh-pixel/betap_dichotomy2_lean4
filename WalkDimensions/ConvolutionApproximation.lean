import WalkDimensions.DiscreteConvolution
import WalkDimensions.Doubling

/-!
# Approximation in the ambient space by discrete convolutions
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal

namespace WalkDimensions

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {m : Measure X} [IsFiniteMeasureOnCompacts m] [m.IsOpenPosMeasure]

omit [BorelSpace X] in
theorem exists_discrete_convolution_error_le (hvol : VolumeDoubling m) {p A : ℝ}
    (hp : 1 ≤ p) (hA : 1 < A) :
    ∃ J : ℝ≥0∞, J ≠ ∞ ∧ ∀ (t : Finset X) {r : ℝ}, 0 < r →
      ∀ (w : X → X → ℝ),
      (∀ z ∈ t, ∀ x, 0 ≤ w z x) →
      (∀ z ∈ t, EqOn (w z) (fun _ ↦ 0) (ball z (A * r))ᶜ) →
      ∀ (U : Set X), EqOn (fun x ↦ ∑ z ∈ t, w z x) (fun _ ↦ 1) U →
      ∀ {u : X → ℝ}, MemLp u (ENNReal.ofReal p) m → tsupport u ⊆ U →
      let v (x : X) := ∑ z ∈ t, (⨍ y in ball z r, u y ∂m) * w z x
      tsupport v ⊆ U →
      ∀ (f g : RealLp m p), f =ᵐ[m] v → g =ᵐ[m] u →
        (ENNReal.ofReal ‖f - g‖) ^ p ≤ J *
          ∫⁻ x, ballMoment m p u ((2 * A + 3) * r) x ∂m := by
  obtain ⟨D, _, hD⟩ := hvol
  let B := 2 * A + 3
  have hB : 0 < B := by dsimp [B]; linarith
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (A + B) (show (1 : ℝ) < 2 by norm_num)
  let J := (ENNReal.ofReal D) ^ n
  have hJ : J ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  refine ⟨J, hJ, fun t r hr w hw hwzero U hUnity u hu huU ↦ ?_⟩
  let a (z : X) := ⨍ y in ball z r, u y ∂m
  let v (x : X) := ∑ z ∈ t, a z * w z x
  change tsupport v ⊆ U → _
  intro hvU f g hf hg
  have hp₀ : 0 < p := zero_lt_one.trans_le hp
  have hp' : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp₀
  have hterm (x z : X) (hxz : x ∈ ball z (A * r)) :
      ENNReal.ofReal |a z - u x| ^ p ≤ J * ballMoment m p u (B * r) x := by
    have hdist : dist x z < A * r := mem_ball.mp hxz
    have hsub : ball z r ⊆ ball x (B * r) := by
      intro y hy
      have h := (dist_triangle y z x).trans_lt
        (add_lt_add (mem_ball.mp hy) (by simpa only [dist_comm z x] using hdist))
      exact mem_ball.mpr (h.trans_le (by dsimp [B]; nlinarith))
    have hcompare := measure_ball_le_of_dist_le hD hr n
      (show dist x z + B * r ≤ (2 : ℝ) ^ n * r from
        (show dist x z + B * r ≤ A * r + B * r from add_le_add hdist.le le_rfl).trans
          (by calc
            _ = (A + B) * r := (add_mul _ _ _).symm
            _ ≤ _ := mul_le_mul_of_nonneg_right hn.le hr.le))
    have hinv := inv_measure_le_mul_inv_of_le (measure_ball_pos m z hr).ne'
      (measure_ball_pos m x (mul_pos hB hr)).ne' measure_ball_ne_top measure_ball_ne_top hcompare
    have hj := ofReal_abs_setAverage_sub_rpow_le hp hsub
      (measure_ball_pos m z hr).ne' measure_ball_ne_top
      (hu.mono_measure Measure.restrict_le_self) (u x)
    apply hj.trans
    simp only [ballMoment, normalizedBall, lintegral_smul_measure, smul_eq_mul, ← mul_assoc]
    simp_rw [abs_sub_comm (u x)]
    exact mul_le_mul_of_nonneg_right hinv bot_le
  have hpt (x : X) : ENNReal.ofReal |v x - u x| ^ p ≤ J * ballMoment m p u (B * r) x := by
    by_cases hx : x ∈ U
    · have hs : ∑ z ∈ t, w z x = 1 := hUnity hx
      have he : v x - u x = ∑ z ∈ t, w z x • (a z - u x) := by
        simp only [v, smul_eq_mul, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hs, one_mul]
        congr 1
        exact Finset.sum_congr rfl (fun z _ ↦ mul_comm _ _)
      have hj := (convexOn_abs_rpow hp).map_sum_le (fun z hz ↦ hw z hz x) hs
        (fun z _ ↦ mem_univ (a z - u x))
      rw [← he] at hj
      rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg (v x - u x)) hp₀.le]
      refine (ENNReal.ofReal_le_ofReal hj).trans ?_
      simp only [smul_eq_mul]
      rw [ENNReal.ofReal_sum_of_nonneg (fun z hz ↦
        mul_nonneg (hw z hz x) (Real.rpow_nonneg (abs_nonneg _) _))]
      calc
        _ ≤ ∑ z ∈ t, ENNReal.ofReal (w z x) * (J * ballMoment m p u (B * r) x) := by
          apply Finset.sum_le_sum
          intro z hz
          rw [ENNReal.ofReal_mul (hw z hz x),
            ← ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp₀.le]
          by_cases hxz : x ∈ ball z (A * r)
          · exact mul_le_mul_of_nonneg_left (hterm x z hxz) bot_le
          · simp [hwzero z hz hxz]
        _ = _ := by
          rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun z hz ↦ hw z hz x), hs]
          simp
    · have huv : u x = 0 := notMem_support.mp fun h ↦ hx (huU (subset_closure h))
      have hvv : v x = 0 := notMem_support.mp fun h ↦ hx (hvU (subset_closure h))
      simp [huv, hvv, ENNReal.zero_rpow_of_pos hp₀]
  have hAE : ∀ᵐ x ∂m, ENNReal.ofReal |(f - g) x| ^ p ≤ J * ballMoment m p u (B * r) x := by
    filter_upwards [Lp.coeFn_sub f g, hf, hg] with x hx hfx hgx
    simpa only [hx, Pi.sub_apply, hfx, hgx] using hpt x
  have hnorm : ENNReal.ofReal ‖f - g‖ = eLpNorm (f - g) (ENNReal.ofReal p) m := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_lt_top (f - g)).ne]
  rw [hnorm, eLpNorm_eq_lintegral_rpow_eNorm_toReal hp' ENNReal.ofReal_ne_top
      (Lp.aestronglyMeasurable (f - g))]
  simp only [ENNReal.toReal_ofReal hp₀.le, Real.eNorm_eq_ofReal_abs, one_div]
  rw [← ENNReal.rpow_mul, inv_mul_cancel₀ hp₀.ne', ENNReal.rpow_one,
    ← lintegral_const_mul' _ _ hJ]
  exact lintegral_mono_ae hAE

end WalkDimensions
