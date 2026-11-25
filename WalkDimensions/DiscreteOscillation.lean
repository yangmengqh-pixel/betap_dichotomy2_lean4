import WalkDimensions.AverageOscillation
import WalkDimensions.BallIntegration
import WalkDimensions.DoublingCovers

/-!
# Oscillation of neighbouring ball averages

For a separated family of centres, the sum of the mean oscillations
across neighbouring balls is controlled by one Besov moment at an
enlarged radius.
-/

open MeasureTheory Metric Set
open scoped ENNReal

namespace WalkDimensions

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SecondCountableTopology X] {m : Measure X} [SFinite m]
  [IsFiniteMeasureOnCompacts m] [m.IsOpenPosMeasure]

theorem exists_sum_ball_average_oscillation_le (hvol : VolumeDoubling m)
    {A : ℝ} (hA : 0 ≤ A) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ {p : ℝ}, 1 ≤ p → ∀ (t : Finset X) (r : ℝ), 0 < r →
        (↑t : Set X).Pairwise (fun x y ↦ r ≤ dist x y) →
        ∀ N : X → Finset X, (∀ z, N z ⊆ t) →
          (∀ z y, y ∈ N z → dist y z ≤ A * r) →
          ∀ u : X → ℝ, Measurable u → MemLp u (ENNReal.ofReal p) m →
          (∑ z ∈ t, ∑ y ∈ N z, m (ball z r) * ENNReal.ofReal
            |(⨍ w in ball z r, u w ∂m) - (⨍ w in ball y r, u w ∂m)| ^ p) ≤
          C * ∫⁻ x, ballMoment m p u ((A + 2) * r) x ∂m := by
  obtain ⟨M, _, hpack⟩ := exists_card_le_of_separated_centres hvol (R := 2 * A) (by positivity)
  obtain ⟨L, _, hcover⟩ := exists_sum_setLIntegral_ball_le hvol (A := 1) zero_le_one
  obtain ⟨D, _, hD⟩ := hvol
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 * A + 3) (show (1 : ℝ) < 2 by norm_num)
  let K := ENNReal.ofReal D ^ n
  have hK : K ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  refine ⟨(M : ℝ≥0∞) * K * L,
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top M) hK) (ENNReal.natCast_ne_top L),
    fun {p} hp t r hr hsep N hNsub hNdist u hu huLp ↦ ?_⟩
  let R := (A + 2) * r
  have hR : 0 < R := by dsimp [R]; positivity
  let a (z : X) := ⨍ w in ball z r, u w ∂m
  let F := ballMoment m p u R
  have hNcard (z : X) : (N z).card ≤ M := by
    apply hpack z (r / 2) (by positivity)
    · intro y hy
      rw [show 2 * A * (r / 2) = A * r by ring]
      exact hNdist z y hy
    · intro x hx y hy hxy
      rw [show 2 * (r / 2) = r by ring]
      exact hsep (hNsub z hx) (hNsub z hy) hxy
  have hpair (z y : X) (hy : y ∈ N z) :
      m (ball z r) * ENNReal.ofReal |a z - a y| ^ p ≤ K * ∫⁻ x in ball z r, F x ∂m := by
    let B := ball z r
    let B' := ball y r
    let H (x w : X) : ℝ≥0∞ := ENNReal.ofReal |u x - u w| ^ p
    have hB : m B ≠ 0 := (measure_ball_pos m z hr).ne'
    have hB' : m B' ≠ 0 := (measure_ball_pos m y hr).ne'
    have hj := ofReal_abs_sub_setAverage_rpow_le hp huLp hB hB' measure_ball_ne_top measure_ball_ne_top
    have hfactor : m B * ((m B)⁻¹ * (m B')⁻¹) = (m B')⁻¹ := by
      rw [← mul_assoc, ENNReal.mul_inv_cancel hB measure_ball_ne_top, one_mul]
    calc
      _ ≤ m B * (((m B)⁻¹ * (m B')⁻¹) * (∫⁻ x in B, (∫⁻ w in B', H x w ∂m) ∂m)) :=
        mul_le_mul_of_nonneg_left hj bot_le
      _ = ∫⁻ x in B, ((m B')⁻¹ * ∫⁻ w in B', H x w ∂m) ∂m := by
        rw [← mul_assoc, hfactor, lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hB')]
      _ ≤ ∫⁻ x in B, K * F x ∂m := by
        apply setLIntegral_mono' measurableSet_ball
        intro x hx
        have hxB : dist x z < r := mem_ball.mp hx
        have hxy : dist x y < (A + 1) * r := by
          have hh := dist_triangle x z y
          rw [dist_comm z y] at hh
          linarith only [hxB, hh, hNdist z y hy]
        have hBsub : B' ⊆ ball x R := by
          intro w hw
          have h := dist_triangle w y x
          rw [dist_comm y x] at h
          exact mem_ball.mpr (h.trans_lt (by dsimp [R]; linarith only [hxy, mem_ball.mp hw]))
        have hvol' : m (ball x R) ≤ K * m B' :=
          measure_ball_le_of_dist_le hD hr n (by
            dsimp [R]
            calc
              _ ≤ (2 * A + 3) * r := by linarith only [hxy]
              _ ≤ _ := mul_le_mul_of_nonneg_right hn.le hr.le)
        have hi := inv_measure_le_mul_inv_of_le hB' (measure_ball_pos m x hR).ne'
          (measure_ball_ne_top (μ := m)) (measure_ball_ne_top (μ := m)) hvol'
        unfold F ballMoment normalizedBall
        rw [lintegral_smul_measure, smul_eq_mul, ← mul_assoc]
        exact mul_le_mul hi (lintegral_mono_set hBsub) bot_le bot_le
      _ = _ := lintegral_const_mul' _ _ hK
  have hlocal (z : X) :
      (∑ y ∈ N z, m (ball z r) * ENNReal.ofReal |a z - a y| ^ p) ≤
        (M : ℝ≥0∞) * (K * ∫⁻ x in ball z r, F x ∂m) := by
    calc
      _ ≤ ∑ _ ∈ N z, K * ∫⁻ x in ball z r, F x ∂m := Finset.sum_le_sum (hpair z)
      _ = ((N z).card : ℝ≥0∞) * (K * ∫⁻ x in ball z r, F x ∂m) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hNcard z) bot_le
  calc
    _ ≤ ∑ z ∈ t, (M : ℝ≥0∞) * (K * ∫⁻ x in ball z r, F x ∂m) :=
      Finset.sum_le_sum (fun z _ ↦ hlocal z)
    _ = ((M : ℝ≥0∞) * K) * (∑ z ∈ t, ∫⁻ x in ball z r, F x ∂m) := by
      simp only [← mul_assoc, Finset.mul_sum]
    _ ≤ ((M : ℝ≥0∞) * K) * ((L : ℝ≥0∞) * ∫⁻ x, F x ∂m) := by
      apply mul_le_mul_of_nonneg_left _ bot_le
      simpa only [one_mul] using hcover t r hr hsep F (measurable_ballMoment hu p R)
    _ = _ := by simp only [mul_assoc, F, R]

end WalkDimensions
