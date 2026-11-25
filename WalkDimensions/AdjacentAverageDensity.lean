import WalkDimensions.AverageOscillation
import WalkDimensions.EnergyMeasureConstruction
import WalkDimensions.Doubling

/-!
# Nearby averages when energy mass is bounded by volume
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {m : Measure X} [IsFiniteMeasureOnCompacts m] [m.IsOpenPosMeasure]
  {p : ℝ} (E : PEnergy m p)

theorem exists_adjacent_average_bound_of_density {β : ℝ}
    (hvol : VolumeDoubling m) (hPI : E.Poincare E.energyMeasure β) :
    ∃ C A : ℝ, 0 < C ∧ 1 ≤ A ∧ ∀ (f : E.domain) (y z : X) (r a : ℝ), 0 < r → 0 ≤ a →
      dist y z ≤ r →
      (E.energyMeasure f (ball z (A * r))).toReal ≤ a * (m (ball z (A * r))).toReal →
      |(⨍ x in ball y r, (f : RealLp m p) x ∂m) - (⨍ x in ball z r, (f : RealLp m p) x ∂m)| ≤
        C * a ^ p⁻¹ * r ^ (β / p) := by
  obtain ⟨D, hD, hvol⟩ := hvol
  obtain ⟨P, A₀, hP, hA₀, hPI⟩ := hPI
  let A := 2 * A₀
  have hA : 1 ≤ A := by dsimp only [A]; linarith
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 + A) (show (1 : ℝ) < 2 by norm_num)
  let C := P * (2 : ℝ) ^ β * D ^ n
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨2 * C ^ p⁻¹, A, by positivity, hA, ?_⟩
  intro f y z r a hr ha hyz hMass
  let u := (f : RealLp m p)
  let T := ball z (2 * r)
  let B := ball z (A * r)
  let c := ⨍ x in T, u x ∂m
  let G := E.energyMeasure f B
  have hMass' : G ≤ ENNReal.ofReal a * m B := by
    have h := ENNReal.ofReal_le_ofReal hMass
    rw [ENNReal.ofReal_toReal (measure_ne_top _ _), ENNReal.ofReal_mul ha,
      ENNReal.ofReal_toReal measure_ball_ne_top] at h
    exact h
  have hPI' : (∫⁻ x in T, ENNReal.ofReal |u x - c| ^ p ∂m) ≤
      ENNReal.ofReal (P * (2 * r) ^ β) * G := by
    simpa only [T, c, G, B, u, A, mul_left_comm A₀ 2, mul_assoc] using hPI z (2 * r) (by positivity) f
  have hMix (w : X) (hw : dist w z ≤ r) :
      |(⨍ x in ball w r, u x ∂m) - c| ≤ C ^ p⁻¹ * a ^ p⁻¹ * r ^ (β / p) := by
    let S := ball w r
    have hS : S ⊆ T := by
      intro x hx
      apply mem_ball.mpr
      exact (dist_triangle x w z).trans_lt (by linarith only [mem_ball.mp hx, hw])
    have hmS := (measure_ball_pos m w hr).ne'
    have hBvol : m B ≤ (ENNReal.ofReal D) ^ n * m S := by
      apply measure_ball_le_of_dist_le hvol hr n
      rw [dist_comm z w]
      calc
        _ ≤ (1 + A) * r := by nlinarith only [hw]
        _ ≤ _ := mul_le_mul_of_nonneg_right hn.le hr.le
    have hAavg := ofReal_abs_setAverage_sub_rpow_le E.one_lt.le hS hmS measure_ball_ne_top
      ((Lp.memLp u).mono_measure Measure.restrict_le_self) c
    have hPoint := hAavg.trans (mul_le_mul_of_nonneg_left hPI' bot_le)
    have hBound := hPoint.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (hMass'.trans (mul_le_mul_of_nonneg_left hBvol bot_le)) bot_le) bot_le)
    have he : (m S)⁻¹ * (ENNReal.ofReal (P * (2 * r) ^ β) *
          (ENNReal.ofReal a * ((ENNReal.ofReal D) ^ n * m S))) =
        ENNReal.ofReal (C * a * r ^ β) := by
      calc
        _ = ((m S)⁻¹ * m S) * (ENNReal.ofReal (P * (2 * r) ^ β) *
          (ENNReal.ofReal a * (ENNReal.ofReal D) ^ n)) := by ac_rfl
        _ = _ := by
          rw [ENNReal.inv_mul_cancel hmS measure_ball_ne_top, one_mul,
            ← ENNReal.ofReal_pow hD.le, ← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [Real.mul_rpow (by norm_num : 0 ≤ (2 : ℝ)) hr.le]
          dsimp only [C]
          ring
    rw [he] at hBound
    have hp := zero_lt_one.trans E.one_lt
    rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp.le, ENNReal.ofReal_le_ofReal_iff (by positivity)] at hBound
    have h := Real.rpow_le_rpow (Real.rpow_nonneg (abs_nonneg _) p) hBound (inv_nonneg.mpr hp.le)
    rw [← Real.rpow_mul (abs_nonneg _), mul_inv_cancel₀ hp.ne', Real.rpow_one,
      Real.mul_rpow (mul_nonneg hC.le ha) (Real.rpow_nonneg hr.le _),
      Real.mul_rpow hC.le ha, ← Real.rpow_mul hr.le, ← div_eq_mul_inv] at h
    exact h
  have hBound := add_le_add (hMix y hyz) (hMix z (by simpa only [dist_self] using hr.le))
  have hTriangle := abs_sub_le (⨍ x in ball y r, u x ∂m) c (⨍ x in ball z r, u x ∂m)
  rw [abs_sub_comm c] at hTriangle
  exact hTriangle.trans (hBound.trans_eq (by
    change _ = 2 * C ^ p⁻¹ * a ^ p⁻¹ * r ^ (β / p)
    ring))

end WalkDimensions.PEnergy
