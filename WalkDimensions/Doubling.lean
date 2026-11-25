import WalkDimensions.Geometry

/-!
# Ball comparisons for doubling measures
-/

open MeasureTheory Metric Set
open scoped ENNReal

namespace WalkDimensions

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] {m : Measure X}

/-- Iterate the twofold volume bound. -/
theorem measure_ball_two_pow_le {D : ℝ≥0∞}
    (hD : ∀ (x : X) (r : ℝ), 0 < r → m (ball x (2 * r)) ≤ D * m (ball x r))
    (x : X) {r : ℝ} (hr : 0 < r) (n : ℕ) :
    m (ball x ((2 : ℝ) ^ n * r)) ≤ D ^ n * m (ball x r) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show (2 : ℝ) ^ (n + 1) * r = 2 * (2 ^ n * r) by ring]
    calc
      _ ≤ D * m (ball x ((2 : ℝ) ^ n * r)) := hD _ _ (by positivity)
      _ ≤ D * (D ^ n * m (ball x r)) := mul_le_mul_of_nonneg_left ih bot_le
      _ = _ := by rw [pow_succ', mul_assoc]

/-- A ball at a nearby centre is controlled by a fixed iterate of doubling. -/
theorem measure_ball_le_of_dist_le {D : ℝ≥0∞}
    (hD : ∀ (x : X) (r : ℝ), 0 < r → m (ball x (2 * r)) ≤ D * m (ball x r))
    {x y : X} {r t : ℝ} (hr : 0 < r) (n : ℕ)
    (hxy : dist y x + t ≤ (2 : ℝ) ^ n * r) :
    m (ball y t) ≤ D ^ n * m (ball x r) := by
  refine (measure_mono ?_).trans (measure_ball_two_pow_le hD x hr n)
  intro z hz
  apply mem_ball.mpr
  calc
    dist z x ≤ dist z y + dist y x := dist_triangle _ _ _
    _ < t + dist y x := add_lt_add_left (mem_ball.mp hz) _
    _ ≤ _ := by simpa only [add_comm] using hxy

/-- Inverse volumes at comparable centres inherit the same doubling factor. -/
theorem inv_measure_le_mul_inv_of_le {a b D : ℝ≥0∞} (ha : a ≠ 0) (hb : b ≠ 0)
    (hat : a ≠ ∞) (hbt : b ≠ ∞) (h : b ≤ D * a) :
    a⁻¹ ≤ D * b⁻¹ := by
  have h' : b * a⁻¹ * b⁻¹ ≤ (D * a) * a⁻¹ * b⁻¹ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h bot_le) bot_le
  rw [mul_assoc D a, ENNReal.mul_inv_cancel ha hat, mul_one, mul_right_comm b,
    ENNReal.mul_inv_cancel hb hbt, one_mul] at h'
  exact h'

end WalkDimensions
