import WalkDimensions.AverageOscillation
import WalkDimensions.EnergyClosedness

/-!
# Point evaluation in the energy graph norm

A pointwise Hölder estimate controls the difference between the value at
a point and the average over a unit ball. The average is bounded in (L^p).
-/

open Filter MeasureTheory Metric Set
open scoped ENNReal

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {m : Measure X} [IsFiniteMeasureOnCompacts m] [m.IsOpenPosMeasure]
  {p : ℝ} (E : PEnergy m p)

theorem abs_apply_le_graphSeminorm {f : E.domain} {u : X → ℝ}
    (hfu : (f : RealLp m p) =ᵐ[m] u) {H a : ℝ} (hH : 0 ≤ H) (ha : 0 ≤ a)
    (hbound : ∀ x y, |u x - u y| ≤ H * E.rootSeminorm f * dist x y ^ a) (x : X) :
    |u x| ≤ (H + (m.real (ball x 1)) ^ (-p⁻¹)) * E.graphSeminorm f := by
  let B := ball x 1
  let M := (m.real B) ^ (-p⁻¹)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hB₀ : m B ≠ 0 := (measure_ball_pos m x zero_lt_one).ne'
  have hBfin : m B ≠ ∞ := measure_ball_ne_top
  let : IsFiniteMeasure (m.restrict B) := ⟨by rw [Measure.restrict_apply_univ]; exact hBfin.lt_top⟩
  have huLp : MemLp u (ENNReal.ofReal p) (m.restrict B) :=
    ((Lp.memLp (f : RealLp m p)).ae_eq hfu).mono_measure Measure.restrict_le_self
  have huI : IntegrableOn u B m := huLp.integrable (ENNReal.one_le_ofReal.mpr E.one_lt.le)
  have hosc := abs_setAverage_sub_le_of_bound (measurableSet_ball (x := x) (ε := 1))
    hB₀ hBfin huI (a := u x) (ε := H * E.rootSeminorm f) (by
      intro y hy
      have h := Real.rpow_le_rpow dist_nonneg (mem_ball.mp hy).le ha
      rw [Real.one_rpow] at h
      exact (hbound y x).trans (mul_le_of_le_one_right (by positivity) h))
  have havg := abs_setAverage_le_realLp_norm E.one_lt.le (f : RealLp m p) hB₀ hBfin
  have hae := average_congr (ae_restrict_of_ae (s := B) hfu)
  rw [← hae] at hosc
  let z := ⨍ y in B, (f : RealLp m p) y ∂m
  calc
    _ = |(u x - z) + z| := by rw [sub_add_cancel]
    _ ≤ |u x - z| + |z| := abs_add_le _ _
    _ ≤ H * E.rootSeminorm f + M * ‖(f : RealLp m p)‖ := by
      rw [abs_sub_comm]
      exact add_le_add hosc havg
    _ ≤ _ := by
      rw [add_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left (E.rootSeminorm_le_graphSeminorm f) hH)
        (mul_le_mul_of_nonneg_left (E.norm_le_graphSeminorm f) hM)

end WalkDimensions.PEnergy
