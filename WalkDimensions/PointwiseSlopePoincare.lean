import WalkDimensions.LipschitzPoincare
import WalkDimensions.LocalMaximalAverage
import WalkDimensions.LocalMorrey

/-!
# The pointwise consequence of the slope Poincaré inequality
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal NNReal Topology

namespace WalkDimensions

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SecondCountableTopology X] {m : Measure X}
  [m.Regular] [SFinite m] [m.IsOpenPosMeasure]

/-- At distinct endpoints, the difference of a Lipschitz function is bounded
by distance times the sum of the endpoint maximal slopes. -/
theorem SlopePoincare.exists_pointwise_bound {p : ℝ} (hp : 1 ≤ p) (hvol : VolumeDoubling m)
    (hP : SlopePoincare m p) :
    ∃ C A : ℝ, 0 < C ∧ 1 ≤ A ∧
      ∀ (u : X → ℝ) {K : ℝ≥0}, LipschitzWith K u →
      ∀ (x y : X), |u x - u y| ≤ C * dist x y *
        ((localMaximalAverage m (fun z ↦ pointwiseSlope u z ^ p) (A * dist x y) x).toReal ^ p⁻¹ +
        (localMaximalAverage m (fun z ↦ pointwiseSlope u z ^ p) (A * dist x y) y).toReal ^ p⁻¹) := by
  obtain ⟨P, hP₀, hPT, A₀, hA₀, hP⟩ := hP
  obtain ⟨D, hD, hVD⟩ := hvol
  have hp₀ := zero_lt_one.trans_le hp
  let A := 2 * A₀
  have hA : 1 ≤ A := by dsimp only [A]; linarith
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 + A) (show (1 : ℝ) < 2 by norm_num)
  let M := P.toReal * D ^ n
  have hM : 0 < M := mul_pos (ENNReal.toReal_pos hP₀.ne' hPT) (pow_pos hD _)
  let C := 8 * M ^ p⁻¹
  refine ⟨C, A, by dsimp only [C]; positivity, hA, fun u K hu x y ↦ ?_⟩
  by_cases hxy : x = y
  · subst y
    simp
  let r := dist x y
  have hr : 0 < r := dist_pos.mpr hxy
  let g (v : X) := pointwiseSlope u v ^ p
  let F (v : X) := localMaximalAverage m g (A * r) v
  let H (v : X) := (F v).toReal ^ p⁻¹
  have hH (v : X) : 0 ≤ H v := by dsimp only [H]; positivity
  have hFfin (v : X) : F v ≠ ∞ := by
    apply ne_top_of_le_ne_top (a := F v)
      (b := (K : ℝ≥0∞) ^ p)
      (ENNReal.rpow_ne_top_of_nonneg hp₀.le ENNReal.coe_ne_top)
    apply localMaximalAverage_le_const
    intro z
    apply ENNReal.rpow_le_rpow _ hp₀.le
    exact iInf_le_of_le (f := fun n : ℕ ↦ ballSlope u (1 / ((n : ℝ) + 1)) z) 0
      (ballSlope_le_of_lipschitzWith hu _ _)
  let av (z : X) (s : ℝ) := ⨍ w in ball z s, u w ∂m
  have hStep (v z : X) (s : ℝ) (hs : 0 < s) (hsr : s ≤ r) (hvz : dist v z ≤ s) :
      |av v s - av z (2 * s)| ≤ (2 * M ^ p⁻¹ * H z) * s := by
    let S := ball v s
    let T := ball z (2 * s)
    let B := ball z (A * s)
    have hSB : S ⊆ T := by
      intro w hw
      apply mem_ball.mpr
      exact (dist_triangle w v z).trans_lt (by linarith only [mem_ball.mp hw, hvz])
    have hsT : 0 < 2 * s := by positivity
    have hsB : 0 < A * s := mul_pos (zero_lt_one.trans_le hA) hs
    have hBvol : m B ≤ ENNReal.ofReal D ^ n * m S := by
      apply measure_ball_le_of_dist_le hVD hs n
      rw [dist_comm z v]
      exact (show dist v z + A * s ≤ (1 + A) * s by nlinarith only [hvz]).trans
        (mul_le_mul_of_nonneg_right hn.le hs.le)
    have hInt : (∫⁻ y in B, g y ∂m) ≤ F z * m B :=
      lintegral_ball_le_localMaximalAverage g hsB
        (mul_le_mul_of_nonneg_left hsr (zero_le_one.trans hA)) (mem_ball_self hsB)
    have hPI' : (∫⁻ w in T, ENNReal.ofReal |u w - av z (2 * s)| ^ p ∂m) ≤
        P * (ENNReal.ofReal (2 * s)) ^ p * ∫⁻ y in B, g y ∂m := by
      simpa only [T, av, B, g, A, mul_left_comm A₀ 2, mul_assoc] using hP z (2 * s) hsT u hu
    have hLp : MemLp u (ENNReal.ofReal p) (m.restrict T) := by
      let : IsFiniteMeasure (m.restrict T) := ⟨by simpa [T] using
        (measure_ball_lt_top (μ := m) (x := z) (r := 2 * s))⟩
      apply MemLp.of_bound hu.continuous.aestronglyMeasurable (|u z| + K * (2 * s))
      filter_upwards [ae_restrict_mem (μ := m) (s := T) measurableSet_ball] with w hw
      have hh := hu.dist_le_mul w z
      rw [Real.dist_eq] at hh
      have hrad : dist w z ≤ 2 * s := (mem_ball.mp hw).le
      calc
        ‖u w‖ = |u w - u z + u z| := by rw [sub_add_cancel, Real.norm_eq_abs]
        _ ≤ |u w - u z| + |u z| := abs_add_le _ _
        _ ≤ _ := by
          have hb := hh.trans (mul_le_mul_of_nonneg_left hrad K.coe_nonneg)
          linarith only [hb]
    have hJ := ofReal_abs_setAverage_sub_rpow_le hp hSB
      (measure_ball_pos m v hs).ne' measure_ball_ne_top hLp (av z (2 * s))
    have hBd := hJ.trans (mul_le_mul_of_nonneg_left
      (hPI'.trans (mul_le_mul_of_nonneg_left (hInt.trans
        (mul_le_mul_of_nonneg_left hBvol bot_le)) bot_le)) bot_le)
    have hBval : (m S)⁻¹ * (P * ENNReal.ofReal (2 * s) ^ p *
          (F z * (ENNReal.ofReal D ^ n * m S))) =
        ENNReal.ofReal (M * (2 * s) ^ p * (F z).toReal) := by
      calc
        _ = ((m S)⁻¹ * m S) * (P * ENNReal.ofReal (2 * s) ^ p * (F z * ENNReal.ofReal D ^ n)) := by ac_rfl
        _ = _ := by
          rw [ENNReal.inv_mul_cancel (measure_ball_pos m v hs).ne' measure_ball_ne_top, one_mul,
            ENNReal.ofReal_rpow_of_pos hsT, ← ENNReal.ofReal_pow hD.le,
            ← ENNReal.ofReal_toReal hPT, ← ENNReal.ofReal_toReal (hFfin z),
            ← ENNReal.ofReal_mul ENNReal.toReal_nonneg, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
            ← ENNReal.ofReal_mul (by positivity : 0 ≤ P.toReal * (2 * s) ^ p),
            ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
          congr 1
          dsimp only [M]
          ring
    rw [hBval, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp₀.le,
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at hBd
    have hh := Real.rpow_le_rpow (Real.rpow_nonneg (abs_nonneg _) p) hBd (inv_nonneg.mpr hp₀.le)
    rw [← Real.rpow_mul (abs_nonneg _), mul_inv_cancel₀ hp₀.ne', Real.rpow_one,
      Real.mul_rpow (by positivity) ENNReal.toReal_nonneg, Real.mul_rpow hM.le (by positivity),
      ← Real.rpow_mul hsT.le, mul_inv_cancel₀ hp₀.ne', Real.rpow_one] at hh
    exact hh.trans_eq (by dsimp only [H]; ring)
  have hAv (v : X) : Tendsto (av v) (𝓝[>] (0 : ℝ)) (𝓝 (u v)) := by
    obtain ⟨w, J, hw, hwC, hEq⟩ := exists_compact_lipschitz_eqOn_ball hu v zero_lt_one
    rw [← hEq (mem_ball_self zero_lt_one)]
    apply (tendsto_ball_average_of_continuous_compact (m := m) hw.continuous hwC v).congr'
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    apply average_congr
    filter_upwards [ae_restrict_mem (μ := m) (s := ball v t) measurableSet_ball] with z hz
    exact hEq (ball_subset_ball ht.2.le hz)
  have hTail (z : X) : |u z - av z r| ≤ (4 * M ^ p⁻¹ * H z) * r := by
    have hh := abs_sub_setAverage_le_of_dyadic_bound (x := z) (e := 1)
      (K := 2 * M ^ p⁻¹ * H z) zero_lt_one (by positivity [hH z]) hr (hAv z)
      (fun t ht htr ↦ by
        rw [Real.rpow_one]
        exact hStep z z t ht htr (by simpa only [dist_self] using ht.le))
    exact hh.trans_eq (by rw [Real.rpow_one, Real.rpow_one]; ring)
  have hMain₁ := hStep x x r hr le_rfl (by simpa only [dist_self] using hr.le)
  have hMain₂ := hStep y x r hr le_rfl (by change dist y x ≤ dist x y; rw [dist_comm])
  have hTriangle : |u x - u y| ≤ |u x - av x r| + |av x r - av x (2 * r)| +
      |av y r - av x (2 * r)| + |u y - av y r| := by
    simp only [← Real.dist_eq, dist_comm (av y r) (av x (2 * r)), dist_comm (u y) (av y r)]
    linarith only [dist_triangle (u x) (av x r) (u y), dist_triangle (av x r) (av x (2 * r)) (u y),
      dist_triangle (av x (2 * r)) (av y r) (u y)]
  change |u x - u y| ≤ C * r * (H x + H y)
  have hPos (z : X) : 0 ≤ M ^ p⁻¹ * H z * r := by positivity [hH z]
  dsimp only [C]
  nlinarith only [hTriangle, hTail x, hTail y, hMain₁, hMain₂, hPos x, hPos y]

end WalkDimensions
