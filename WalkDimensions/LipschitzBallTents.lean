import WalkDimensions.DiscreteOscillation
import WalkDimensions.PointwiseSlope

/-!
# Lipschitz interpolants of a finite family of ball averages
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal NNReal

namespace WalkDimensions

variable {X : Type*} [MetricSpace X]

noncomputable def ballTent (r : ℝ) (z x : X) : ℝ :=
  max 0 (min 1 (2 - dist x z / r))

theorem ballTent_nonneg (r : ℝ) (z x : X) : 0 ≤ ballTent r z x := le_max_left _ _

theorem ballTent_le_one (r : ℝ) (z x : X) : ballTent r z x ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem ballTent_eq_one {r : ℝ} (hr : 0 < r) {z x : X} (hx : x ∈ ball z r) :
    ballTent r z x = 1 := by
  unfold ballTent
  rw [min_eq_left (by
    have h := (div_lt_one hr).mpr (mem_ball.mp hx)
    linarith), max_eq_right zero_le_one]

theorem ballTent_eq_zero {r : ℝ} (hr : 0 < r) {z x : X} (hx : 2 * r ≤ dist x z) :
    ballTent r z x = 0 := by
  have h := (le_div_iff₀ hr).mpr hx
  simp only [ballTent, max_eq_left ((min_le_right _ _).trans (sub_nonpos.mpr h))]

theorem abs_ballTent_sub_le {r : ℝ} (hr : 0 < r) (z x y : X) :
    |ballTent r z x - ballTent r z y| ≤ dist x y / r := by
  let f (a : ℝ) := max 0 (min 1 a)
  have hf : LipschitzWith 1 f := by
    have he : f = fun a : ℝ ↦ max (min (id a) 1) 0 := by
      funext a
      change max 0 (min 1 a) = max (min a 1) 0
      rw [min_comm 1, max_comm 0]
    rw [he]
    exact (LipschitzWith.id.min_const (1 : ℝ)).max_const 0
  have h := hf.dist_le_mul (2 - dist x z / r) (2 - dist y z / r)
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul] at h
  have hB : |dist x z - dist y z| ≤ dist x y :=
    abs_dist_sub_le x y z
  apply h.trans
  rw [sub_sub_sub_cancel_left, ← sub_div, abs_div, abs_of_pos hr, abs_sub_comm]
  exact div_le_div_of_nonneg_right hB hr.le

noncomputable def tentDenominator (t : Finset X) (r : ℝ) (x : X) : ℝ :=
  max 1 (∑ z ∈ t, ballTent r z x)

noncomputable def tentInterpolant (t : Finset X) (r : ℝ) (a : X → ℝ) (x : X) : ℝ :=
  ∑ z ∈ t, a z * (ballTent r z x / tentDenominator t r x)

theorem tentDenominator_ge_one (t : Finset X) (r : ℝ) (x : X) :
    1 ≤ tentDenominator t r x := le_max_left _ _

theorem tentDenominator_eq_sum (t : Finset X) {r : ℝ} (hr : 0 < r)
    {z x : X} (hz : z ∈ t) (hx : x ∈ ball z r) :
    tentDenominator t r x = ∑ z ∈ t, ballTent r z x := by
  apply max_eq_right
  rw [← ballTent_eq_one hr hx]
  exact Finset.single_le_sum (f := fun z ↦ ballTent r z x) (fun _ _ ↦ ballTent_nonneg _ _ _) hz

private theorem abs_tent_fraction_sub_le (t N : Finset X) {r : ℝ} (hr : 0 < r)
    (x y z : X) (hN : N ⊆ t)
    (hZero : ∀ w ∈ t, w ∉ N → ballTent r w x = 0 ∧ ballTent r w y = 0) :
    |ballTent r z x / tentDenominator t r x - ballTent r z y / tentDenominator t r y| ≤
      ((N.card : ℝ) + 1) * (dist x y / r) := by
  let B := tentDenominator t r x
  let C := tentDenominator t r y
  have hB := tentDenominator_ge_one t r x
  have hC := tentDenominator_ge_one t r y
  have hSumX : ∑ z ∈ N, ballTent r z x = ∑ z ∈ t, ballTent r z x :=
    Finset.sum_subset hN fun w hw hW ↦ (hZero w hw hW).1
  have hSumY : ∑ z ∈ N, ballTent r z y = ∑ z ∈ t, ballTent r z y :=
    Finset.sum_subset hN fun w hw hW ↦ (hZero w hw hW).2
  have hDen : |B - C| ≤ (N.card : ℝ) * (dist x y / r) := by
    have h := (LipschitzWith.id.max_const (1 : ℝ)).dist_le_mul
      (∑ z ∈ N, ballTent r z x) (∑ z ∈ N, ballTent r z y)
    simp only [Real.dist_eq, NNReal.coe_one, one_mul, id_eq] at h
    change |max 1 (∑ z ∈ t, ballTent r z x) - max 1 (∑ z ∈ t, ballTent r z y)| ≤ _
    rw [← hSumX, ← hSumY]
    rw [max_comm _ 1, max_comm _ 1] at h
    apply h.trans
    rw [← Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      ((Finset.sum_le_sum fun j hj ↦ abs_ballTent_sub_le hr j x y).trans_eq (by simp [nsmul_eq_mul]))
  have hBC : 1 ≤ B * C := one_le_mul_of_one_le_of_one_le hB hC
  have hB₀ : 0 < B := zero_lt_one.trans_le hB
  have hC₀ : 0 < C := zero_lt_one.trans_le hC
  let a := ballTent r z x
  let b := ballTent r z y
  change |a / B - b / C| ≤ _
  have hEq : a / B - b / C = (a - b) / B + b * ((C - B) / (B * C)) := by
    field_simp [hB₀.ne', hC₀.ne']
    ring
  rw [hEq]
  apply (abs_add_le _ _).trans
  rw [abs_div, abs_of_pos hB₀, abs_mul, abs_of_nonneg (ballTent_nonneg _ _ _),
    abs_div, abs_of_pos (mul_pos hB₀ hC₀), abs_sub_comm C B]
  have h₁ := (div_le_self (abs_nonneg (a - b)) hB).trans (abs_ballTent_sub_le hr z x y)
  have h₂ := (div_le_self (abs_nonneg (B - C)) hBC).trans hDen
  have h₃ := mul_le_mul (ballTent_le_one r z y) h₂ (div_nonneg (abs_nonneg _) (by positivity)) zero_le_one
  nlinarith only [h₁, h₃]

theorem tentInterpolant_lipschitz (t : Finset X) {r : ℝ} (hr : 0 < r) (a : X → ℝ) :
    ∃ K : ℝ≥0, LipschitzWith K (tentInterpolant t r a) := by
  let C := (∑ z ∈ t, |a z|) * ((t.card : ℝ) + 1) / r
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact div_nonneg (mul_nonneg (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _) (by positivity)) hr.le
  refine ⟨⟨C, hC⟩, LipschitzWith.of_dist_le_mul (fun x y ↦ ?_)⟩
  rw [Real.dist_eq, tentInterpolant, tentInterpolant, ← Finset.sum_sub_distrib]
  change _ ≤ C * dist x y
  simp_rw [← mul_sub]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ z ∈ t, |a z| * (((t.card : ℝ) + 1) * (dist x y / r)) := by
      apply Finset.sum_le_sum
      intro z hz
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (abs_tent_fraction_sub_le t t hr x y z subset_rfl (fun _ h ht ↦ (ht h).elim)) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; dsimp only [C]; ring

theorem tentInterpolant_eq_const (t : Finset X) {r : ℝ} (hr : 0 < r) (a : X → ℝ)
    {x z : X} (hz : z ∈ t) (hx : x ∈ ball z r) (c : ℝ)
    (hConst : ∀ y ∈ t, ballTent r y x ≠ 0 → a y = c) :
    tentInterpolant t r a x = c := by
  unfold tentInterpolant
  calc
    _ = ∑ y ∈ t, c * (ballTent r y x / tentDenominator t r x) := by
      apply Finset.sum_congr rfl
      intro y hy
      by_cases h : ballTent r y x = 0
      · simp only [h, zero_div, mul_zero]
      · rw [hConst y hy h]
    _ = _ := by
      rw [← Finset.mul_sum, ← Finset.sum_div, ← tentDenominator_eq_sum t hr hz hx,
        div_self (zero_lt_one.trans_le (tentDenominator_ge_one _ _ _)).ne', mul_one]

/-- In the region covered by the tents, the increments depend only on
differences of the neighboring coefficients. -/
theorem abs_tentInterpolant_sub_le (t N : Finset X) {r : ℝ} (hr : 0 < r) (a : X → ℝ)
    {x y z w : X} (hz : z ∈ t) (hw : w ∈ t) (hx : x ∈ ball z r) (hy : y ∈ ball w r)
    (hN : N ⊆ t) (hZero : ∀ j ∈ t, j ∉ N → ballTent r j x = 0 ∧ ballTent r j y = 0) :
    |tentInterpolant t r a x - tentInterpolant t r a y| ≤
      ((N.card : ℝ) + 1) * (dist x y / r) * ∑ j ∈ N, |a j - a z| := by
  have hShift (u : X) (hU : ∃ v ∈ t, u ∈ ball v r) :
      tentInterpolant t r a u = tentInterpolant t r (fun v ↦ a v - a z) u + a z := by
    obtain ⟨v, hv, hu⟩ := hU
    have hEq := tentInterpolant_eq_const t hr (fun _ ↦ a z) hv hu (a z) (fun _ _ _ ↦ rfl)
    calc
      _ = tentInterpolant t r (fun v ↦ a v - a z) u + tentInterpolant t r (fun _ ↦ a z) u := by
        simp only [tentInterpolant, sub_mul, Finset.sum_sub_distrib, sub_add_cancel]
      _ = _ := by rw [hEq]
  rw [hShift x ⟨z, hz, hx⟩, hShift y ⟨w, hw, hy⟩, add_sub_add_right_eq_sub]
  unfold tentInterpolant
  have hsum (u : X) (hu : u = x ∨ u = y) :
      (∑ j ∈ N, (a j - a z) * (ballTent r j u / tentDenominator t r u)) =
        ∑ j ∈ t, (a j - a z) * (ballTent r j u / tentDenominator t r u) := by
    apply Finset.sum_subset hN
    intro j hj hJn
    obtain ⟨ha, hb⟩ := hZero j hj hJn
    rcases hu with rfl | rfl <;> simp only [ha, hb, zero_div, mul_zero]
  rw [← hsum x (Or.inl rfl), ← hsum y (Or.inr rfl), ← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  rw [abs_mul, mul_comm (_ * (_ / _))]
  exact mul_le_mul_of_nonneg_left (abs_tent_fraction_sub_le t N hr x y j hN hZero) (abs_nonneg _)

end WalkDimensions
