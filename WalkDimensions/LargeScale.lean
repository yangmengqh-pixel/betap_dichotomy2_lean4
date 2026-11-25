import WalkDimensions.BallIntegration

/-!
# Large-scale Besov control on Ahlfors-regular spaces

The global moment bound used in (5.3) of arXiv:2611.02422v1.
-/

open MeasureTheory Metric Set Function
open scoped ENNReal

namespace WalkDimensions

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem ennreal_abs_sub_rpow_le (a b : ℝ) {p : ℝ} (hp : 0 ≤ p) :
    ENNReal.ofReal |a - b| ^ p ≤ (2 : ℝ≥0∞) ^ p *
      (ENNReal.ofReal |a| ^ p + ENNReal.ofReal |b| ^ p) := by
  have hab : |a - b| ≤ 2 * max |a| |b| := by
    calc
      _ ≤ |a| + |b| := abs_sub _ _
      _ ≤ max |a| |b| + max |a| |b| := add_le_add (le_max_left _ _) (le_max_right _ _)
      _ = _ := (two_mul _).symm
  have hm : ENNReal.ofReal (max |a| |b|) ^ p ≤
      ENNReal.ofReal |a| ^ p + ENNReal.ofReal |b| ^ p := by
    rcases le_total |a| |b| with h | h
    · rw [max_eq_right h]; exact le_add_of_nonneg_left bot_le
    · rw [max_eq_left h]; exact le_add_of_nonneg_right bot_le
  calc
    _ ≤ ENNReal.ofReal (2 * max |a| |b|) ^ p :=
      ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hab) hp
    _ = (2 : ℝ≥0∞) ^ p * ENNReal.ofReal (max |a| |b|) ^ p := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.mul_rpow_of_nonneg _ _ hp]
      norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left hm bot_le

/-- The integral of ball averages of a nonnegative function is bounded by
a fixed multiple of its integral, uniformly in the radius. -/
theorem lintegral_normalizedBall_le {m : Measure X} [SFinite m] [SecondCountableTopology X]
    {d C r : ℝ} (hC : 0 < C) (hr : 0 < r)
    (hvol : ∀ x, ENNReal.ofReal (r ^ d / C) ≤ m (ball x r) ∧
      m (ball x r) ≤ ENNReal.ofReal (C * r ^ d))
    {f : X → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, ∫⁻ y, f y ∂normalizedBall m x r ∂m ≤
      ENNReal.ofReal (C * C) * ∫⁻ y, f y ∂m := by
  let v := ENNReal.ofReal (r ^ d / C)
  have hv : 0 < v := ENNReal.ofReal_pos.mpr (div_pos (Real.rpow_pos_of_pos hr _) hC)
  have hvtop : v ≠ ∞ := ENNReal.ofReal_ne_top
  let B : Set (X × X) := {z | dist z.2 z.1 < r}
  have hB : MeasurableSet B :=
    measurableSet_lt (continuous_snd.dist continuous_fst).measurable measurable_const
  have hfB : Measurable (B.indicator (fun z : X × X ↦ f z.2)) :=
    (hf.comp measurable_snd).indicator hB
  have hfirst (x : X) : (∫⁻ y, f y ∂normalizedBall m x r) ≤
      v⁻¹ * ∫⁻ y, B.indicator (fun z : X × X ↦ f z.2) (x, y) ∂m := by
    rw [normalizedBall, lintegral_smul_measure, smul_eq_mul, ← lintegral_indicator measurableSet_ball]
    have he : (fun y ↦ (ball x r).indicator f y) =
        fun y ↦ B.indicator (fun z : X × X ↦ f z.2) (x, y) := by
      ext y
      by_cases hy : y ∈ ball x r
      · have hxy : (x, y) ∈ B := hy
        rw [indicator_of_mem hy, indicator_of_mem hxy]
      · have hxy : (x, y) ∉ B := hy
        rw [indicator_of_notMem hy, indicator_of_notMem hxy]
    rw [he]
    exact mul_le_mul_of_nonneg_right (ENNReal.inv_le_inv.mpr (hvol x).1) bot_le
  calc
    _ ≤ ∫⁻ x, v⁻¹ * ∫⁻ y, B.indicator (fun z : X × X ↦ f z.2) (x, y) ∂m ∂m :=
      lintegral_mono hfirst
    _ = v⁻¹ * ∫⁻ y, ∫⁻ x, B.indicator (fun z : X × X ↦ f z.2) (x, y) ∂m ∂m := by
      rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hv.ne')]
      congr 1
      exact lintegral_lintegral_swap
        (f := fun x y ↦ B.indicator (fun z : X × X ↦ f z.2) (x, y)) hfB.aemeasurable
    _ ≤ _ := by
      rw [← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hv.ne')]
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_mono
      intro y
      have hfun : (fun x ↦ B.indicator (fun z : X × X ↦ f z.2) (x, y)) =
          (ball y r).indicator (fun _ ↦ f y) := by
        ext x
        by_cases hx : x ∈ ball y r
        · have hxy : (x, y) ∈ B := by simpa only [B, mem_ofPred_eq, mem_ball, dist_comm] using hx
          rw [indicator_of_mem hx, indicator_of_mem hxy]
        · have hxy : (x, y) ∉ B := by simpa only [B, mem_ofPred_eq, mem_ball, dist_comm] using hx
          rw [indicator_of_notMem hx, indicator_of_notMem hxy]
      change v⁻¹ * (∫⁻ x, B.indicator (fun z : X × X ↦ f z.2) (x, y) ∂m) ≤ _
      rw [hfun, lintegral_indicator measurableSet_ball, lintegral_const, Measure.restrict_apply_univ,
        mul_comm (f y), ← mul_assoc]
      have hvol' : m (ball y r) ≤ ENNReal.ofReal (C * C) * v := by
        apply (hvol y).2.trans_eq
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ C * C)]
        congr 1
        field_simp
      apply mul_le_mul_of_nonneg_right _ bot_le
      calc
        _ ≤ v⁻¹ * (ENNReal.ofReal (C * C) * v) :=
          mul_le_mul_of_nonneg_left hvol' bot_le
        _ = _ := by rw [mul_left_comm, ENNReal.inv_mul_cancel hv.ne' hvtop, mul_one]

omit [BorelSpace X] in
private theorem besovEnergy_zero_scale_le_of_ball_average {m : Measure X}
    [ProperSpace X] [IsFiniteMeasureOnCompacts m] [m.IsOpenPosMeasure]
    {p r : ℝ} (hp : 0 ≤ p) (hr : 0 < r) {D : ℝ≥0∞}
    (havg : ∀ f : X → ℝ≥0∞, Measurable f →
      (∫⁻ x, ∫⁻ y, f y ∂normalizedBall m x r ∂m) ≤ D * ∫⁻ y, f y ∂m)
    {u : X → ℝ} (hu : Measurable u) :
    besovEnergy m p 0 univ u r ≤
      (2 : ℝ≥0∞) ^ p * (1 + D) * ∫⁻ x, ENNReal.ofReal |u x| ^ p ∂m := by
  let f : X → ℝ≥0∞ := fun x ↦ ENNReal.ofReal |u x| ^ p
  let K : ℝ≥0∞ := (2 : ℝ≥0∞) ^ p
  have hK : K ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hp (by norm_num)
  have hf : Measurable f := ((continuous_abs.measurable.comp hu).ennreal_ofReal).pow_const _
  have hpoint (x : X) : ballMoment m p u r x ≤
      K * (f x + ∫⁻ y, f y ∂normalizedBall m x r) := by
    unfold ballMoment
    calc
      _ ≤ ∫⁻ y, K * (f x + f y) ∂normalizedBall m x r :=
        lintegral_mono fun y ↦ ennreal_abs_sub_rpow_le (u x) (u y) hp
      _ = _ := by
        rw [lintegral_const_mul' _ _ hK, lintegral_add_left measurable_const, lintegral_const,
          normalizedBall_univ x hr, mul_one]
  simp only [besovEnergy, neg_zero, ENNReal.rpow_zero, one_mul, Measure.restrict_univ]
  calc
    _ ≤ ∫⁻ x, K * (f x + ∫⁻ y, f y ∂normalizedBall m x r) ∂m := lintegral_mono hpoint
    _ = K * ((∫⁻ x, f x ∂m) + ∫⁻ x, ∫⁻ y, f y ∂normalizedBall m x r ∂m) := by
      rw [lintegral_const_mul' _ _ hK, lintegral_add_left hf]
    _ ≤ K * ((∫⁻ x, f x ∂m) + D * ∫⁻ x, f x ∂m) :=
      mul_le_mul_of_nonneg_left (add_le_add_right (havg f hf) _) bot_le
    _ = _ := by rw [mul_assoc, add_mul, one_mul]

/-- The uniform large-scale bound on an Ahlfors-regular space. -/
theorem besovEnergy_zero_scale_le {m : Measure X} [SFinite m] [SecondCountableTopology X]
    [ProperSpace X] [IsFiniteMeasureOnCompacts m] [m.IsOpenPosMeasure]
    {d C p r : ℝ} (hC : 0 < C) (hp : 0 ≤ p) (hr : 0 < r)
    (hvol : ∀ x, ENNReal.ofReal (r ^ d / C) ≤ m (ball x r) ∧
      m (ball x r) ≤ ENNReal.ofReal (C * r ^ d))
    {u : X → ℝ} (hu : Measurable u) :
    besovEnergy m p 0 univ u r ≤
      (2 : ℝ≥0∞) ^ p * (1 + ENNReal.ofReal (C * C)) *
        ∫⁻ x, ENNReal.ofReal |u x| ^ p ∂m :=
  besovEnergy_zero_scale_le_of_ball_average hp hr
    (fun _ hf ↦ lintegral_normalizedBall_le hC hr hvol hf) hu

/-- The unscaled global increment moment on a doubling space. -/
theorem besovEnergy_zero_scale_le_of_doubling {m : Measure X} [SFinite m] [SecondCountableTopology X]
    [ProperSpace X] [IsFiniteMeasureOnCompacts m] [m.IsOpenPosMeasure]
    {p r : ℝ} (hp : 0 ≤ p) (hr : 0 < r) {D : ℝ≥0∞}
    (hD : ∀ x r, 0 < r → m (ball x (2 * r)) ≤ D * m (ball x r))
    {u : X → ℝ} (hu : Measurable u) :
    besovEnergy m p 0 univ u r ≤
      (2 : ℝ≥0∞) ^ p * (1 + D) * ∫⁻ x, ENNReal.ofReal |u x| ^ p ∂m :=
  besovEnergy_zero_scale_le_of_ball_average hp hr
    (fun f _ ↦ lintegral_normalizedBall_le_of_doubling hD hr f) hu

end WalkDimensions
