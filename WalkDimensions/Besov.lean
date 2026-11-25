import WalkDimensions.Geometry
import WalkDimensions.LintegralHolderMass
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Local Besov energies

The scale-dependent integral in Section 3 of arXiv:2611.02422v1, and the
power comparisons used in Sections 4 and 5.
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal Topology

namespace WalkDimensions

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The probability normalization of the reference measure on an open ball
when that ball has positive finite mass. -/
noncomputable def normalizedBall (m : Measure X) (x : X) (r : ℝ) : Measure X :=
  (m (ball x r))⁻¹ • m.restrict (ball x r)

omit [BorelSpace X] in
theorem normalizedBall_univ {m : Measure X} [ProperSpace X]
    [IsFiniteMeasureOnCompacts m] [m.IsOpenPosMeasure] (x : X) {r : ℝ} (hr : 0 < r) :
    normalizedBall m x r univ = 1 := by
  simp only [normalizedBall, smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (measure_ball_pos m x hr).ne' measure_ball_ne_top

/-- The (p)-th moment of the increments with one argument fixed at the centre. -/
noncomputable def ballMoment (m : Measure X) (p : ℝ) (u : X → ℝ)
    (r : ℝ) (x : X) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal |u x - u y| ^ p ∂normalizedBall m x r

/-- The local scale-dependent Besov energy from Section 3.
The nonnegative integral takes values in the extended nonnegative reals. -/
noncomputable def besovEnergy (m : Measure X) (p β : ℝ) (U : Set X)
    (u : X → ℝ) (r : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal r) ^ (-β) * ∫⁻ x in U, ballMoment m p u r x ∂m

omit [BorelSpace X] in
/-- The Besov integral is independent of the almost-everywhere representative. -/
theorem besovEnergy_congr_ae {m : Measure X} {u v : X → ℝ}
    (h : u =ᵐ[m] v) (p β : ℝ) (U : Set X) (r : ℝ) :
    besovEnergy m p β U u r = besovEnergy m p β U v r := by
  unfold besovEnergy
  congr 1
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae h] with x hx
  simp only [ballMoment, normalizedBall, lintegral_smul_measure, smul_eq_mul]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae (s := ball x r) h] with y hy
  rw [hx, hy]

/-- Membership in (B^{p,α}(X)) for a representative of an (L^p) class. -/
def InBesov (m : Measure X) (p α : ℝ) (u : X → ℝ) : Prop :=
  MemLp u (ENNReal.ofReal p) m ∧ (⨆ r : Ioi (0 : ℝ),
    besovEnergy m p (p * α) univ u r) < ∞

/-- The critical Besov exponent from Section 3. -/
noncomputable def criticalBesovExponent (m : Measure X) (p : ℝ) : ℝ≥0∞ :=
  ⨆ α : Ioi (0 : ℝ), ⨆ (_ : ∃ u, InBesov m p α u ∧
    ¬ ∃ c : ℝ, u =ᵐ[m] fun _ ↦ c), ENNReal.ofReal (α : ℝ)

omit [BorelSpace X] in
theorem le_criticalBesovExponent {m : Measure X} {p α : ℝ} {u : X → ℝ}
    (hα : 0 < α) (h : InBesov m p α u) (hnonconst : ¬ ∃ c : ℝ, u =ᵐ[m] fun _ ↦ c) :
    ENNReal.ofReal α ≤ criticalBesovExponent m p := by
  exact le_iSup_of_le ⟨α, hα⟩ (le_iSup_of_le ⟨u, h, hnonconst⟩ le_rfl)

theorem measurable_ballMoment {m : Measure X} [SFinite m] [SecondCountableTopology X] {u : X → ℝ}
    (hu : Measurable u) (p r : ℝ) : Measurable (ballMoment m p u r) := by
  let D : Set (X × X) := {z | dist z.2 z.1 < r}
  have hD : MeasurableSet D :=
    measurableSet_lt (continuous_snd.dist continuous_fst).measurable measurable_const
  have hmass : Measurable (fun x : X ↦ m (ball x r)) :=
    measurable_measure_prodMk_left hD
  let f : X × X → ℝ≥0∞ := fun z ↦ ENNReal.ofReal |u z.1 - u z.2| ^ p
  have hf : Measurable f :=
    (continuous_abs.measurable.comp ((hu.comp measurable_fst).sub
      (hu.comp measurable_snd))).ennreal_ofReal.pow_const _
  have hi : Measurable (fun x : X ↦ ∫⁻ y, D.indicator f (x, y) ∂m) :=
    Measurable.lintegral_prod_right (f := fun x y ↦ D.indicator f (x, y)) (hf.indicator hD)
  convert hmass.inv.mul hi using 1
  ext x
  rw [ballMoment, normalizedBall, lintegral_smul_measure, smul_eq_mul]
  congr 1
  rw [← lintegral_indicator measurableSet_ball]
  apply lintegral_congr
  intro y
  by_cases hy : y ∈ ball x r
  · have hxy : (x, y) ∈ D := hy
    rw [indicator_of_mem hy, indicator_of_mem hxy]
  · have hxy : (x, y) ∉ D := hy
    rw [indicator_of_notMem hy, indicator_of_notMem hxy]

omit [MetricSpace X] [BorelSpace X] in
private theorem lintegral_rpow_le {m : Measure X} {p q : ℝ}
    (hp : 0 < p) (hpq : p < q) {f : X → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ^ p ∂m ≤ (∫⁻ x, f x ^ q ∂m) ^ (p / q) *
      m univ ^ (1 - p / q) := by
  have hq : 0 < q := hp.trans hpq
  have ht : 1 < q / p := (lt_div_iff₀ hp).2 (by simpa using hpq)
  have hθ : 0 < p / q := div_pos hp hq
  have hm : (q / p) * (p / q) = 1 := by
    field_simp
  have h := ENNReal.rpow_le_rpow
    (lintegral_rpow_le_mass_rpow_mul (μ := m) ht (hf.pow_const p).aemeasurable) hθ.le
  simp only [← ENNReal.rpow_mul, hm, ENNReal.rpow_one] at h
  rw [ENNReal.mul_rpow_of_nonneg _ _ hθ.le, ← ENNReal.rpow_mul, mul_comm] at h
  have hpq' : p * (q / p) = q := by field_simp
  have ht' : (q / p - 1) * (p / q) = 1 - p / q := by rw [sub_mul, hm, one_mul]
  simpa only [← ENNReal.rpow_mul, hpq', ht'] using h

/-- The two applications of Hölder's inequality in (4.1), before scaling. -/
theorem lintegral_ballMoment_le {m : Measure X} [SFinite m] [ProperSpace X] [SecondCountableTopology X]
    [IsFiniteMeasureOnCompacts m] [m.IsOpenPosMeasure] {p q r : ℝ}
    (hp : 0 < p) (hpq : p < q) (hr : 0 < r) {u : X → ℝ} (hu : Measurable u) (U : Set X) :
    ∫⁻ x in U, ballMoment m p u r x ∂m ≤
      (∫⁻ x in U, ballMoment m q u r x ∂m) ^ (p / q) * m U ^ (1 - p / q) := by
  have hmoment (x : X) : ballMoment m p u r x ≤ ballMoment m q u r x ^ (p / q) := by
    have hf : Measurable (fun y ↦ ENNReal.ofReal |u x - u y|) :=
      (continuous_abs.measurable.comp ((measurable_const (a := u x)).sub hu)).ennreal_ofReal
    simpa only [ballMoment, normalizedBall_univ x hr, ENNReal.one_rpow, mul_one] using
      (lintegral_rpow_le (m := normalizedBall m x r) hp hpq hf)
  have hq : 0 < q := hp.trans hpq
  have hθ : 0 < p / q := div_pos hp hq
  have hθ₁ : p / q < 1 := (div_lt_iff₀ hq).2 (by simpa using hpq)
  calc
    _ ≤ ∫⁻ x in U, ballMoment m q u r x ^ (p / q) ∂m := lintegral_mono hmoment
    _ ≤ _ := by
      simpa only [ENNReal.rpow_one, div_one, Measure.restrict_apply_univ] using
        (lintegral_rpow_le (m := m.restrict U) hθ hθ₁ (measurable_ballMoment hu q r))

/-- Formula (4.1) at matching normalized exponents. -/
theorem besovEnergy_le_of_equal_ratio {m : Measure X} [SFinite m] [ProperSpace X] [SecondCountableTopology X]
    [IsFiniteMeasureOnCompacts m] [m.IsOpenPosMeasure] {p q βp βq r : ℝ}
    (hp : 0 < p) (hpq : p < q) (hr : 0 < r) (hβ : βp / p = βq / q)
    {u : X → ℝ} (hu : Measurable u) (U : Set X) :
    besovEnergy m p βp U u r ≤
      besovEnergy m q βq U u r ^ (p / q) * m U ^ (1 - p / q) := by
  have hq : 0 < q := hp.trans hpq
  have hθ : 0 ≤ p / q := (div_pos hp hq).le
  have hscale : -βq * (p / q) = -βp := by
    have he := (div_eq_div_iff hp.ne' hq.ne').1 hβ
    rw [← mul_div_assoc]
    apply (div_eq_iff hq.ne').2
    linarith
  unfold besovEnergy
  rw [ENNReal.mul_rpow_of_nonneg _ _ hθ, ← ENNReal.rpow_mul, hscale, mul_assoc]
  exact mul_le_mul_of_nonneg_left (lintegral_ballMoment_le hp hpq hr hu U) bot_le

/-- A uniform bound on increments at a given scale increases the power in
the Besov integral, retaining the explicit factor used in Section 5. -/
private theorem besovEnergy_le_of_increment_bound_ae {m : Measure X} {p q βp βq r M : ℝ}
    (hp : 0 ≤ p) (hpq : p ≤ q) (hr : 0 < r) {u : X → ℝ} (U : Set X)
    (hM : ∀ᵐ x ∂m.restrict U, ∀ y, dist y x < r → |u x - u y| ≤ M) :
    besovEnergy m q βq U u r ≤
      (ENNReal.ofReal r) ^ (βp - βq) * (ENNReal.ofReal M) ^ (q - p) *
        besovEnergy m p βp U u r := by
  have hMfinite : (ENNReal.ofReal M) ^ (q - p) ≠ ∞ :=
    (ENNReal.rpow_lt_top_of_nonneg (sub_nonneg.mpr hpq) ENNReal.ofReal_ne_top).ne
  have hball : ∀ᵐ x ∂m.restrict U, ballMoment m q u r x ≤
      (ENNReal.ofReal M) ^ (q - p) * ballMoment m p u r x := by
    filter_upwards [hM] with x hx
    simp only [ballMoment, normalizedBall, lintegral_smul_measure, smul_eq_mul]
    rw [mul_left_comm, ← lintegral_const_mul' _ _ hMfinite]
    refine mul_le_mul_of_nonneg_left (lintegral_mono_ae ?_) bot_le
    filter_upwards [ae_restrict_mem (μ := m) (measurableSet_ball (x := x) (ε := r))] with y hy
    have he : q = q - p + p := by ring
    conv_lhs => rw [he]
    rw [ENNReal.rpow_add_of_nonneg _ _ (sub_nonneg.mpr hpq) hp]
    exact mul_le_mul_of_nonneg_right (ENNReal.rpow_le_rpow
      (ENNReal.ofReal_le_ofReal (hx y hy)) (sub_nonneg.mpr hpq)) bot_le
  have hscale : (ENNReal.ofReal r) ^ (βp - βq) * (ENNReal.ofReal r) ^ (-βp) =
      (ENNReal.ofReal r) ^ (-βq) := by
    rw [← ENNReal.rpow_add _ _ (ENNReal.ofReal_ne_zero_iff.mpr hr) ENNReal.ofReal_ne_top]
    congr 1
    ring
  unfold besovEnergy
  rw [mul_right_comm _ _ ((ENNReal.ofReal r) ^ (-βp) * _), ← mul_assoc, hscale, mul_assoc,
    ← lintegral_mul_const' _ _ hMfinite]
  simp_rw [mul_comm _ ((ENNReal.ofReal M) ^ (q - p))]
  exact mul_le_mul_of_nonneg_left (lintegral_mono_ae hball) bot_le

/-- Only increments based at points in the integration region enter the bound. -/
theorem besovEnergy_le_of_increment_bound_on {m : Measure X} {p q βp βq r M : ℝ}
    (hp : 0 ≤ p) (hpq : p ≤ q) (hr : 0 < r) {u : X → ℝ} {U : Set X}
    (hU : MeasurableSet U) (hM : ∀ x ∈ U, ∀ y, dist y x < r → |u x - u y| ≤ M) :
    besovEnergy m q βq U u r ≤
      (ENNReal.ofReal r) ^ (βp - βq) * (ENNReal.ofReal M) ^ (q - p) *
        besovEnergy m p βp U u r :=
  besovEnergy_le_of_increment_bound_ae hp hpq hr U ((ae_restrict_mem hU).mono hM)

/-- A global increment bound may be used on any integration region. -/
theorem besovEnergy_le_of_increment_bound {m : Measure X} {p q βp βq r M : ℝ}
    (hp : 0 ≤ p) (hpq : p ≤ q) (hr : 0 < r) {u : X → ℝ} (U : Set X)
    (hM : ∀ x y, dist y x < r → |u x - u y| ≤ M) :
    besovEnergy m q βq U u r ≤
      (ENNReal.ofReal r) ^ (βp - βq) * (ENNReal.ofReal M) ^ (q - p) *
        besovEnergy m p βp U u r := by
  exact besovEnergy_le_of_increment_bound_ae hp hpq hr U
    (Eventually.of_forall hM)

end WalkDimensions
