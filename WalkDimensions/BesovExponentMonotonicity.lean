import WalkDimensions.Besov
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Monotonicity of the unnormalized critical Besov exponent

The monotonicity of `p * αₚ` in Lemma 3.1(ii). An injective bounded
Lipschitz composition preserves nonconstancy and controls higher moments.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal NNReal

namespace WalkDimensions

private theorem lipschitzWith_arctan : LipschitzWith 1 Real.arctan := by
  apply lipschitzWith_of_nnNorm_deriv_le Real.differentiable_arctan
  intro x
  change ‖deriv Real.arctan x‖ ≤ (1 : ℝ)
  rw [Real.deriv_arctan, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply div_le_one_of_le₀ _ (by positivity)
  linarith only [sq_nonneg x]

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] {m : Measure X}

/-- Composition with a contraction decreases the Besov energy. -/
theorem besovEnergy_lipschitz_comp_le {p β : ℝ} (hp : 0 ≤ p)
    {φ : ℝ → ℝ} (hφ : LipschitzWith 1 φ) (u : X → ℝ) (r : ℝ) :
    besovEnergy m p β univ (φ ∘ u) r ≤ besovEnergy m p β univ u r := by
  unfold besovEnergy
  apply mul_le_mul_of_nonneg_left _ bot_le
  apply lintegral_mono
  intro x
  unfold ballMoment
  apply lintegral_mono
  intro y
  have h := lipschitzWith_iff_dist_le_mul.mp hφ (u x) (u y)
  simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h
  exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal h) hp

omit [MetricSpace X] in
private theorem memLp_arctan_comp {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q)
    {u : X → ℝ} (hu : MemLp u (ENNReal.ofReal p) m) :
    MemLp (Real.arctan ∘ u) (ENNReal.ofReal q) m := by
  have hq : 0 < q := hp.trans_le hpq
  have hmeas : AEStronglyMeasurable (Real.arctan ∘ u) m :=
    Real.continuous_arctan.comp_aestronglyMeasurable hu.aestronglyMeasurable
  rw [memLp_iff]
  apply (eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top
    (ENNReal.ofReal_ne_zero_iff.mpr hq) ENNReal.ofReal_ne_top hmeas).2
  simp only [ENNReal.toReal_ofReal hq.le, comp_apply, Real.eNorm_eq_ofReal_abs]
  let D := (ENNReal.ofReal (Real.pi / 2)) ^ (q - p)
  have hDfin : D ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (sub_nonneg.mpr hpq) ENNReal.ofReal_ne_top
  have hbound (x : X) : ENNReal.ofReal |Real.arctan (u x)| ^ q ≤ D * ENNReal.ofReal |u x| ^ p := by
    have habs : |Real.arctan (u x)| ≤ Real.pi / 2 :=
      abs_le.mpr ⟨(Real.neg_pi_div_two_lt_arctan _).le, (Real.arctan_lt_pi_div_two _).le⟩
    conv_lhs => rw [show q = (q - p) + p by ring]
    rw [ENNReal.rpow_add_of_nonneg _ _ (sub_nonneg.mpr hpq) hp.le]
    exact mul_le_mul (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal habs) (sub_nonneg.mpr hpq))
      (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal Real.abs_arctan_le_abs) hp.le) bot_le bot_le
  have hLpint : (∫⁻ x, ENNReal.ofReal |u x| ^ p ∂m) < ∞ := by
    simpa only [ENNReal.toReal_ofReal hp.le, Real.eNorm_eq_ofReal_abs] using
      lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top (ENNReal.ofReal_ne_zero_iff.mpr hp)
        ENNReal.ofReal_ne_top hu.eLpNorm_lt_top
  apply lt_of_le_of_lt (lintegral_mono hbound)
  rw [lintegral_const_mul' _ _ hDfin]
  exact (ENNReal.mul_ne_top hDfin hLpint.ne).lt_top

variable [BorelSpace X]

private theorem inBesov_arctan_comp {p q α : ℝ} (hp : 0 < p) (hpq : p ≤ q)
    {u : X → ℝ} (hu : InBesov m p α u) :
    InBesov m q (p * α / q) (Real.arctan ∘ u) := by
  refine ⟨memLp_arctan_comp hp hpq hu.1, ?_⟩
  have hq : 0 < q := hp.trans_le hpq
  have he : q * (p * α / q) = p * α := by field_simp
  rw [he]
  let A := (ENNReal.ofReal Real.pi) ^ (q - p)
  have hAfin : A ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (sub_nonneg.mpr hpq) ENNReal.ofReal_ne_top
  let S := ⨆ r : Ioi (0 : ℝ), besovEnergy m p (p * α) univ u r
  have hS : S ≠ ∞ := hu.2.ne
  refine lt_of_le_of_lt (iSup_le fun r ↦ ?_) (ENNReal.mul_ne_top hAfin hS).lt_top
  have hincr (x y : X) (_ : dist y x < (r : ℝ)) :
      |(Real.arctan ∘ u) x - (Real.arctan ∘ u) y| ≤ Real.pi := by
    have h (z : X) : |Real.arctan (u z)| ≤ Real.pi / 2 :=
      abs_le.mpr ⟨(Real.neg_pi_div_two_lt_arctan _).le, (Real.arctan_lt_pi_div_two _).le⟩
    simpa only [comp_apply] using (abs_sub (Real.arctan (u x)) (Real.arctan (u y))).trans
      (by linarith only [h x, h y] : |Real.arctan (u x)| + |Real.arctan (u y)| ≤ Real.pi)
  have h := besovEnergy_le_of_increment_bound (m := m) (βp := p * α) (βq := p * α)
    hp.le hpq r.property univ hincr
  rw [sub_self, ENNReal.rpow_zero, one_mul] at h
  calc
    _ ≤ A * besovEnergy m p (p * α) univ (Real.arctan ∘ u) r := h
    _ ≤ A * besovEnergy m p (p * α) univ u r :=
      mul_le_mul_of_nonneg_left (besovEnergy_lipschitz_comp_le hp.le lipschitzWith_arctan u r) bot_le
    _ ≤ A * S := mul_le_mul_of_nonneg_left (le_iSup (fun s : Ioi (0 : ℝ) ↦
      besovEnergy m p (p * α) univ u s) r) bot_le

/-- The scale `p * αₚ` is nondecreasing, including when an exponent
takes the value infinity. -/
theorem criticalBesovExponent_mul_mono {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    ENNReal.ofReal p * criticalBesovExponent m p ≤
      ENNReal.ofReal q * criticalBesovExponent m q := by
  classical
  have hq : 0 < q := hp.trans_le hpq
  unfold criticalBesovExponent at *
  simp only [ENNReal.mul_iSup]
  refine iSup_le fun α ↦ iSup_le fun ⟨u, hu, hnonconst⟩ ↦ ?_
  let v := Real.arctan ∘ u
  have hv : InBesov m q (p * (α : ℝ) / q) v := inBesov_arctan_comp hp hpq hu
  have hvnc : ¬ ∃ c : ℝ, v =ᵐ[m] fun _ ↦ c := by
    rintro ⟨c, hc⟩
    have hm : m ≠ 0 := by
      intro hzero
      apply hnonconst
      exact ⟨0, by simp [hzero, Filter.EventuallyEq]⟩
    have : NeZero m := ⟨hm⟩
    obtain ⟨x, hx⟩ := hc.exists
    apply hnonconst
    refine ⟨u x, ?_⟩
    filter_upwards [hc] with y hy
    exact Real.arctan_injective (hy.trans hx.symm)
  have hα : 0 < p * (α : ℝ) / q := div_pos (mul_pos hp α.property) hq
  have h := le_criticalBesovExponent hα hv hvnc
  have hmul : ENNReal.ofReal p * ENNReal.ofReal (α : ℝ) =
      ENNReal.ofReal q * ENNReal.ofReal (p * (α : ℝ) / q) := by
    rw [← ENNReal.ofReal_mul hp.le, ← ENNReal.ofReal_mul hq.le]
    congr 1
    field_simp
  rw [hmul]
  have h' := mul_le_mul_of_nonneg_left h (bot_le : (0 : ℝ≥0∞) ≤ ENNReal.ofReal q)
  simpa only [criticalBesovExponent, ENNReal.mul_iSup] using h'

end WalkDimensions
