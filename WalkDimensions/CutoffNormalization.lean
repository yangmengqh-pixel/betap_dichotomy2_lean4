import WalkDimensions.EnergyClarkson

/-!
# Normalizing cutoffs

The Markov and algebra properties give the domain and energy estimates
for the normalization used in a controlled partition of unity.
-/

open MeasureTheory
open scoped ENNReal

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {m : Measure X} [IsFiniteMeasureOnCompacts m] {p : ℝ} (E : PEnergy m p)

private theorem lipschitzWith_inv_max_one_sub_one :
    LipschitzWith 1 (fun x : ℝ ↦ (max x 1)⁻¹ - 1) := by
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro x y
  let a := max x 1
  let b := max y 1
  have ha : 1 ≤ a := le_max_right _ _
  have hb : 1 ≤ b := le_max_right _ _
  have ha₀ : 0 < a := zero_lt_one.trans_le ha
  have hb₀ : 0 < b := zero_lt_one.trans_le hb
  have he : a⁻¹ - b⁻¹ = (b - a) / (a * b) := by
    field_simp
  have hab : |a⁻¹ - b⁻¹| ≤ |a - b| := by
    rw [he, abs_div, abs_of_pos (mul_pos ha₀ hb₀), abs_sub_comm b a]
    exact div_le_self (abs_nonneg _) (one_le_mul_of_one_le_of_one_le ha hb)
  have hmax := (lipschitzWith_iff_dist_le_mul.mp (LipschitzWith.id.max_const (1 : ℝ))) x y
  simp only [Real.dist_eq, id_eq, NNReal.coe_one, one_mul] at hmax ⊢
  rw [sub_sub_sub_cancel_right]
  exact hab.trans hmax

/-- Divide a bounded cutoff by a denominator clamped below at one.
In a partition of unity the denominator is the sum of the cutoffs
meeting the support of the numerator. -/
theorem exists_div_max_one (f g : E.domain) (hbounded : eLpNorm (f : RealLp m p) ∞ m ≤ 1) :
    ∃ h : E.domain,
      ((h : RealLp m p) =ᵐ[m] fun x ↦ (f : RealLp m p) x / max ((g : RealLp m p) x) 1) ∧
      E.rootSeminorm h ≤ 2 * E.rootSeminorm f + E.rootSeminorm g := by
  let φ : ℝ → ℝ := fun x ↦ (max x 1)⁻¹ - 1
  have hφ₀ : φ 0 = 0 := by norm_num [φ]
  obtain ⟨v, hv, hEv⟩ := E.markov φ lipschitzWith_inv_max_one_sub_one hφ₀ g
  have hvbound : eLpNorm (v : RealLp m p) ∞ m ≤ 1 := by
    rw [eLpNorm_exponent_top (Lp.aestronglyMeasurable (v : RealLp m p))]
    apply eLpNormEssSup_le_of_ae_eNorm_bound
    filter_upwards [hv] with x hx
    change ‖(v : RealLp m p) x‖ₑ ≤ _
    rw [hx, Real.eNorm_eq_ofReal_abs, ← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    have hmax : (1 : ℝ) ≤ max ((g : RealLp m p) x) 1 := le_max_right _ _
    have h₁ : (max ((g : RealLp m p) x) 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hmax
    have h₀ : 0 ≤ (max ((g : RealLp m p) x) 1)⁻¹ :=
      inv_nonneg.mpr (zero_le_one.trans hmax)
    exact abs_le.mpr ⟨by dsimp [φ]; linarith only [h₀], by dsimp [φ]; linarith only [h₁]⟩
  obtain ⟨w, hw, hEw⟩ := E.algebra f v
    (hbounded.trans_lt ENNReal.one_lt_top) (hvbound.trans_lt ENNReal.one_lt_top)
  have hfnorm : (eLpNorm (f : RealLp m p) ∞ m).toReal ≤ 1 := by
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top hbounded
  have hvnorm : (eLpNorm (v : RealLp m p) ∞ m).toReal ≤ 1 := by
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top hvbound
  have hvroot : E.rootSeminorm v ≤ E.rootSeminorm g := by
    rw [E.rootSeminorm_apply, E.rootSeminorm_apply]
    exact Real.rpow_le_rpow (NNReal.coe_nonneg _) hEv (inv_nonneg.mpr (zero_lt_one.trans E.one_lt).le)
  refine ⟨f + w, ?_, ?_⟩
  · have hadd := Lp.coeFn_add (f : RealLp m p) (w : RealLp m p)
    filter_upwards [hadd, hw, hv] with x hx hxw hxv
    change ((f : RealLp m p) + (w : RealLp m p)) x =
      (f : RealLp m p) x / max ((g : RealLp m p) x) 1
    rw [hx, Pi.add_apply, hxw, hxv, div_eq_mul_inv]
    dsimp [φ]
    ring
  · have hw' : E.rootSeminorm w ≤ E.rootSeminorm g + E.rootSeminorm f := by
      apply hEw.trans (add_le_add ?_ ?_)
      · calc
          _ ≤ 1 * E.rootSeminorm v :=
            mul_le_mul_of_nonneg_right hfnorm (apply_nonneg _ _)
          _ ≤ _ := by rw [one_mul]; exact hvroot
      · simpa only [one_mul] using mul_le_mul_of_nonneg_right hvnorm (apply_nonneg E.rootSeminorm f)
    calc
      _ ≤ E.rootSeminorm f + E.rootSeminorm w := E.rootSeminorm.add_le' f w
      _ ≤ _ := by linarith only [hw']

end WalkDimensions.PEnergy
