import WalkDimensions.Interpolation
import WalkDimensions.LargeScale

/-!
# Besov membership of a Hölder test function

The interpolation step in Lemma 5.2 of arXiv:2611.02422v1, including
control of all positive radii.
-/

open MeasureTheory Set
open scoped ENNReal

namespace WalkDimensions

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X}

omit [BorelSpace X] in
/-- Lowering the scaling exponent at radii at most one decreases the energy. -/
theorem besovEnergy_le_of_le_scale {p β₁ β₂ r : ℝ} (hβ : β₁ ≤ β₂) (hr : r ≤ 1)
    (U : Set X) (u : X → ℝ) :
    besovEnergy m p β₁ U u r ≤ besovEnergy m p β₂ U u r :=
  mul_le_mul_of_nonneg_right
    (ENNReal.rpow_le_rpow_of_exponent_ge
      (by simpa using ENNReal.ofReal_le_ofReal hr) (neg_le_neg hβ)) bot_le

variable [SFinite m] [SecondCountableTopology X] [ProperSpace X]
  [IsFiniteMeasureOnCompacts m] [m.IsOpenPosMeasure]

/-- A Hölder function with bounded (p)-Besov energy belongs to the
(q)-Besov space at every positive exponent up to the interpolation
endpoint, provided it is (q)-integrable. -/
theorem inBesov_of_holder {d p q α β c K : ℝ} (hvol : AhlforsRegular m d)
    (hp : 0 < p) (hpq : p ≤ q) (hα : 0 < α) (hc : 0 ≤ c) (hK : 0 ≤ K)
    (hscale : q * α ≤ β + (q - p) * c) {u : X → ℝ} (hu : Measurable u)
    (huq : MemLp u (ENNReal.ofReal q) m) {M : ℝ≥0∞} (hM : M ≠ ∞)
    (hbound : ∀ r ∈ Ioc (0 : ℝ) 1, besovEnergy m p β univ u r ≤ M)
    (hholder : ∀ x y, |u x - u y| ≤ K * dist x y ^ c) :
    InBesov m q α u := by
  obtain ⟨_, C, hC, hvol⟩ := hvol
  have hq : 0 < q := hp.trans_le hpq
  let F := (ENNReal.ofReal K) ^ (q - p) * M
  let G := (2 : ℝ≥0∞) ^ q * (1 + ENNReal.ofReal (C * C)) *
    ∫⁻ x, ENNReal.ofReal |u x| ^ q ∂m
  have hF : F ≠ ∞ := ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (sub_nonneg.mpr hpq) ENNReal.ofReal_ne_top) hM
  have hmoment : (∫⁻ x, ENNReal.ofReal |u x| ^ q ∂m) < ∞ := by
    simpa only [← ofReal_norm, Real.norm_eq_abs, ENNReal.toReal_ofReal hq.le] using
      (lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top
        (ENNReal.ofReal_ne_zero_iff.2 hq) ENNReal.ofReal_ne_top huq.eLpNorm_lt_top)
  have hG : G ≠ ∞ := ENNReal.mul_ne_top (ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg hq.le (by norm_num))
    (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.ofReal_ne_top⟩)) hmoment.ne
  refine ⟨huq, lt_of_le_of_lt (iSup_le fun r ↦ ?_) (lt_top_iff_ne_top.mpr (ENNReal.add_ne_top.2 ⟨hF, hG⟩))⟩
  have hr : 0 < (r : ℝ) := r.property
  by_cases hsmall : (r : ℝ) ≤ 1
  · apply le_trans _ (le_add_of_nonneg_right (bot_le : 0 ≤ G))
    exact (besovEnergy_le_of_le_scale (m := m) hscale hsmall univ u).trans
      ((besovEnergy_le_of_holder hp.le hpq hc hK hr univ hholder).trans
        (mul_le_mul_of_nonneg_left (hbound r ⟨hr, hsmall⟩) bot_le))
  · apply le_trans _ (le_add_of_nonneg_left (bot_le : 0 ≤ F))
    have hlarge : 1 < (ENNReal.ofReal (r : ℝ)) := by
      simpa using ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < (r : ℝ)) |>.2
        (lt_of_not_ge hsmall)
    have hneg : -(q * α) < 0 := neg_neg_of_pos (mul_pos hq hα)
    have hdrop : besovEnergy m q (q * α) univ u r ≤ besovEnergy m q 0 univ u r := by
      simp only [besovEnergy, neg_zero, ENNReal.rpow_zero, one_mul]
      exact mul_le_of_le_one_left' (ENNReal.rpow_le_one_of_one_le_of_neg hlarge.le hneg)
    exact hdrop.trans (besovEnergy_zero_scale_le hC hq.le hr (fun x ↦ hvol x r hr) hu)

/-- The positive-(γ_p) comparison in Section 5 once a Hölder test function
and the critical exponent identity are available. -/
theorem gamma_le_gamma_of_holder_test {d p q K : ℝ} {β : ℝ → ℝ}
    (hvol : AhlforsRegular m d) (hp : 1 < p) (hpq : p ≤ q) (hβp : d < β p)
    (hβq : 0 ≤ β q) (hK : 0 ≤ K)
    (hcritical : criticalBesovExponent m q = ENNReal.ofReal (β q / q))
    {u : X → ℝ} (hu : Measurable u) (huq : MemLp u (ENNReal.ofReal q) m)
    (hnonconst : ¬ ∃ a : ℝ, u =ᵐ[m] fun _ ↦ a) {M : ℝ≥0∞} (hM : M ≠ ∞)
    (hbound : ∀ r ∈ Ioc (0 : ℝ) 1, besovEnergy m p (β p) univ u r ≤ M)
    (hholder : ∀ x y, |u x - u y| ≤ K * dist x y ^ gamma d β p) :
    gamma d β p ≤ gamma d β q := by
  have hq : 1 < q := hp.trans_le hpq
  have hq₀ := zero_lt_one.trans hq
  have hγp : 0 < gamma d β p := div_pos (sub_pos.mpr hβp) (sub_pos.mpr hp)
  let α := ((q - 1) * gamma d β p + d) / q
  have hα : 0 < α := div_pos (add_pos (mul_pos (sub_pos.mpr hq) hγp) hvol.1) hq₀
  have hscale : q * α = β p + (q - p) * gamma d β p := by
    rw [show q * α = (q - 1) * gamma d β p + d by
      dsimp only [α]
      rw [mul_comm, div_mul_cancel₀ _ hq₀.ne'], gamma_interpolation_exponent hp]
  have hm := inBesov_of_holder hvol (zero_lt_one.trans hp) hpq hα hγp.le hK
    hscale.le hu huq hM hbound hholder
  have h := le_criticalBesovExponent hα hm hnonconst
  rw [hcritical, ENNReal.ofReal_le_ofReal_iff (div_nonneg hβq hq₀.le)] at h
  apply (gamma_le_gamma_iff hq).2
  exact (div_le_div_iff_of_pos_right hq₀).1 h

end WalkDimensions
