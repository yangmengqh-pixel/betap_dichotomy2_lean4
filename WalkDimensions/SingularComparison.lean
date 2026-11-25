import WalkDimensions.Besov
import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Vanishing at matching normalized exponents

The measure-theoretic step in Section 4 of arXiv:2611.02422v1. The two
regions of integration are separated by a neighbourhood of a compact
set carrying almost all of the singular measure.
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal Topology

namespace WalkDimensions

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [BorelSpace X] in
theorem besovEnergy_union_le (m : Measure X) (p β : ℝ) (U V : Set X)
    (u : X → ℝ) (r : ℝ) :
    besovEnergy m p β (U ∪ V) u r ≤
      besovEnergy m p β U u r + besovEnergy m p β V u r := by
  unfold besovEnergy
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (lintegral_union_le _ _ _) bot_le

theorem besovEnergy_thickening_support {m : Measure X} {p β R r : ℝ}
    (hp : 0 < p) (hR : 0 < R) (hr : r ≤ R) (u : X → ℝ) :
    besovEnergy m p β (thickening R (tsupport u)) u r =
      besovEnergy m p β univ u r := by
  simp only [besovEnergy, Measure.restrict_univ]
  congr 1
  apply setLIntegral_eq_of_support_subset
  intro x hx
  by_contra hnot
  apply hx
  have hx₀ : u x = 0 :=
    notMem_support.mp (fun h ↦ hnot (self_subset_thickening hR _ (subset_closure h)))
  have hy₀ (y : X) (hy : y ∈ ball x r) : u y = 0 := by
    apply notMem_support.mp
    intro h
    have hdist : dist y x < r := hy
    exact hnot (mem_thickening_iff.mpr
      ⟨y, subset_closure h, (dist_comm x y ▸ hdist).trans_le hr⟩)
  rw [ballMoment, normalizedBall, lintegral_smul_measure]
  have hzero : (∫⁻ y in ball x r, ENNReal.ofReal |u x - u y| ^ p ∂m) = 0 := by
    calc
      _ = ∫⁻ _ in ball x r, (0 : ℝ≥0∞) ∂m := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem (μ := m) measurableSet_ball] with y hy
        simp [hx₀, hy₀ y hy, hp]
      _ = 0 := lintegral_zero
  simp [hzero]

/-- If the higher-power local energies are bounded by a finite singular
measure, the lower-power global energy at the same normalized exponent
tends to zero. The local bound is the analytic input in Lemma 3.3. -/
theorem tendsto_besovEnergy_zero_of_singular {m ν : Measure X}
    [ProperSpace X] [SecondCountableTopology X] [SFinite m]
    [IsFiniteMeasureOnCompacts m] [m.IsOpenPosMeasure] [m.OuterRegular]
    [IsFiniteMeasure ν] [ν.InnerRegularCompactLTTop]
    {p q βp βq A : ℝ} (hp : 0 < p) (hpq : p < q) (hA : 0 < A)
    (hβ : βp / p = βq / q) {u : X → ℝ} (hu : Measurable u) (hc : HasCompactSupport u)
    (hsing : m.MutuallySingular ν) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hdom : ∀ U : Set X, IsOpen U → ∀ r > (0 : ℝ),
      besovEnergy m q βq U u r ≤ C * ν (thickening (A * r) U)) :
    Tendsto (besovEnergy m p βp univ u) (𝓝[>] 0) (𝓝 0) := by
  let S := thickening 1 (tsupport u)
  have hS : IsOpen S := isOpen_thickening
  have hSfin : m S ≠ ∞ := measure_ne_top_of_subset (thickening_subset_cthickening 1 (tsupport u))
    (IsCompact.measure_lt_top (μ := m) (hc.isCompact.cthickening (r := 1))).ne
  let θ := p / q
  have hq : 0 < q := hp.trans hpq
  have hθ : 0 < θ := div_pos hp hq
  have hθ₁ : 0 < 1 - θ := sub_pos.mpr ((div_lt_iff₀ hq).2 (by simpa using hpq))
  let D := (C * ν univ) ^ θ
  let E := C ^ θ * m S ^ (1 - θ)
  have hD : D ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hθ.le
    (ENNReal.mul_ne_top hC (measure_ne_top ν univ))
  have hE : E ≠ ∞ := ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hθ.le hC)
    (ENNReal.rpow_ne_top_of_nonneg hθ₁.le hSfin)
  have hlim : Tendsto (fun ε : ℝ≥0∞ ↦ D * ε ^ (1 - θ) + E * ε ^ θ) (𝓝 0) (𝓝 0) := by
    simpa only [zero_add] using
      (ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hD hθ₁).add
        (ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hE hθ)
  refine tendsto_order.2 ⟨fun b hb ↦ (not_lt_of_ge (bot_le : (0 : ℝ≥0∞) ≤ b) hb).elim, fun b hb ↦ ?_⟩
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0∞), D * ε ^ (1 - θ) + E * ε ^ θ < b :=
    ((tendsto_order.1 hlim).2 b hb).filter_mono nhdsWithin_le_nhds
  obtain ⟨ε, hε, hbound⟩ := (eventually_mem_nhdsWithin.and hev).exists
  obtain ⟨N, hNm, hmN, hνN⟩ := hsing
  obtain ⟨K, hKN, hK, hνK⟩ :=
    hNm.exists_isCompact_sdiff_lt (measure_ne_top ν N) hε.ne'
  have hmK : m K = 0 := measure_mono_null hKN hmN
  have hνK' : ν Kᶜ < ε := by
    have hsd : ν (Kᶜ \ Nᶜ) = ν Kᶜ :=
      measure_sdiff_null' (measure_mono_null inter_subset_right hνN)
    rw [← hsd, show Kᶜ \ Nᶜ = N \ K by ext x; simp [and_comm]]
    exact hνK
  obtain ⟨G, hKG, hG, hmG⟩ := K.exists_isOpen_lt_of_lt ε (hmK ▸ hε)
  obtain ⟨δ, hδ, hδG⟩ := hK.exists_thickening_subset_open hG hKG
  let U := S ∩ thickening δ K
  let V := S ∩ (cthickening (δ / 2) K)ᶜ
  have hU : IsOpen U := hS.inter isOpen_thickening
  have hV : IsOpen V := hS.inter isClosed_cthickening.isOpen_compl
  have hUV : U ∪ V = S := by
    have hsub : cthickening (δ / 2) K ⊆ thickening δ K :=
      cthickening_subset_thickening' hδ (by linarith) K
    apply Subset.antisymm (union_subset inter_subset_left inter_subset_left)
    intro x hx
    by_cases hxK : x ∈ cthickening (δ / 2) K
    · exact Or.inl ⟨hx, hsub hxK⟩
    · exact Or.inr ⟨hx, hxK⟩
  have hmU : m U ≤ ε := (measure_mono (inter_subset_right.trans hδG)).trans hmG.le
  have hmV : m V ≤ m S := measure_mono inter_subset_left
  have hη : 0 < min 1 (δ / (2 * A)) := lt_min zero_lt_one (by positivity)
  filter_upwards [Ioo_mem_nhdsGT hη] with r hr
  have hr₁ : r ≤ 1 := hr.2.le.trans (min_le_left _ _)
  have hr₂ : A * r ≤ δ / 2 := by
    have h := (le_div_iff₀ (show 0 < 2 * A by positivity)).1
      (hr.2.le.trans (min_le_right _ _))
    linarith
  have hsep : thickening (A * r) V ⊆ Kᶜ := by
    intro x hx hxK
    obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.mp hx
    exact hy.2 (mem_cthickening_of_dist_le y x (δ / 2) K hxK ((dist_comm y x ▸ hxy).le.trans hr₂))
  have hcompare (T : Set X) (hT : IsOpen T) :
      besovEnergy m p βp T u r ≤ (C * ν (thickening (A * r) T)) ^ θ *
        m T ^ (1 - θ) :=
    (besovEnergy_le_of_equal_ratio hp hpq hr.1 hβ hu T).trans
      (mul_le_mul_of_nonneg_right (ENNReal.rpow_le_rpow (hdom T hT r hr.1) hθ.le) bot_le)
  have hU' := (hcompare U hU).trans (mul_le_mul
    (ENNReal.rpow_le_rpow (mul_le_mul_of_nonneg_left (measure_mono (subset_univ _)) bot_le) hθ.le)
    (ENNReal.rpow_le_rpow hmU hθ₁.le) bot_le bot_le)
  have hV' := (hcompare V hV).trans (mul_le_mul
    (ENNReal.rpow_le_rpow (mul_le_mul_of_nonneg_left
      ((measure_mono hsep).trans hνK'.le) bot_le) hθ.le)
    (ENNReal.rpow_le_rpow hmV hθ₁.le) bot_le bot_le)
  rw [ENNReal.mul_rpow_of_nonneg _ _ hθ.le, mul_right_comm] at hV'
  calc
    besovEnergy m p βp univ u r = besovEnergy m p βp (U ∪ V) u r := by
      rw [hUV, besovEnergy_thickening_support hp zero_lt_one hr₁]
    _ ≤ besovEnergy m p βp U u r + besovEnergy m p βp V u r :=
      besovEnergy_union_le m p βp U V u r
    _ ≤ D * ε ^ (1 - θ) + E * ε ^ θ := add_le_add hU' hV'
    _ < b := hbound

end WalkDimensions
