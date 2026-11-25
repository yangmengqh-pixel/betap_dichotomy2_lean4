import WalkDimensions.BallIntegration
import WalkDimensions.BesovExponentMonotonicity
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Antitonicity of the critical Besov exponent

Truncating away a neighbourhood of zero gives a test on a set of finite
measure. Doubling controls the increments with only one endpoint in that set.
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal Topology

namespace WalkDimensions

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] {m : Measure X} [SFinite m]
  [ProperSpace X] [IsFiniteMeasureOnCompacts m] [m.IsOpenPosMeasure]

theorem besovEnergy_univ_le_of_support_subset {D : ℝ≥0∞}
    (hDfin : D ≠ ∞) (hD : ∀ (x : X) (r : ℝ), 0 < r → m (ball x (2 * r)) ≤ D * m (ball x r))
    {p β r : ℝ} (hp : 0 < p) (hr : 0 < r) {u : X → ℝ} (hu : Measurable u)
    {S : Set X} (hS : MeasurableSet S) (hsupp : support u ⊆ S) :
    besovEnergy m p β univ u r ≤ (1 + D) * besovEnergy m p β S u r := by
  let F : X × X → ℝ≥0∞ := fun z ↦
    (m (ball z.1 r))⁻¹ * ENNReal.ofReal |u z.1 - u z.2| ^ p
  have hF : Measurable F := ((measurable_measure_ball m r).inv.comp measurable_fst).mul
    ((continuous_abs.measurable.comp ((hu.comp measurable_fst).sub
      (hu.comp measurable_snd))).ennreal_ofReal.pow_const _)
  have hmoment (x : X) : ballMoment m p u r x = ∫⁻ y in ball x r, F (x, y) ∂m := by
    rw [ballMoment, normalizedBall, lintegral_smul_measure, smul_eq_mul,
      lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr (measure_ball_pos m x hr).ne')]
  have hswap :
      (∫⁻ x in Sᶜ, ballMoment m p u r x ∂m) ≤ D * ∫⁻ y in S, ballMoment m p u r y ∂m := by
    calc
      _ = ∫⁻ x in Sᶜ, (∫⁻ y in ball x r, S.indicator (fun y ↦ F (x, y)) y ∂m) ∂m := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem hS.compl (μ := m)] with x hx
        rw [hmoment]
        apply lintegral_congr
        intro y
        by_cases hy : y ∈ S
        · rw [indicator_of_mem hy]
        · rw [indicator_of_notMem hy]
          have hux := notMem_support.mp (fun h ↦ hx (hsupp h))
          have huy := notMem_support.mp (fun h ↦ hy (hsupp h))
          simp [F, hux, huy, hp]
      _ ≤ ∫⁻ x, (∫⁻ y in ball x r, S.indicator (fun y ↦ F (x, y)) y ∂m) ∂m :=
        lintegral_mono' Measure.restrict_le_self le_rfl
      _ = ∫⁻ y in S, (∫⁻ x in ball y r, F (x, y) ∂m) ∂m := by
        let G : X × X → ℝ≥0∞ := {z | z.2 ∈ S}.indicator F
        have hG : Measurable G := hF.indicator (measurable_snd hS)
        have hG' (x y : X) : S.indicator (fun z ↦ F (x, z)) y = G (x, y) := by
          by_cases hy : y ∈ S <;> simp [G, hy]
        simp only [hG']
        rw [lintegral_lintegral_ball_swap r hG, ← lintegral_indicator hS]
        apply lintegral_congr
        intro y
        by_cases hy : y ∈ S
        · simp [G, hy]
        · simp [G, hy]
      _ ≤ ∫⁻ y in S, D * ballMoment m p u r y ∂m := by
        apply lintegral_mono
        intro y
        dsimp only
        rw [hmoment, ← lintegral_const_mul' _ _]
        · apply setLIntegral_mono' measurableSet_ball
          intro x hx
          have hvol : m (ball y r) ≤ D * m (ball x r) := by
            have hcompare := measure_ball_le_of_dist_le hD hr 1 (x := x) (y := y)
              (t := r) (by rw [pow_one, dist_comm y x]; linarith only [mem_ball.mp hx])
            simpa only [pow_one] using hcompare
          have hinv := inv_measure_le_mul_inv_of_le (measure_ball_pos m x hr).ne'
            (measure_ball_pos m y hr).ne' measure_ball_ne_top measure_ball_ne_top hvol
          dsimp only [F]
          rw [abs_sub_comm (u x) (u y), ← mul_assoc]
          exact mul_le_mul_of_nonneg_right hinv bot_le
        · exact hDfin
      _ = _ := lintegral_const_mul' _ _ hDfin
  unfold besovEnergy
  rw [Measure.restrict_univ, ← lintegral_add_compl _ hS,
    mul_left_comm (1 + D), add_mul, one_mul]
  exact mul_le_mul_of_nonneg_left (add_le_add_right hswap _) bot_le

def softThreshold (δ a : ℝ) : ℝ := min (a + δ) (max (a - δ) 0)

theorem lipschitzWith_softThreshold (δ : ℝ) : LipschitzWith 1 (softThreshold δ) := by
  have hadd (c : ℝ) : LipschitzWith 1 (fun a : ℝ ↦ a + c) := by
    apply lipschitzWith_iff_dist_le_mul.mpr
    intro a b
    simp [Real.dist_eq]
  have hsub : LipschitzWith 1 (fun a : ℝ ↦ a - δ) := by simpa only [sub_eq_add_neg] using hadd (-δ)
  unfold softThreshold
  simpa only [max_self] using (hadd δ).min (hsub.max_const 0)

theorem softThreshold_zero_of_abs_lt {δ a : ℝ} (ha : |a| < δ) :
    softThreshold δ a = 0 := by
  have h := abs_lt.mp ha
  rw [softThreshold, max_eq_right (by linarith : a - δ ≤ 0),
    min_eq_right (by linarith : 0 ≤ a + δ)]

omit [MetricSpace X] [BorelSpace X] [SecondCountableTopology X] [SFinite m]
  [ProperSpace X] [IsFiniteMeasureOnCompacts m] [m.IsOpenPosMeasure] in
theorem exists_softThreshold_nonconstant {u : X → ℝ}
    (hu : ¬ ∃ c : ℝ, u =ᵐ[m] fun _ ↦ c) :
    ∃ δ > (0 : ℝ), ¬ ∃ c : ℝ, (softThreshold δ ∘ u) =ᵐ[m] fun _ ↦ c := by
  by_contra! h
  let δ : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have hδ (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  choose c hc using fun n ↦ h (δ n) (hδ n)
  have hAE : ∀ᵐ x ∂m, ∀ n, softThreshold (δ n) (u x) = c n :=
    eventually_countable_forall.mpr hc
  have hm : m ≠ 0 := by
    intro hm
    apply hu
    exact ⟨0, by simp [hm, Filter.EventuallyEq]⟩
  have : NeZero m := ⟨hm⟩
  obtain ⟨y, hy⟩ := hAE.exists
  have hlim (a : ℝ) : Tendsto (fun n ↦ softThreshold (δ n) a) atTop (𝓝 a) := by
    have hcont : Continuous (fun d : ℝ ↦ softThreshold d a) := by
      unfold softThreshold
      fun_prop
    have hzero : softThreshold 0 a = a := by simp [softThreshold]
    simpa only [Function.comp_def, hzero, δ] using
      (hcont.tendsto 0).comp (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  apply hu
  refine ⟨u y, hAE.mono fun x hx ↦ ?_⟩
  have heq : (fun n ↦ softThreshold (δ n) (u x)) = fun n ↦ softThreshold (δ n) (u y) :=
    funext fun n ↦ (hx n).trans (hy n).symm
  exact tendsto_nhds_unique (hlim (u x)) (heq.symm ▸ hlim (u y))

private theorem inBesov_softThreshold {p q α δ : ℝ} (hvol : VolumeDoubling m)
    (hp : 0 < p) (hpq : p < q) (hδ : 0 < δ)
    {u : X → ℝ} (hu : Measurable u) (huq : InBesov m q α u) :
    InBesov m p α (softThreshold δ ∘ u) := by
  obtain ⟨D, _, hD⟩ := hvol
  let v := softThreshold δ ∘ u
  let S : Set X := {x | δ ≤ |u x|}
  have hS : MeasurableSet S := measurableSet_le measurable_const (continuous_abs.measurable.comp hu)
  have hzero (x : X) (hx : x ∉ S) : v x = 0 :=
    softThreshold_zero_of_abs_lt (lt_of_not_ge hx)
  have hsupp : support v ⊆ S := support_subset_iff'.mpr hzero
  have hv : Measurable v := (lipschitzWith_softThreshold δ).continuous.measurable.comp hu
  have hq : 0 < q := hp.trans hpq
  let F : X → ℝ≥0∞ := fun x ↦ ENNReal.ofReal |u x| ^ q
  let k := ENNReal.ofReal δ ^ q
  have hk : k ≠ 0 := (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hδ)
    ENNReal.ofReal_ne_top).ne'
  have hF : Measurable F := ((continuous_abs.measurable.comp hu).ennreal_ofReal).pow_const _
  have hFfin : (∫⁻ x, F x ∂m) < ∞ := by
    simpa only [F, ENNReal.toReal_ofReal hq.le, Real.eNorm_eq_ofReal_abs] using
      lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top (ENNReal.ofReal_ne_zero_iff.mpr hq)
        ENNReal.ofReal_ne_top huq.1.eLpNorm_lt_top
  have hmS : m S ≠ ∞ := by
    intro hm
    have h := mul_meas_ge_le_lintegral hF (μ := m) k
    have hle : k * m S ≤ ∫⁻ x, F x ∂m := by
      refine (mul_le_mul_of_nonneg_left (measure_mono ?_) bot_le).trans h
      intro x hx
      exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hx) hq.le
    exact hFfin.not_ge (by simpa [hm, hk] using hle)
  have hvq : MemLp v (ENNReal.ofReal q) m := huq.1.of_le hv.aestronglyMeasurable (ae_of_all _ fun x ↦ by
    have h := lipschitzWith_iff_dist_le_mul.mp (lipschitzWith_softThreshold δ) (u x) 0
    have hz : softThreshold δ 0 = 0 := softThreshold_zero_of_abs_lt (by simpa using hδ)
    simpa only [v, Function.comp_apply, hz, Real.dist_eq, sub_zero, NNReal.coe_one, one_mul, Real.norm_eq_abs] using h)
  let M := ⨆ r : Ioi (0 : ℝ), besovEnergy m q (q * α) univ u r
  have hθ : 0 ≤ p / q := (div_pos hp hq).le
  have hθ' : 0 ≤ 1 - p / q := sub_nonneg.mpr ((div_le_iff₀ hq).mpr (by simpa using hpq.le))
  let K := (1 + ENNReal.ofReal D) * (M ^ (p / q) * m S ^ (1 - p / q))
  have hK : K ≠ ∞ := ENNReal.mul_ne_top (by finiteness)
    (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hθ huq.2.ne)
      (ENNReal.rpow_ne_top_of_nonneg hθ' hmS))
  refine ⟨hvq.mono_exponent_of_measure_support_ne_top hzero hmS (ENNReal.ofReal_le_ofReal hpq.le),
    (iSup_le fun r ↦ ?_).trans_lt hK.lt_top⟩
  have hratio : p * α / p = q * α / q := by field_simp
  have hlocal :
      besovEnergy m q (q * α) S v r ≤ M := by
    calc
      _ ≤ besovEnergy m q (q * α) univ v r := by
        unfold besovEnergy
        exact mul_le_mul_of_nonneg_left (lintegral_mono_set (subset_univ _)) bot_le
      _ ≤ besovEnergy m q (q * α) univ u r :=
        besovEnergy_lipschitz_comp_le hq.le (lipschitzWith_softThreshold δ) u r
      _ ≤ M := le_iSup (fun s : Ioi (0 : ℝ) ↦ besovEnergy m q (q * α) univ u s) r
  calc
    _ ≤ (1 + ENNReal.ofReal D) * besovEnergy m p (p * α) S v r :=
      besovEnergy_univ_le_of_support_subset ENNReal.ofReal_ne_top hD hp r.property hv hS hsupp
    _ ≤ _ := mul_le_mul_of_nonneg_left ((besovEnergy_le_of_equal_ratio hp hpq r.property hratio hv S).trans
      (mul_le_mul_of_nonneg_right (ENNReal.rpow_le_rpow hlocal hθ) bot_le)) bot_le

/-- The normalized critical exponent is nonincreasing in the integrability
exponent on a doubling metric measure space. This is Lemma 3.1(iii). -/
theorem criticalBesovExponent_antitone (hvol : VolumeDoubling m) {p q : ℝ}
    (hp : 0 < p) (hpq : p ≤ q) :
    criticalBesovExponent m q ≤ criticalBesovExponent m p := by
  rcases lt_or_eq_of_le hpq with hpq | rfl
  · refine iSup_le fun α ↦ iSup_le fun ⟨u, hu, hconst⟩ ↦ ?_
    let v := hu.1.aestronglyMeasurable.aemeasurable.mk u
    have hmeas : Measurable v := hu.1.aestronglyMeasurable.aemeasurable.measurable_mk
    have huv : u =ᵐ[m] v := hu.1.aestronglyMeasurable.aemeasurable.ae_eq_mk
    have hv : InBesov m q α v := ⟨hu.1.ae_eq huv, by
      simpa only [← besovEnergy_congr_ae huv] using hu.2⟩
    have hvnc : ¬ ∃ c : ℝ, v =ᵐ[m] fun _ ↦ c := by
      rintro ⟨c, hc⟩
      exact hconst ⟨c, huv.trans hc⟩
    obtain ⟨δ, hδ, hw⟩ := exists_softThreshold_nonconstant hvnc
    exact le_criticalBesovExponent α.property (inBesov_softThreshold hvol hp hpq hδ hmeas hv) hw
  · exact le_rfl

end WalkDimensions
