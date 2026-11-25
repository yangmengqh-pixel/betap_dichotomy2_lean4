import WalkDimensions.EnergyMeasureConstruction
import WalkDimensions.BesovStability

/-!
# Control of the graph norm on functions vanishing on a set of positive mass
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {m : Measure X} [IsFiniteMeasureOnCompacts m] [m.IsOpenPosMeasure]
  {p : ℝ} (E : PEnergy m p)

theorem exists_graphNorm_le_root_of_zero_off_ball_and_on {β : ℝ}
    (hPI : E.Poincare E.energyMeasure β) (x : X) {r : ℝ} (hr : 0 < r)
    {V : Set X} (hV : MeasurableSet V) (hVB : V ⊆ ball x r) (hVm : 0 < m V) :
    ∃ K : ℝ, 0 < K ∧ ∀ f : E.domain,
      (f : RealLp m p) =ᵐ[m.restrict (ball x r)ᶜ] (fun _ ↦ 0) →
      (f : RealLp m p) =ᵐ[m.restrict V] (fun _ ↦ 0) →
      E.graphSeminorm f ≤ K * E.rootSeminorm f := by
  obtain ⟨C, A, hC, _, hPI⟩ := hPI
  let B := ball x r
  let D := (2 : ℝ≥0∞) ^ p * (1 + (m V)⁻¹ * m B) * ENNReal.ofReal (C * r ^ β)
  have hp := zero_lt_one.trans E.one_lt
  have hVT : m V ≠ ∞ := measure_ne_top_of_subset hVB measure_ball_ne_top
  have hDT : D ≠ ∞ := by
    apply ENNReal.mul_ne_top _ ENNReal.ofReal_ne_top
    apply ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hp.le (by norm_num))
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top,
      ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hVm.ne') measure_ball_ne_top⟩
  refine ⟨1 + D.toReal ^ p⁻¹, by positivity, ?_⟩
  intro f hOff hZero
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt.le⟩
  let u : X → ℝ := (f : RealLp m p)
  let a := ⨍ y in B, u y ∂m
  let F (y : X) := ENNReal.ofReal |u y - a| ^ p
  let H (y : X) := ENNReal.ofReal |u y| ^ p
  let b := ENNReal.ofReal |a| ^ p
  let I := ∫⁻ y in B, F y ∂m
  have hI : I ≤ ENNReal.ofReal (C * r ^ β) * (E.energy f : ℝ≥0∞) := by
    have hh := hPI x r hr f
    change I ≤ _ at hh
    exact hh.trans (mul_le_mul_of_nonneg_left
      ((measure_mono (subset_univ _)).trans_eq (E.energyMeasure_univ f)) bot_le)
  have hb : b * m V ≤ I := by
    have he : (∫⁻ y in V, F y ∂m) = b * m V := by
      rw [← setLIntegral_const]
      apply lintegral_congr_ae
      filter_upwards [hZero] with y hy
      change u y = 0 at hy
      simp only [F, hy, zero_sub, abs_neg, b]
    rw [← he]
    exact lintegral_mono_set hVB
  have hb' : b ≤ (m V)⁻¹ * I := by
    have h := mul_le_mul_of_nonneg_left hb (show 0 ≤ (m V)⁻¹ from bot_le)
    rw [mul_left_comm, ENNReal.inv_mul_cancel hVm.ne' hVT, mul_one] at h
    exact h
  have hF : AEMeasurable F (m.restrict B) := by
    have hu : AEMeasurable u m := (Lp.aestronglyMeasurable _).aemeasurable
    exact ((continuous_abs.measurable.comp_aemeasurable (hu.restrict.sub aemeasurable_const)).ennreal_ofReal).pow_const _
  have hOff0 : (∫⁻ y in Bᶜ, H y ∂m) = 0 := by
    rw [← lintegral_zero (μ := m.restrict Bᶜ)]
    apply lintegral_congr_ae
    filter_upwards [hOff] with y hy
    change u y = 0 at hy
    simp only [H, hy, abs_zero, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos hp]
  have hMoment : (∫⁻ y, H y ∂m) ≤ D * (E.energy f : ℝ≥0∞) := by
    rw [← lintegral_add_compl _ measurableSet_ball, hOff0, add_zero]
    have hP : (2 : ℝ≥0∞) ^ p ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hp.le (by norm_num)
    calc
      _ ≤ ∫⁻ y in B, (2 : ℝ≥0∞) ^ p * (F y + b) ∂m := by
        apply lintegral_mono
        intro y
        have h := ennreal_abs_sub_rpow_le (u y - a) (-a) hp.le
        simpa only [sub_neg_eq_add, sub_add_cancel, abs_neg, F, H, b] using h
      _ = (2 : ℝ≥0∞) ^ p * (I + b * m B) := by
        rw [lintegral_const_mul' _ _ hP, lintegral_add_left' hF, setLIntegral_const]
      _ ≤ (2 : ℝ≥0∞) ^ p * (I + ((m V)⁻¹ * I) * m B) :=
        mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_right hb' bot_le) _) bot_le
      _ = ((2 : ℝ≥0∞) ^ p * (1 + (m V)⁻¹ * m B)) * I := by
        rw [mul_assoc ((2 : ℝ≥0∞) ^ p), add_mul, one_mul]
        congr 2
        ac_rfl
      _ ≤ _ := by
        dsimp only [D]
        rw [mul_assoc ((2 : ℝ≥0∞) ^ p * (1 + (m V)⁻¹ * m B))]
        exact mul_le_mul_of_nonneg_left hI bot_le
  have hNorm : ‖(f : RealLp m p)‖ ≤ D.toReal ^ p⁻¹ * E.rootSeminorm f := by
    have hExp := eLpNorm_rpow_eq_lintegral_abs hp (Lp.aestronglyMeasurable (f : RealLp m p))
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top hDT ENNReal.coe_ne_top) (hExp.symm ▸ hMoment)
    rw [← ENNReal.toReal_rpow, ← Lp.norm_def, ENNReal.toReal_mul, ENNReal.coe_toReal] at h
    have h' := Real.rpow_le_rpow (Real.rpow_nonneg (norm_nonneg (f : RealLp m p)) p) h (inv_nonneg.mpr hp.le)
    rw [← Real.rpow_mul (norm_nonneg _), mul_inv_cancel₀ hp.ne', Real.rpow_one,
      Real.mul_rpow ENNReal.toReal_nonneg (NNReal.coe_nonneg _), ← E.rootSeminorm_apply] at h'
    exact h'
  exact (E.graphSeminorm_le_add f).trans
    ((add_le_add_right hNorm _).trans_eq (by ring))

end WalkDimensions.PEnergy
