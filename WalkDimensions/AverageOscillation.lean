import WalkDimensions.PEnergy
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Mean oscillation estimates

Jensen's inequality bounds the distance from a set average to a constant
by the integrated oscillation on any larger set.
-/

open Filter MeasureTheory Set
open scoped ENNReal

namespace WalkDimensions

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

theorem convexOn_abs_rpow {p : ℝ} (hp : 1 ≤ p) :
    ConvexOn ℝ (univ : Set ℝ) (fun a ↦ |a| ^ p) := by
  have hp' : 0 < p := zero_lt_one.trans_le hp
  have hrange : abs '' (univ : Set ℝ) ⊆ Ici 0 := by
    rintro _ ⟨a, _, rfl⟩
    exact abs_nonneg a
  have hrangeConvex : Convex ℝ (abs '' (univ : Set ℝ)) := by
    rw [show abs '' (univ : Set ℝ) = Ici 0 from by
      apply Subset.antisymm hrange
      intro a ha
      exact ⟨a, mem_univ _, abs_of_nonneg ha⟩]
    exact convex_Ici _
  have habs : ConvexOn ℝ (univ : Set ℝ) abs := by
    simpa only [Real.norm_eq_abs] using
      (show ConvexOn ℝ (univ : Set ℝ) (fun x : ℝ ↦ ‖x‖) from convexOn_norm convex_univ)
  exact ((convexOn_rpow hp).subset hrange hrangeConvex).comp habs (by
    intro a ha b _ hab
    exact Real.rpow_le_rpow (hrange ha) hab hp'.le)

theorem ofReal_abs_setAverage_sub_rpow_le {p : ℝ} (hp : 1 ≤ p) {u : X → ℝ}
    {S T : Set X} (hST : S ⊆ T) (hSpos : m S ≠ 0) (hTfin : m T ≠ ∞)
    (hu : MemLp u (ENNReal.ofReal p) (m.restrict T)) (c : ℝ) :
    ENNReal.ofReal |(⨍ x in S, u x ∂m) - c| ^ p ≤
      (m S)⁻¹ * ∫⁻ x in T, ENNReal.ofReal |u x - c| ^ p ∂m := by
  have hSfin := measure_ne_top_of_subset hST hTfin
  let : IsFiniteMeasure (m.restrict S) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hSfin.lt_top⟩
  let v : X → ℝ := fun x ↦ u x - c
  have hp' : 0 < p := zero_lt_one.trans_le hp
  have hq : 1 ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr hp
  have hmem := hu.mono_measure (Measure.restrict_mono hST le_rfl)
  have hv : MemLp v (ENNReal.ofReal p) (m.restrict S) := hmem.sub (memLp_const c)
  have hvi : IntegrableOn v S m := hv.integrable hq
  have hpow : IntegrableOn (fun x ↦ |v x| ^ p) S m := by
    change Integrable (fun x ↦ |v x| ^ p) (m.restrict S)
    simpa only [ENNReal.toReal_ofReal hp'.le, Real.norm_eq_abs] using
      hv.integrable_norm_rpow (ENNReal.ofReal_ne_zero_iff.mpr hp') ENNReal.ofReal_ne_top
  have hconvex := convexOn_abs_rpow hp
  have hcont : Continuous (fun a : ℝ ↦ |a| ^ p) :=
    (Real.continuous_rpow_const hp'.le).comp continuous_abs
  have hj := hconvex.map_set_average_le hcont.continuousOn isClosed_univ hSpos hSfin
    (Eventually.of_forall fun x ↦ mem_univ (v x)) hvi hpow
  have havg : (⨍ x in S, v x ∂m) = (⨍ x in S, u x ∂m) - c := by
    unfold v
    rw [setAverage_fun_sub (hmem.integrable hq) (integrableOn_const hSfin), setAverage_const hSpos hSfin]
  rw [havg] at hj
  have hIntegral :
      ENNReal.ofReal (∫ x in S, |v x| ^ p ∂m) = ∫⁻ x in S, ENNReal.ofReal |v x| ^ p ∂m := by
    rw [ofReal_integral_eq_lintegral_ofReal hpow
      (Eventually.of_forall fun x ↦ Real.rpow_nonneg (abs_nonneg (v x)) _)]
    simp_rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg (v _)) hp'.le]
  calc
    _ = ENNReal.ofReal (|(⨍ x in S, u x ∂m) - c| ^ p) :=
      ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp'.le
    _ ≤ ENNReal.ofReal (⨍ x in S, |v x| ^ p ∂m) := ENNReal.ofReal_le_ofReal hj
    _ = (m S)⁻¹ * ∫⁻ x in S, ENNReal.ofReal |v x| ^ p ∂m := by
      rw [setAverage_eq, smul_eq_mul, ENNReal.ofReal_mul (by positivity),
        measureReal_def, ENNReal.ofReal_inv_of_pos (ENNReal.toReal_pos hSpos hSfin),
        ENNReal.ofReal_toReal hSfin, hIntegral]
    _ ≤ _ := mul_le_mul_of_nonneg_left (lintegral_mono_set hST) bot_le

theorem abs_setAverage_sub_le_of_bound {u : X → ℝ} {S : Set X}
    (hS : MeasurableSet S) (hSpos : m S ≠ 0) (hSfin : m S ≠ ∞) (hu : IntegrableOn u S m)
    {a ε : ℝ} (h : ∀ y ∈ S, |u y - a| ≤ ε) :
    |(⨍ y in S, u y ∂m) - a| ≤ ε := by
  let ν := (m S)⁻¹ • m.restrict S
  have hν : ν univ = 1 := by
    rw [show ν univ = (m S)⁻¹ * m S by
      simp only [ν, smul_apply, Measure.restrict_apply_univ, smul_eq_mul],
      ENNReal.inv_mul_cancel hSpos hSfin]
  let : IsFiniteMeasure ν := ⟨hν ▸ ENNReal.one_lt_top⟩
  have hI : Integrable u ν := (integrable_smul_measure (ENNReal.inv_ne_zero.mpr hSfin)
      (ENNReal.inv_ne_top.mpr hSpos)).mpr hu
  have hconst (v : ℝ) : ∫ _ : X, v ∂ν = v := by
    simp only [integral_const, measureReal_def, hν, ENNReal.toReal_one, one_smul]
  rw [setAverage_eq' m u S]
  change |(∫ y, u y ∂ν) - a| ≤ ε
  rw [← hconst a, ← integral_sub hI (integrable_const a), ← Real.norm_eq_abs]
  apply (norm_integral_le_integral_norm _).trans
  have hAE : ∀ᵐ y ∂ν, y ∈ S :=
    (Measure.AbsolutelyContinuous.rfl.smul_left ((m S)⁻¹)).ae_le (ae_restrict_mem hS)
  have hbound : ∀ᵐ y ∂ν, ‖u y - a‖ ≤ ε := hAE.mono fun y hy ↦ by
    simpa only [Real.norm_eq_abs] using h y hy
  exact (integral_mono_ae (hI.sub (integrable_const a)).norm (integrable_const ε) hbound).trans_eq
    (hconst ε)

theorem abs_setAverage_le_realLp_norm {p : ℝ} (hp : 1 ≤ p) (f : RealLp m p)
    {S : Set X} (hSpos : m S ≠ 0) (hSfin : m S ≠ ∞) :
    |⨍ x in S, f x ∂m| ≤ (m.real S) ^ (-p⁻¹) * ‖f‖ := by
  have hp' : 0 < p := zero_lt_one.trans_le hp
  have hpExp := ENNReal.ofReal_ne_zero_iff.mpr hp'
  have hP := ofReal_abs_setAverage_sub_rpow_le hp (subset_refl S) hSpos hSfin
    ((Lp.memLp f).mono_measure Measure.restrict_le_self) 0
  simp only [sub_zero] at hP
  have hnorm : (∫⁻ x, ENNReal.ofReal |f x| ^ p ∂m) ^ p⁻¹ = eLpNorm f (ENNReal.ofReal p) m := by
    rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hpExp ENNReal.ofReal_ne_top
      (Lp.aestronglyMeasurable f)]
    simp only [ENNReal.toReal_ofReal hp'.le, Real.eNorm_eq_ofReal_abs, one_div]
  have hbound := hP.trans (mul_le_mul_of_nonneg_left
    (lintegral_mono_set (subset_univ S)) bot_le)
  have hroot := ENNReal.rpow_le_rpow hbound (inv_nonneg.mpr hp'.le)
  rw [← ENNReal.rpow_mul, mul_inv_cancel₀ hp'.ne', ENNReal.rpow_one,
    ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hp'.le), ENNReal.inv_rpow, ← ENNReal.rpow_neg, Measure.restrict_univ, hnorm] at hroot
  have hmass : (m S) ^ (-p⁻¹) ≠ ∞ := by
    rw [ENNReal.rpow_neg]
    exact ENNReal.inv_ne_top.mpr
      (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hSpos) hSfin).ne'
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top hmass (Lp.eLpNorm_lt_top f).ne) hroot
  simpa only [measureReal_def, ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_mul,
    ENNReal.toReal_rpow, Lp.norm_def] using h

/-- The distance between two averages is controlled by the mixed integral
of the increments over the two averaging sets. -/
theorem ofReal_abs_sub_setAverage_rpow_le {p : ℝ} (hp : 1 ≤ p) {u : X → ℝ}
    (hu : MemLp u (ENNReal.ofReal p) m) {S T : Set X}
    (hSpos : m S ≠ 0) (hTpos : m T ≠ 0) (hSfin : m S ≠ ∞) (hTfin : m T ≠ ∞) :
    ENNReal.ofReal |(⨍ x in S, u x ∂m) - (⨍ y in T, u y ∂m)| ^ p ≤
      ((m S)⁻¹ * (m T)⁻¹) * ∫⁻ x in S, (∫⁻ y in T, ENNReal.ofReal |u x - u y| ^ p ∂m) ∂m := by
  have hT (x : X) : ENNReal.ofReal |u x - (⨍ y in T, u y ∂m)| ^ p ≤
      (m T)⁻¹ * ∫⁻ y in T, ENNReal.ofReal |u x - u y| ^ p ∂m := by
    simpa only [abs_sub_comm] using
      ofReal_abs_setAverage_sub_rpow_le hp (subset_refl T) hTpos hTfin
        (hu.mono_measure Measure.restrict_le_self) (u x)
  refine (ofReal_abs_setAverage_sub_rpow_le hp (subset_refl S) hSpos hSfin
    (hu.mono_measure Measure.restrict_le_self) _).trans ?_
  calc
    _ ≤ (m S)⁻¹ * ∫⁻ x in S,
          ((m T)⁻¹ * ∫⁻ y in T, ENNReal.ofReal |u x - u y| ^ p ∂m) ∂m :=
      mul_le_mul_of_nonneg_left (lintegral_mono hT) bot_le
    _ = _ := by
      rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hTpos), ← mul_assoc]

end WalkDimensions
