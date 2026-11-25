import WalkDimensions.AverageOscillation
import WalkDimensions.AverageHolder

/-!
# Morrey estimates from Poincaré and Ahlfors regularity

The comparison of nearby averages and the dyadic argument use the total
mass of the energy measure.
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {m : Measure X} [IsFiniteMeasureOnCompacts m] [ProperSpace X] [m.IsOpenPosMeasure]
  {p : ℝ} (E : PEnergy m p)

/-- At comparable scales, Poincaré and the lower volume estimate bound the
change in the local average. -/
theorem exists_setAverage_sub_le_local {d β : ℝ} (hvol : AhlforsRegular m d)
    {Γ : E.domain → Measure X} (hPI : E.Poincare Γ β)
    (hΓ : ∀ f, Γ f univ = (E.energy f : ℝ≥0∞)) :
    ∃ K A : ℝ, 0 < K ∧ 1 ≤ A ∧ ∀ (f : E.domain) (x z : X) (r : ℝ), 0 < r → dist x z ≤ r →
      |(⨍ y in ball x r, (f : RealLp m p) y ∂m) -
        (⨍ y in ball z (2 * r), (f : RealLp m p) y ∂m)| ≤
        K * (Γ f (ball z (2 * A * r))).toReal ^ p⁻¹ * r ^ ((β - d) / p) := by
  obtain ⟨_, V, hV, hvolume⟩ := hvol
  obtain ⟨C, A, hC, hA, hpoincare⟩ := hPI
  have hp : 0 < p := zero_lt_one.trans E.one_lt
  let D := (2 : ℝ) ^ β * C * V
  have hD : 0 < D := by positivity
  refine ⟨D ^ p⁻¹, A, by positivity, hA, fun f x z r hr hdist ↦ ?_⟩
  let u := (f : RealLp m p)
  let S := ball x r
  let T := ball z (2 * r)
  let c := ⨍ y in T, u y ∂m
  have hST : S ⊆ T := by
    intro y hy
    apply mem_ball.mpr
    apply (dist_triangle y x z).trans_lt
    have h := mem_ball.mp hy
    linarith only [h, hdist]
  have hJ := ofReal_abs_setAverage_sub_rpow_le E.one_lt.le hST
    (measure_ball_pos m x hr).ne' measure_ball_ne_top
    ((Lp.memLp u).mono_measure Measure.restrict_le_self) c
  have hV' : 0 < r ^ d / V := div_pos (Real.rpow_pos_of_pos hr _) hV
  have hInv : (m S)⁻¹ ≤ ENNReal.ofReal (V / r ^ d) := by
    have h := ENNReal.inv_le_inv.mpr (hvolume x r hr).1
    rw [← ENNReal.ofReal_inv_of_pos hV', inv_div] at h
    exact h
  let M := Γ f (ball z (2 * A * r))
  have hM : M ≠ ∞ := ((measure_mono (subset_univ _) : M ≤ Γ f univ).trans_lt
    (hΓ f ▸ ENNReal.coe_lt_top)).ne
  have hP : (∫⁻ y in T, ENNReal.ofReal |u y - c| ^ p ∂m) ≤
      ENNReal.ofReal (C * (2 * r) ^ β) * M := by
    simpa only [M, T, mul_left_comm A 2, mul_assoc] using hpoincare z (2 * r) (by positivity) f
  have hproduct :
      ENNReal.ofReal (V / r ^ d) * (ENNReal.ofReal (C * (2 * r) ^ β) * M) =
        ENNReal.ofReal (D * M.toReal * r ^ (β - d)) := by
    rw [← ENNReal.ofReal_toReal hM, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    rw [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
    congr 1
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hr.le, Real.rpow_sub hr]
    dsimp only [D]
    ring
  have hle := hJ.trans ((mul_le_mul hInv hP bot_le bot_le).trans_eq hproduct)
  rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp.le,
    ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ D * M.toReal * r ^ (β - d))] at hle
  have hroot := Real.rpow_le_rpow (Real.rpow_nonneg (abs_nonneg _) _) hle (inv_nonneg.mpr hp.le)
  rw [← Real.rpow_mul (abs_nonneg _), mul_inv_cancel₀ hp.ne', Real.rpow_one,
    Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow hD.le ENNReal.toReal_nonneg,
    ← Real.rpow_mul hr.le, ← div_eq_mul_inv] at hroot
  exact hroot


/-- At comparable scales, Poincaré and the lower volume estimate bound the
change in the local average. -/
theorem exists_setAverage_sub_le {d β : ℝ} (hvol : AhlforsRegular m d)
    {Γ : E.domain → Measure X} (hPI : E.Poincare Γ β)
    (hΓ : ∀ f, Γ f univ = (E.energy f : ℝ≥0∞)) :
    ∃ K > (0 : ℝ), ∀ (f : E.domain) (x z : X) (r : ℝ), 0 < r → dist x z ≤ r →
      |(⨍ y in ball x r, (f : RealLp m p) y ∂m) -
        (⨍ y in ball z (2 * r), (f : RealLp m p) y ∂m)| ≤
        K * E.rootSeminorm f * r ^ ((β - d) / p) := by
  obtain ⟨K, A, hK, _, hbound⟩ := E.exists_setAverage_sub_le_local hvol hPI hΓ
  refine ⟨K, hK, fun f x z r hr hdist ↦ (hbound f x z r hr hdist).trans ?_⟩
  have hp := zero_lt_one.trans E.one_lt
  have hM : Γ f (ball z (2 * A * r)) ≤ (E.energy f : ℝ≥0∞) :=
    (measure_mono (subset_univ _)).trans_eq (hΓ f)
  have h := ENNReal.toReal_mono ENNReal.coe_ne_top hM
  rw [ENNReal.coe_toReal] at h
  rw [E.rootSeminorm_apply]
  gcongr


variable [SecondCountableTopology X]

/-- The Morrey bound holds at every pair of Lebesgue points. The full
measure statement records where the averages recover the (L^p) class. -/
theorem exists_morrey_bound_at_lebesgue_points {d β : ℝ} (hvol : AhlforsRegular m d)
    (hβ : d < β) {Γ : E.domain → Measure X} (hPI : E.Poincare Γ β)
    (hΓ : ∀ f, Γ f univ = (E.energy f : ℝ≥0∞)) :
    ∃ H > (0 : ℝ), ∀ f : E.domain, ∃ S : Set X,
      (∀ᵐ x ∂m, x ∈ S) ∧ ∀ x ∈ S, ∀ y ∈ S,
        |(f : RealLp m p) x - (f : RealLp m p) y| ≤
          H * E.rootSeminorm f * dist x y ^ ((β - d) / p) := by
  obtain ⟨K, hK, hKbound⟩ := E.exists_setAverage_sub_le hvol hPI hΓ
  let e := (β - d) / p
  have he : 0 < e := div_pos (sub_pos.mpr hβ) (zero_lt_one.trans E.one_lt)
  obtain ⟨L, hL, hbound⟩ := exists_holder_bound_at_lebesgue_points hvol.volumeDoubling he
  refine ⟨L * K, mul_pos hL hK, fun f ↦ ?_⟩
  obtain ⟨S, hS, hEstimate⟩ := hbound
    ((Lp.memLp (f : RealLp m p)).locallyIntegrable (ENNReal.one_le_ofReal.mpr E.one_lt.le))
    (mul_nonneg hK.le (apply_nonneg E.rootSeminorm f)) (hKbound f)
  refine ⟨S, hS, fun x hx y hy ↦ ?_⟩
  simpa only [mul_assoc] using hEstimate x hx y hy



/-- In the supercritical range, every energy-domain element has a globally
Hölder continuous representative. -/
theorem exists_holder_representative {d β : ℝ} (hvol : AhlforsRegular m d)
    (hβ : d < β) {Γ : E.domain → Measure X} (hPI : E.Poincare Γ β)
    (hΓ : ∀ f, Γ f univ = (E.energy f : ℝ≥0∞)) :
    ∃ H > (0 : ℝ), ∀ f : E.domain, ∃ v : X → ℝ,
      Continuous v ∧ (f : RealLp m p) =ᵐ[m] v ∧
      ∀ x y, |v x - v y| ≤ H * E.rootSeminorm f * dist x y ^ ((β - d) / p) := by
  obtain ⟨H, hH, hholder⟩ := E.exists_morrey_bound_at_lebesgue_points hvol hβ hPI hΓ
  refine ⟨H, hH, fun f ↦ ?_⟩
  obtain ⟨S, hS, hSbound⟩ := hholder f
  have he : 0 < (β - d) / p := div_pos (sub_pos.mpr hβ) (zero_lt_one.trans E.one_lt)
  exact exists_holder_representative_of_full_measure hS he
    (mul_nonneg hH.le (apply_nonneg E.rootSeminorm f)) hSbound

end WalkDimensions.PEnergy
