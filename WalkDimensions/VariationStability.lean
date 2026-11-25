import WalkDimensions.EnergyDerivativeLaws
import Mathlib.Analysis.Convex.Deriv

/-!
# Stability of first variation with bounded varying directions
-/

open Asymptotics Filter Function MeasureTheory Set
open scoped ENNReal Topology

namespace WalkDimensions

section Seminorm

variable {Y : Type*} [AddCommGroup Y] [Module ℝ Y]

private theorem convexOn_line_root_rpow (S : Seminorm ℝ Y) {p : ℝ} (hp : 1 ≤ p)
    (x y : Y) : ConvexOn ℝ univ (fun t : ℝ ↦ S (x + t • y) ^ p) := by
  refine ⟨convex_univ, fun a _ b _ s t hs ht hst ↦ ?_⟩
  change S (x + (s * a + t * b) • y) ^ p ≤
    s * S (x + a • y) ^ p + t * S (x + b • y) ^ p
  have he : x + (s * a + t * b) • y = s • (x + a • y) + t • (x + b • y) := by
    rw [smul_add, smul_add, smul_smul, smul_smul, add_smul]
    have h := congrArg (fun k : ℝ ↦ k • x) hst
    rw [add_smul, one_smul] at h
    calc
      _ = (s • x + t • x) + ((s * a) • y + (t * b) • y) :=
        congrArg (fun z : Y ↦ z + ((s * a) • y + (t * b) • y)) h.symm
      _ = _ := by abel
  have h := map_add_le_add S (s • (x + a • y)) (t • (x + b • y))
  rw [map_smul_eq_mul, map_smul_eq_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hs, abs_of_nonneg ht, ← he] at h
  refine (Real.rpow_le_rpow (apply_nonneg _ _) h (zero_le_one.trans hp)).trans ?_
  exact (convexOn_rpow hp).2 (mem_Ici.mpr (apply_nonneg S _))
    (mem_Ici.mpr (apply_nonneg S _)) hs ht hst

private theorem bracketing_firstVariation (S : Seminorm ℝ Y) {p : ℝ} (hp : 1 ≤ p)
    (P : Y → ℝ) (hEq : ∀ u, P u = S u ^ p) (D : Y → Y → ℝ)
    (hD : ∀ x y, HasDerivAt (fun t : ℝ ↦ P (x + t • y)) (p * D x y) 0)
    (x y : Y) {t : ℝ} (ht : 0 < t) :
    (P x - P (x - t • y)) / t ≤ p * D x y ∧
      p * D x y ≤ (P (x + t • y) - P x) / t := by
  have hconv : ConvexOn ℝ univ (fun t : ℝ ↦ P (x + t • y)) := by
    simpa only [hEq] using convexOn_line_root_rpow S hp x y
  constructor
  · have h := hconv.slope_le_of_hasDerivAt (mem_univ (-t)) (mem_univ 0) (neg_lt_zero.mpr ht) (hD x y)
    simpa only [slope_def_field, zero_sub, neg_neg, zero_smul, add_zero, neg_smul, ← sub_eq_add_neg] using h
  · have h := hconv.le_slope_of_hasDerivAt (mem_univ 0) (mem_univ t) ht (hD x y)
    simpa only [slope_def_field, sub_zero, zero_smul, add_zero] using h

private theorem tendsto_energy_perturbation_of_bounded (S : Seminorm ℝ Y) {p : ℝ} (hp : 0 ≤ p)
    {C : ℝ} {u v : ℕ → Y}
    (hU : ∀ n, S (u n) ≤ C) (h : Tendsto (fun n ↦ S (v n - u n)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ S (v n) ^ p - S (u n) ^ p) atTop (𝓝 0) := by
  have hc : UniformContinuousOn (fun b : ℝ ↦ b ^ p) (Icc 0 (C + 1)) :=
    isCompact_Icc.uniformContinuousOn_of_continuous (Real.continuous_rpow_const hp).continuousOn
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hcl⟩ := Metric.uniformContinuousOn_iff.mp hc ε hε
  filter_upwards [h.eventually_lt_const (lt_min hδ zero_lt_one)] with n hn
  have hU' : S (u n) ∈ Icc 0 (C + 1) := ⟨apply_nonneg _ _, (hU n).trans (by linarith)⟩
  have hUV : |S (v n) - S (u n)| ≤ S (v n - u n) := abs_sub_map_le_sub _ _ _
  have hV' : S (v n) ∈ Icc 0 (C + 1) := by
    refine ⟨apply_nonneg _ _, ?_⟩
    have he := ((le_abs_self _).trans hUV).trans_lt (hn.trans_le (min_le_right _ _))
    linarith only [he, hU n]
  have he := hcl _ hV' _ hU' (by rw [Real.dist_eq]; exact hUV.trans_lt (hn.trans_le (min_le_left _ _)))
  simpa only [Real.dist_eq, sub_zero] using he

theorem tendsto_firstVariation_sub_of_bounded (S : Seminorm ℝ Y) {p : ℝ} (hp : 1 < p)
    (P : Y → ℝ) (hEq : ∀ u, P u = S u ^ p)
    (hUpper₂ : p ≤ 2 → ∀ f g, P (f + g) + P (f - g) ≤ 2 * (P f + P g))
    (hUpper : 2 ≤ p → ∀ f g, P (f + g) + P (f - g) ≤
      2 * (P f ^ (p - 1)⁻¹ + P g ^ (p - 1)⁻¹) ^ (p - 1))
    (D : Y → Y → ℝ) (hD : ∀ x y, HasDerivAt (fun t : ℝ ↦ P (x + t • y)) (p * D x y) 0)
    {u : Y} {v g : ℕ → Y} {C : ℝ} (hC : 0 ≤ C) (hg : ∀ n, S (g n) ≤ C)
    (h : Tendsto (fun n ↦ S (v n - u)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ D (v n) (g n) - D u (g n)) atTop (𝓝 0) := by
  have hp₀ := zero_lt_one.trans hp
  obtain ⟨M, hM, hM₀, hMbound⟩ := exists_symm_upper_envelope_of_bound hp P
    (fun x ↦ hEq x ▸ Real.rpow_nonneg (apply_nonneg S x) _)
    (fun a x ↦ by rw [hEq, hEq, map_smul_eq_mul, Real.norm_eq_abs,
      Real.mul_rpow (abs_nonneg _) (apply_nonneg _ _)]) hUpper₂ hUpper u
    (Real.rpow_nonneg hC p)
  have hMbound' (n : ℕ) (t : ℝ) :
      P (u + t • g n) + P (u - t • g n) ≤ M t :=
    hMbound (g n) (hEq (g n) ▸ Real.rpow_le_rpow (apply_nonneg _ _) (hg n) hp₀.le) t
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let e := p * ε / 4
  have he : 0 < e := by dsimp only [e]; positivity
  have hO := (isLittleO_iff.mp hM.isLittleO) he
  simp only [smul_zero, sub_zero, Real.norm_eq_abs] at hO
  have hO' : ∀ᶠ t in 𝓝[>] (0 : ℝ), |M t - M 0| ≤ e * |t| := hO.filter_mono nhdsWithin_le_nhds
  have ht' : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := eventually_mem_nhdsWithin
  obtain ⟨t, ht, hMt⟩ := (ht'.and hO').exists
  have hWidth (n : ℕ) :
      P (u + t • g n) + P (u - t • g n) - 2 * P u ≤ e * t := by
    rw [← hM₀]
    exact (sub_le_sub_right (hMbound' n t) _).trans ((le_abs_self _).trans (by
      simpa only [abs_of_pos ht] using hMt))
  have hShift (k : ℝ) : Tendsto (fun n ↦ P (v n + k • g n) - P (u + k • g n)) atTop (𝓝 0) := by
    simp only [hEq]
    apply tendsto_energy_perturbation_of_bounded S hp₀.le
      (C := S u + |k| * C)
    · intro n
      apply (map_add_le_add _ _ _).trans
      rw [map_smul_eq_mul, Real.norm_eq_abs]
      exact add_le_add_right (mul_le_mul_of_nonneg_left (hg n) (abs_nonneg _)) _
    · simpa only [add_sub_add_right_eq_sub] using h
  have h0 : Tendsto (fun n ↦ P (v n) - P u) atTop (𝓝 0) := by
    simpa only [zero_smul, add_zero] using hShift 0
  have hm : Tendsto (fun n ↦ P (v n - t • g n) - P (u - t • g n)) atTop (𝓝 0) := by
    simpa only [neg_smul, ← sub_eq_add_neg] using hShift (-t)
  filter_upwards [((hShift t).abs.eventually_lt_const (mul_pos he ht)),
    h0.abs.eventually_lt_const (mul_pos he ht), hm.abs.eventually_lt_const (mul_pos he ht)] with n h₁ h₂ h₃
  have ⟨hlo, hhi⟩ := bracketing_firstVariation S hp.le P hEq D hD u (g n) ht
  have ⟨hlo', hhi'⟩ := bracketing_firstVariation S hp.le P hEq D hD (v n) (g n) ht
  have hloT := (div_le_iff₀ ht).mp hlo
  have hhiT := (le_div_iff₀ ht).mp hhi
  have hloT' := (div_le_iff₀ ht).mp hlo'
  have hhiT' := (le_div_iff₀ ht).mp hhi'
  have h₁' := abs_lt.mp h₁
  have h₂' := abs_lt.mp h₂
  have h₃' := abs_lt.mp h₃
  rw [Real.dist_eq, sub_zero, abs_lt]
  constructor
  · apply (mul_lt_mul_iff_right₀ (mul_pos hp₀ ht)).mp
    dsimp only [e] at h₁' h₂' h₃'
    have hW := hWidth n
    dsimp only [e] at hW
    nlinarith only [hhiT, hloT', h₂'.1, h₃'.2, hW, mul_pos (mul_pos hp₀ hε) ht]
  · apply (mul_lt_mul_iff_right₀ (mul_pos hp₀ ht)).mp
    dsimp only [e] at h₁' h₂' h₃'
    have hW := hWidth n
    dsimp only [e] at hW
    nlinarith only [hloT, hhiT', h₁'.2, h₂'.1, hW, mul_pos (mul_pos hp₀ hε) ht]

end Seminorm

namespace PEnergy

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {m : Measure X} [IsFiniteMeasureOnCompacts m] {p : ℝ} (E : PEnergy m p)

theorem tendsto_energyDerivativeMeasure_sub_of_bounded
    {u : E.domain} {v g : ℕ → E.domain} {C : ℝ} (hC : 0 ≤ C) (hg : ∀ n, E.rootSeminorm (g n) ≤ C)
    (h : Tendsto (fun n ↦ E.rootSeminorm (v n - u)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ E.energyDerivativeMeasure (v n) (g n) univ -
      E.energyDerivativeMeasure u (g n) univ) atTop (𝓝 0) := by
  apply tendsto_firstVariation_sub_of_bounded E.rootSeminorm E.one_lt
    (fun f ↦ (E.energy f : ℝ)) E.energy_eq_root_rpow ?_ ?_
    (fun f g ↦ E.energyDerivativeMeasure f g univ) E.hasDerivAt_energy_of_energyDerivativeMeasure hC hg h
  · intro hp f g
    simpa only [E.energyMeasure_univ, ENNReal.coe_toReal] using
      E.energyMeasure_real_pair_upper_le_two_mul hp f g MeasurableSet.univ
  · intro hp f g
    simpa only [E.energyMeasure_univ, ENNReal.coe_toReal] using
      E.energyMeasure_real_clarkson_upper hp f g MeasurableSet.univ

end PEnergy

end WalkDimensions
