import WalkDimensions.BallDifferentiation
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Hölder estimates from comparisons of averages

A summable sequence of differences at dyadic scales controls each
Lebesgue point. Full support then extends the bound to all points.
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal Topology

namespace WalkDimensions

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  [SecondCountableTopology X] {m : Measure X} [IsFiniteMeasureOnCompacts m]
  [m.IsOpenPosMeasure]

omit [BorelSpace X] [ProperSpace X] [SecondCountableTopology X]
  [IsFiniteMeasureOnCompacts m] [m.IsOpenPosMeasure] in
theorem abs_sub_setAverage_le_of_dyadic_bound {u : X → ℝ} {x : X} {e K r : ℝ}
    (he : 0 < e) (hK : 0 ≤ K) (hr : 0 < r)
    (hx : Tendsto (fun t ↦ ⨍ y in ball x t, u y ∂m) (𝓝[>] (0 : ℝ)) (𝓝 (u x)))
    (hKbound : ∀ t > (0 : ℝ), t ≤ r →
      |(⨍ y in ball x t, u y ∂m) - (⨍ y in ball x (2 * t), u y ∂m)| ≤ K * t ^ e) :
    |u x - ⨍ y in ball x r, u y ∂m| ≤ (K / (1 - (1 / 2 : ℝ) ^ e)) * r ^ e := by
  let a := (1 / 2 : ℝ) ^ e
  have ha₀ : 0 ≤ a := by dsimp [a]; positivity
  have ha₁ : a < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) he
  let avg (x : X) (r : ℝ) := ⨍ y in ball x r, u y ∂m
  let ρ : ℕ → ℝ := fun n ↦ r * (1 / 2 : ℝ) ^ n
  have hρpos (n : ℕ) : 0 < ρ n := by dsimp [ρ]; positivity
  have hρzero : ρ 0 = r := by simp [ρ]
  have hρsucc (n : ℕ) : 2 * ρ (n + 1) = ρ n := by dsimp [ρ]; rw [pow_succ]; ring
  have hρle (n : ℕ) : ρ (n + 1) ≤ ρ n := by
    rw [← hρsucc n]
    linarith only [(hρpos (n + 1)).le]
  have hρle_r (n : ℕ) : ρ n ≤ r := by
    rw [← hρzero]
    exact (antitone_nat_of_succ_le hρle) (Nat.zero_le n)
  have hρlim : Tendsto ρ atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨by simpa only [mul_zero] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num)).const_mul r,
      Eventually.of_forall hρpos⟩
  have hlim : Tendsto (fun n ↦ avg x (ρ n)) atTop (𝓝 (u x)) :=
    hx.comp hρlim
  have hpow (n : ℕ) : (ρ n) ^ e = r ^ e * a ^ n := by
    dsimp only [ρ, a]
    rw [Real.mul_rpow hr.le (by positivity), ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
      mul_comm (n : ℝ), Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2), Real.rpow_natCast]
  have hstep (n : ℕ) :
      dist (avg x (ρ n)) (avg x (ρ (n + 1))) ≤ (K * r ^ e) * a ^ n := by
    have h := hKbound (ρ (n + 1)) (hρpos _) (hρle_r _)
    change |avg x (ρ (n + 1)) - avg x (2 * ρ (n + 1))| ≤ _ at h
    rw [hρsucc n, abs_sub_comm] at h
    rw [Real.dist_eq]
    calc
      _ ≤ K * ρ (n + 1) ^ e := h
      _ ≤ K * ρ n ^ e :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (hρpos _).le (hρle n) he.le) (by positivity)
      _ = _ := by rw [hpow]; ring
  have hbound (n : ℕ) : dist (avg x r) (avg x (ρ n)) ≤
      (K / (1 - a)) * r ^ e := by
    have hSum : (∑ j ∈ Finset.range n, a ^ j) ≤ (1 - a)⁻¹ := by
      rw [Finset.range_eq_Ico]
      simpa only [pow_zero, one_div] using (geom_sum_Ico_le_of_lt_one (m := 0) (n := n) ha₀ ha₁)
    calc
      _ ≤ ∑ j ∈ Finset.range n, dist (avg x (ρ j)) (avg x (ρ (j + 1))) := by
        simpa only [hρzero] using dist_le_range_sum_dist (fun j ↦ avg x (ρ j)) n
      _ ≤ ∑ j ∈ Finset.range n, (K * r ^ e) * a ^ j :=
        Finset.sum_le_sum fun j _ ↦ hstep j
      _ = (K * r ^ e) * (∑ j ∈ Finset.range n, a ^ j) :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ (K * r ^ e) * (1 - a)⁻¹ :=
        mul_le_mul_of_nonneg_left hSum (by positivity)
      _ = _ := by ring
  have hCLim := (continuous_const.dist continuous_id : Continuous (fun b : ℝ ↦ dist (avg x r) b))
  have hdist := (hCLim.tendsto (u x)).comp hlim
  have hle := le_of_tendsto hdist (Eventually.of_forall hbound)
  simpa only [Function.comp_apply, Real.dist_eq, abs_sub_comm (avg x r) (u x)] using hle

theorem exists_holder_bound_at_lebesgue_points (hvol : VolumeDoubling m)
    {e : ℝ} (he : 0 < e) :
    ∃ H > (0 : ℝ), ∀ {u : X → ℝ}, LocallyIntegrable u m → ∀ {K : ℝ}, 0 ≤ K →
      (∀ x z : X, ∀ r > (0 : ℝ), dist x z ≤ r →
        |(⨍ y in ball x r, u y ∂m) - (⨍ y in ball z (2 * r), u y ∂m)| ≤ K * r ^ e) →
      ∃ S : Set X, (∀ᵐ x ∂m, x ∈ S) ∧
        ∀ x ∈ S, ∀ y ∈ S, |u x - u y| ≤ H * K * dist x y ^ e := by
  let a := (1 / 2 : ℝ) ^ e
  have ha₁ : a < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) he
  have hden : 0 < 1 - a := sub_pos.mpr ha₁
  refine ⟨2 * ((1 - a)⁻¹ + 1), by positivity, ?_⟩
  intro u hu K hK hKbound
  let avg (x : X) (r : ℝ) := ⨍ y in ball x r, u y ∂m
  let S : Set X := {x | Tendsto (avg x) (𝓝[>] (0 : ℝ)) (𝓝 (u x))}
  have hS : ∀ᵐ x ∂m, x ∈ S := hvol.ae_tendsto_openBall_average hu
  refine ⟨S, hS, ?_⟩
  have htail (x : X) (hx : x ∈ S) {r : ℝ} (hr : 0 < r) :
      |u x - avg x r| ≤ (K / (1 - a)) * r ^ e :=
    abs_sub_setAverage_le_of_dyadic_bound he hK hr hx
      (fun t ht _ ↦ hKbound x x t ht (by simpa using ht.le))
  intro x hx y hy
  by_cases heq : x = y
  · subst y
    simp only [sub_self, abs_zero, dist_self]
    positivity
  · let r := dist x y
    have hr : 0 < r := dist_pos.mpr heq
    have hx' : |avg x r - avg x (2 * r)| ≤ K * r ^ e :=
      hKbound x x r hr (by simpa using hr.le)
    have hy' : |avg y r - avg x (2 * r)| ≤ K * r ^ e :=
      hKbound y x r hr (by simp [r, dist_comm y x])
    calc
      |u x - u y| ≤ |u x - avg x r| + |avg x r - avg x (2 * r)| +
          |avg y r - avg x (2 * r)| + |u y - avg y r| := by
        rw [← Real.dist_eq, ← Real.dist_eq, ← Real.dist_eq, ← Real.dist_eq, ← Real.dist_eq,
          dist_comm (avg y r), dist_comm (u y)]
        have h₁ := dist_triangle (u x) (avg x r) (u y)
        have h₂ := dist_triangle (avg x r) (avg x (2 * r)) (u y)
        have h₃ := dist_triangle (avg x (2 * r)) (avg y r) (u y)
        linarith only [h₁, h₂, h₃]
      _ ≤ 2 * (K / (1 - a) + K) * r ^ e := by
        linarith only [htail x hx hr, htail y hy hr, hx', hy']
      _ = _ := by dsimp [r]; rw [div_eq_mul_inv]; ring

omit [BorelSpace X] [ProperSpace X] [SecondCountableTopology X] [IsFiniteMeasureOnCompacts m] in
theorem exists_holder_representative_of_full_measure {w : X → ℝ} {S : Set X}
    (hS : ∀ᵐ x ∂m, x ∈ S) {e D : ℝ} (he : 0 < e) (hD : 0 ≤ D)
    (hSbound : ∀ x ∈ S, ∀ y ∈ S, |w x - w y| ≤ D * dist x y ^ e) :
    ∃ v : X → ℝ, Continuous v ∧ w =ᵐ[m] v ∧
      ∀ x y, |v x - v y| ≤ D * dist x y ^ e := by
  have hdense : Dense S := Measure.dense_of_ae hS
  let u : S → ℝ := fun x ↦ w x
  have hR : Continuous (fun r : ℝ ↦ D * r ^ e) :=
    (Real.continuous_rpow_const he.le).const_mul D
  have hu : UniformContinuous u := by
    apply Metric.uniformContinuous_iff.mpr
    intro ε hε
    obtain ⟨δ, hδ, hδbound⟩ := Metric.continuousAt_iff.mp (hR.continuousAt (x := 0)) ε hε
    refine ⟨δ, hδ, fun x y hxy ↦ ?_⟩
    have h := hδbound (x := dist (x : X) (y : X)) (by
      simpa only [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg, Subtype.dist_eq] using hxy)
    change dist (D * dist (x : X) (y : X) ^ e) (D * (0 : ℝ) ^ e) < ε at h
    rw [Real.dist_eq, Real.zero_rpow he.ne', mul_zero, sub_zero, abs_of_nonneg (by positivity)] at h
    rw [Real.dist_eq]
    exact (hSbound x x.property y y.property).trans_lt h
  let v := hdense.extend u
  have hv : Continuous v := (hdense.uniformContinuous_extend hu).continuous
  have hEq (x : S) : v x = u x := hdense.extend_of_ind hu x
  refine ⟨v, hv, hS.mono (fun x hx ↦ (hEq ⟨x, hx⟩).symm), ?_⟩
  have hclosed : IsClosed {z : X × X | |v z.1 - v z.2| ≤ D * dist z.1 z.2 ^ e} :=
    isClosed_le (continuous_abs.comp ((hv.comp continuous_fst).sub (hv.comp continuous_snd)))
      (hR.comp (continuous_fst.dist continuous_snd))
  exact hdense.denseRange_subtypeVal.induction_on₂ hclosed (fun x y ↦ by
    rw [hEq x, hEq y]
    exact hSbound x x.property y y.property)


end WalkDimensions
