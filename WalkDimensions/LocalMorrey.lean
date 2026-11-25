import WalkDimensions.Morrey

/-!
# The localized Morrey estimate

Dyadic comparisons of averages only use the energy measure on a fixed
enlargement of the original ball.
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal Topology

namespace WalkDimensions

variable {X : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X] [BorelSpace X]
  {m : Measure X} [IsFiniteMeasureOnCompacts m] [m.IsOpenPosMeasure]

theorem tendsto_ball_average_of_continuous_compact {u : X → ℝ} (hu : Continuous u)
    (hc : HasCompactSupport u) (x : X) :
    Tendsto (fun r ↦ ⨍ y in ball x r, u y ∂m) (𝓝[>] (0 : ℝ)) (𝓝 (u x)) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.1 hu.continuousAt (ε / 2) (half_pos hε)
  filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
  rw [Real.dist_eq]
  refine (abs_setAverage_sub_le_of_bound measurableSet_ball (measure_ball_pos m x hr.1).ne'
    measure_ball_ne_top (hu.integrable_of_hasCompactSupport hc).integrableOn ?_).trans_lt
      (half_lt_self hε)
  intro y hy
  simpa only [Real.dist_eq] using (h ((mem_ball.mp hy).trans hr.2)).le

namespace PEnergy

variable {p : ℝ} (E : PEnergy m p)

theorem exists_local_morrey_bound {d β : ℝ}
    (hvol : AhlforsRegular m d) (hβ : d < β)
    {Γ : E.domain → Measure X} (hPI : E.Poincare Γ β)
    (hΓ : ∀ f, Γ f univ = (E.energy f : ℝ≥0∞)) :
    ∃ C A : ℝ, 0 < C ∧ 1 ≤ A ∧ ∀ (f : E.domain) {u : X → ℝ},
      Continuous u → HasCompactSupport u → (f : RealLp m p) =ᵐ[m] u →
      ∀ (z : X) {r : ℝ}, 0 < r → ∀ x ∈ ball z r, ∀ y ∈ ball z r,
        |u x - u y| ≤ C * (Γ f (ball z (A * r))).toReal ^ p⁻¹ * r ^ ((β - d) / p) := by
  obtain ⟨K, A, hK, hA, hbound⟩ := E.exists_setAverage_sub_le_local hvol hPI hΓ
  let e := (β - d) / p
  have hp := zero_lt_one.trans E.one_lt
  have he : 0 < e := div_pos (sub_pos.mpr hβ) hp
  let a := (1 / 2 : ℝ) ^ e
  have ha : 0 < 1 - a := sub_pos.mpr (Real.rpow_lt_one (by norm_num) (by norm_num) he)
  refine ⟨2 * K * ((1 - a)⁻¹ + 1), 2 * A + 1, by positivity, by linarith, ?_⟩
  intro f u hu hc hfu z r hr x hx y hy
  let G := Γ f (ball z ((2 * A + 1) * r))
  have hGfin : G ≠ ∞ := ((measure_mono (subset_univ _) : G ≤ Γ f univ).trans_lt
    (hΓ f ▸ ENNReal.coe_lt_top)).ne
  let B := K * G.toReal ^ p⁻¹
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let L (z : X) (t : ℝ) := ⨍ w in ball z t, u w ∂m
  have hstep (w v : X) (hv : v ∈ ball z r) (t : ℝ) (ht : 0 < t) (htr : t ≤ r)
      (hWV : dist w v ≤ t) : |L w t - L v (2 * t)| ≤ B * t ^ e := by
    have hsub : ball v (2 * A * t) ⊆ ball z ((2 * A + 1) * r) := by
      intro b hb
      apply mem_ball.mpr
      calc
        _ ≤ dist b v + dist v z := dist_triangle _ _ _
        _ < 2 * A * t + r := add_lt_add (mem_ball.mp hb) (mem_ball.mp hv)
        _ ≤ _ := by nlinarith
    have hMass := ENNReal.toReal_mono hGfin (measure_mono (μ := Γ f) hsub)
    have hf := hbound f w v t ht hWV
    rw [average_congr (ae_restrict_of_ae hfu), average_congr (ae_restrict_of_ae hfu)] at hf
    exact hf.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow ENNReal.toReal_nonneg hMass (inv_nonneg.mpr hp.le)) hK.le)
      (Real.rpow_nonneg ht.le _))
  have htail (v : X) (hv : v ∈ ball z r) :
      |u v - L v r| ≤ (B / (1 - a)) * r ^ e :=
    abs_sub_setAverage_le_of_dyadic_bound he hB hr (tendsto_ball_average_of_continuous_compact hu hc v)
      (fun t ht htr ↦ hstep v v hv t ht htr (by simpa only [dist_self] using ht.le))
  have hx' := hstep x z (mem_ball_self hr) r hr le_rfl (mem_ball.mp hx).le
  have hy' := hstep y z (mem_ball_self hr) r hr le_rfl (mem_ball.mp hy).le
  calc
    _ ≤ |u x - L x r| + |L x r - L z (2 * r)| +
        |L y r - L z (2 * r)| + |u y - L y r| := by
      simp only [← Real.dist_eq, dist_comm (L y r) (L z (2 * r)), dist_comm (u y) (L y r)]
      have h₁ := dist_triangle (u x) (L x r) (u y)
      have h₂ := dist_triangle (L x r) (L z (2 * r)) (u y)
      have h₃ := dist_triangle (L z (2 * r)) (L y r) (u y)
      linarith only [h₁, h₂, h₃]
    _ ≤ 2 * (B / (1 - a) + B) * r ^ e := by
      linarith only [htail x hx, htail y hy, hx', hy']
    _ = _ := by dsimp only [B, G, e]; rw [div_eq_mul_inv]; ring

end PEnergy

end WalkDimensions
