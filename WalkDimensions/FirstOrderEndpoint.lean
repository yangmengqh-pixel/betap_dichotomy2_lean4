import WalkDimensions.ConnectivitySelfImprovement
import WalkDimensions.FirstOrderInterpolation
import WalkDimensions.TimedPathSlope
import WalkDimensions.WalkExponentFamily

/-!
# A first-order connectivity estimate forces first-order energy scaling
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal NNReal Topology

namespace WalkDimensions

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [Nonempty X] [ProperSpace X] [SecondCountableTopology X] {m : Measure X}
  [m.Regular] [SFinite m] [m.IsOpenPosMeasure]

omit [Nonempty X] [SecondCountableTopology X] [SFinite m] in
theorem localMaximalAverage_le_integral_of_zero_near {D : ℝ≥0∞}
    (hD : ∀ (x : X) (r : ℝ), 0 < r → m (ball x (2 * r)) ≤ D * m (ball x r))
    (f : X → ℝ≥0∞) (x : X) {a : ℝ} (ha : 0 < a) (hz : EqOn f (fun _ ↦ 0) (ball x (2 * a)))
    (R : ℝ) : localMaximalAverage m f R x ≤ (D * (m (ball x a))⁻¹) * ∫⁻ y, f y ∂m := by
  apply iSup_le
  intro z
  apply iSup_le
  intro s
  apply iSup_le
  intro hs
  apply iSup_le
  intro hx
  change (∫⁻ y, f y ∂normalizedBall m z s) ≤ _
  rw [normalizedBall, lintegral_smul_measure, smul_eq_mul]
  by_cases hsa : s ≤ a
  · have hsub : ball z s ⊆ ball x (2 * a) := by
      intro y hy
      apply mem_ball.mpr
      have h := dist_triangle y z x
      rw [dist_comm z x] at h
      linarith only [h, hsa, mem_ball.mp hy, mem_ball.mp hx]
    have hInt : (∫⁻ y in ball z s, f y ∂m) = 0 := by
      apply (lintegral_congr_ae (g := fun _ ↦ 0) ?_).trans lintegral_zero
      filter_upwards [ae_restrict_mem (μ := m) (s := ball z s) measurableSet_ball] with y hy
      exact hz (hsub hy)
    rw [hInt, mul_zero]
    exact bot_le
  · have hs₀ : 0 < s := hs.1
    have he := measure_ball_le_of_dist_le hD (x := z) (y := x) hs₀ 1 (t := a) (by
      have hh := mem_ball.mp hx
      norm_num
      linarith only [hh, lt_of_not_ge hsa])
    have hinv := inv_measure_le_mul_inv_of_le (measure_ball_pos m z hs₀).ne'
      (measure_ball_pos m x ha).ne' measure_ball_ne_top measure_ball_ne_top (by simpa only [pow_one] using he)
    have hInt : (∫⁻ y in ball z s, f y ∂m) ≤ ∫⁻ y, f y ∂m := by
      exact lintegral_mono' Measure.restrict_le_self le_rfl
    exact mul_le_mul hinv hInt bot_le bot_le

namespace PEnergy

theorem walkExponent_eq_of_connectivity {q β C A : ℝ} (E : PEnergy m q)
    (hβ : 0 < β) (hC : 0 < C) (hvol : VolumeDoubling m) (hPI : E.Poincare E.energyMeasure β)
    (hcap : E.CapacityUpperBound β) (hunbounded : ¬ Bornology.IsBounded (univ : Set X))
    (hConn : LowerSemicontinuousConnectivity m q C A) : β = q := by
  apply le_antisymm _ (E.exponent_le_walkExponent hvol hβ E.energyMeasure_univ hPI hcap hunbounded)
  by_contra! hsuper
  let o : X := Classical.choice ‹Nonempty X›
  have hyEx : (closedBall o 4)ᶜ.Nonempty := by
    by_contra hh
    apply hunbounded
    have he : closedBall o 4 = univ := eq_univ_of_forall fun y ↦ by_contra fun hy ↦ hh ⟨y, hy⟩
    exact he ▸ (isCompact_closedBall o 4).isBounded
  obtain ⟨y, hy⟩ := hyEx
  have hy' : 4 < dist y o := lt_of_not_ge (fun h ↦ hy (mem_closedBall.mpr h))
  let d := dist o y
  have hd : 0 < d := by dsimp only [d]; rw [dist_comm]; linarith
  let τ := (2 * C * d)⁻¹
  have hτ : 0 < τ := inv_pos.mpr (by positivity)
  have hq := zero_lt_one.trans E.one_lt
  obtain ⟨K, hKT, hV⟩ := E.exists_lipschitz_plate_interpolants hβ hvol hPI o
  obtain ⟨D, hD, hVD⟩ := hvol
  let P (x : X) := ENNReal.ofReal D * (m (ball x (1 / 8)))⁻¹
  have hPT (x : X) : P x ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.inv_ne_top.mpr (measure_ball_pos m x (by norm_num : (0 : ℝ) < 1 / 8)).ne')
  have hSmall (x : X) : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      (P x * K) * ENNReal.ofReal (r ^ (β - q)) < ENNReal.ofReal (τ ^ q) := by
    have hCont : Continuous (fun r : ℝ ↦ ENNReal.ofReal (r ^ (β - q))) :=
      ENNReal.continuous_ofReal.comp (Real.continuous_rpow_const (by linarith : 0 ≤ β - q))
    have hCont' : Continuous (fun r : ℝ ↦ (P x * K) * ENNReal.ofReal (r ^ (β - q))) :=
      continuous_iff_continuousAt.mpr fun r ↦
        (ENNReal.continuousAt_const_mul (Or.inl (ENNReal.mul_ne_top (hPT x) hKT))).comp hCont.continuousAt
    have hLim := (hCont'.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    have hLim' : Tendsto (fun r : ℝ ↦ (P x * K) * ENNReal.ofReal (r ^ (β - q))) (𝓝[>] 0) (𝓝 0) := by
      simpa only [Real.zero_rpow (sub_pos.mpr hsuper).ne', ENNReal.ofReal_zero, mul_zero] using hLim
    exact hLim'.eventually_lt_const (ENNReal.ofReal_pos.mpr (by positivity))
  have hRsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioo (0 : ℝ) (1 / 8) :=
    Ioo_mem_nhdsGT (by norm_num)
  obtain ⟨r, hr, hr₁, hr₂⟩ := (hRsmall.and ((hSmall o).and (hSmall y))).exists
  obtain ⟨v, J, hv, hv₁, hv₀, hvBound⟩ := hV r hr
  let g := ballSlope v r
  have hg : LowerSemicontinuous g := lowerSemicontinuous_ballSlope hv.continuous r
  have hgz (x : X) (hx : x ∈ ball o (1 / 4) ∨ x ∈ ball y (1 / 4)) : g x ^ q = 0 := by
    suffices hh : g x = 0 by rw [hh, ENNReal.zero_rpow_of_pos hq]
    apply le_antisymm _ bot_le
    apply iSup_le
    intro z
    change ENNReal.ofReal (|v x - v z| / dist x (z : X)) ≤ 0
    have hzx : dist (z : X) x < r := z.property
    have hEq : v x = v z := by
      rcases hx with hx | hx
      · have h₁ : x ∈ ball o (1 / 2) := ball_subset_ball (by norm_num) hx
        have h₂ : (z : X) ∈ ball o (1 / 2) := mem_ball.mpr ((dist_triangle (z : X) x o).trans_lt
          (by linarith only [hzx, hr.2, mem_ball.mp hx]))
        exact (hv₁ h₁).trans (hv₁ h₂).symm
      · have h₁ : x ∉ ball o 3 := by
          intro hh
          linarith only [dist_triangle y x o, mem_ball.mp hh, mem_ball.mp hx, hy', dist_comm y x]
        have h₂ : (z : X) ∉ ball o 3 := by
          intro hh
          linarith only [dist_triangle y (z : X) o, dist_triangle y x (z : X), mem_ball.mp hh,
            mem_ball.mp hx, hy', hzx, hr.2, dist_comm y x, dist_comm x (z : X)]
        exact (hv₀ h₁).trans (hv₀ h₂).symm
    rw [hEq, sub_self, abs_zero, zero_div, ENNReal.ofReal_zero]
  have hMax (x : X) (hx : x = o ∨ x = y)
      (hrx : (P x * K) * ENNReal.ofReal (r ^ (β - q)) < ENNReal.ofReal (τ ^ q)) :
      localMaximalAverage m (fun z ↦ g z ^ q) (A * d) x ≤ ENNReal.ofReal (τ ^ q) := by
    have hzero : EqOn (fun z ↦ g z ^ q) (fun _ ↦ 0) (ball x (2 * (1 / 8))) := by
      intro z hz
      apply hgz z
      rcases hx with rfl | rfl
      · exact Or.inl (by convert hz using 1 <;> norm_num)
      · exact Or.inr (by convert hz using 1 <;> norm_num)
    have hh := localMaximalAverage_le_integral_of_zero_near hVD (fun z ↦ g z ^ q) x (by norm_num)
      hzero (A * d)
    exact hh.trans ((mul_le_mul_of_nonneg_left hvBound bot_le).trans (by rw [← mul_assoc]; exact hrx.le))
  obtain ⟨γ, _, hCost⟩ := hConn o y g hg ⟨(J : ℝ≥0∞), ENNReal.coe_ne_top,
    fun z ↦ ballSlope_le_of_lipschitzWith hv z r⟩ τ hτ (hMax o (Or.inl rfl) hr₁) (hMax y (Or.inr rfl) hr₂)
  have hLow := (γ.ofReal_abs_sub_le_cost_ballSlope hv hr.1).trans hCost
  have hvo : v o = 1 := hv₁ (mem_ball_self (by norm_num))
  have hvy : v y = 0 := hv₀ fun hyO ↦ (by linarith only [mem_ball.mp hyO, hy'] : False)
  have hτC : C * τ * d = 1 / 2 := by dsimp only [τ]; field_simp [hC.ne', hd.ne']
  rw [hvo, hvy, sub_zero, abs_one, ENNReal.ofReal_one, hτC] at hLow
  exact (not_le_of_gt (by norm_num : ENNReal.ofReal ((1 : ℝ) / 2) < 1)) hLow

end PEnergy

end WalkDimensions
