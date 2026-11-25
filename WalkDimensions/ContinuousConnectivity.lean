import WalkDimensions.PointwiseSlopePoincare
import WalkDimensions.WeightedDistance

/-!
# Finite-cost paths from the first-order Poincaré estimate
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal NNReal

namespace WalkDimensions

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SecondCountableTopology X] {m : Measure X}
  [m.Regular] [SFinite m] [m.IsOpenPosMeasure]

/-- Weighted connections with controlled duration and cost, for continuous bounded weights. -/
def ContinuousConnectivity (m : Measure X) (p C A : ℝ) : Prop :=
  ∀ (x y : X) (g : X → ℝ≥0∞), Continuous g → (∃ M ≠ ∞, ∀ z, g z ≤ M) →
    ∀ τ > (0 : ℝ),
      localMaximalAverage m (fun z ↦ g z ^ p) (A * dist x y) x ≤ ENNReal.ofReal (τ ^ p) →
      localMaximalAverage m (fun z ↦ g z ^ p) (A * dist x y) y ≤ ENNReal.ofReal (τ ^ p) →
      ∃ γ : TimedPath x y, γ.duration ≤ C * dist x y ∧
        γ.cost g ≤ ENNReal.ofReal (C * τ * dist x y)

theorem SlopePoincare.exists_continuousConnectivity {p : ℝ}
    (hp : 1 ≤ p) (hvol : VolumeDoubling m) (hCC : ChainCondition X) (hP : SlopePoincare m p) :
    ∃ C A : ℝ, 0 < C ∧ 1 ≤ A ∧ ContinuousConnectivity m p C A := by
  obtain ⟨K, A, hK, hA, hPt⟩ := hP.exists_pointwise_bound hp hvol
  obtain ⟨L, hL, hSlope⟩ := hCC.exists_weightedDistanceSlope
  have hp₀ := zero_lt_one.trans_le hp
  let C := 8 * K * L + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, A, hC, hA, ?_⟩
  intro x y g hg hgb τ hτ hx hy
  by_cases hxy : x = y
  · subst y
    exact ⟨TimedPath.refl x, by simp, by simp [TimedPath.cost]⟩
  obtain ⟨M, hM, hgM⟩ := hgb
  have hfin (z : X) : g z ≠ ∞ := ne_top_of_le_ne_top hM (hgM z)
  let w (z : X) := (g z).toReal + τ
  have hCont : Continuous (fun z ↦ (g z).toReal) :=
    continuous_iff_continuousAt.mpr fun z ↦ (ENNReal.continuousAt_toReal (hfin z)).comp hg.continuousAt
  have hw : Continuous w := hCont.add continuous_const
  have hwM (z : X) : w z ∈ Icc 0 (M.toReal + τ) :=
    ⟨add_nonneg ENNReal.toReal_nonneg hτ.le, add_le_add_left (ENNReal.toReal_mono hM (hgM z)) _⟩
  let W (z : X) := ENNReal.ofReal (w z)
  have hW (z : X) : W z = g z + ENNReal.ofReal τ := by
    dsimp only [W, w]
    rw [ENNReal.ofReal_add ENNReal.toReal_nonneg hτ.le, ENNReal.ofReal_toReal (hfin z)]
  let u (z : X) := (weightedDistance W x z).toReal
  obtain ⟨huT, ⟨J, hu⟩, hSlopeU⟩ := hSlope w hw hwM x
  let r := dist x y
  have hr : 0 < r := dist_pos.mpr hxy
  have hMax (v : X) (hv : localMaximalAverage m (fun z ↦ g z ^ p) (A * r) v ≤ ENNReal.ofReal (τ ^ p)) :
      (localMaximalAverage m (fun z ↦ pointwiseSlope u z ^ p) (A * r) v).toReal ^ p⁻¹ ≤ 4 * L * τ := by
    let B := ENNReal.ofReal ((4 * L * τ) ^ p)
    have hB : localMaximalAverage m (fun z ↦ pointwiseSlope u z ^ p) (A * r) v ≤ B := by
      apply iSup_le
      intro z
      apply iSup_le
      intro s
      apply iSup_le
      intro hs
      apply iSup_le
      intro hz
      let ν := normalizedBall m z s
      have hν : ν univ = 1 := normalizedBall_univ z hs.1
      let F := ENNReal.ofReal ((2 * L) ^ p)
      have hpow (b : X) : pointwiseSlope u b ^ p ≤ F * (g b ^ p + ENNReal.ofReal (τ ^ p)) := by
        refine (ENNReal.rpow_le_rpow (hSlopeU b) hp₀.le).trans ?_
        have h₂ : L * w b ≤ (2 * L) * max (g b).toReal τ := by
          dsimp only [w]
          nlinarith only [mul_le_mul_of_nonneg_left (le_max_left (g b).toReal τ) hL.le,
            mul_le_mul_of_nonneg_left (le_max_right (g b).toReal τ) hL.le]
        calc
          _ ≤ ENNReal.ofReal ((2 * L) * max (g b).toReal τ) ^ p :=
            ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal h₂) hp₀.le
          _ = F * (max (g b) (ENNReal.ofReal τ)) ^ p := by
            rw [ENNReal.ofReal_mul (by positivity), ENNReal.mul_rpow_of_nonneg _ _ hp₀.le,
              ENNReal.ofReal_rpow_of_pos (by positivity), ENNReal.ofReal_max,
              ENNReal.ofReal_toReal (hfin b)]
          _ ≤ _ := by
            rw [← ENNReal.ofReal_rpow_of_pos hτ]
            apply mul_le_mul_of_nonneg_left _ bot_le
            rcases le_total (g b) (ENNReal.ofReal τ) with hle | hle
            · rw [max_eq_right hle]
              exact le_add_left le_rfl
            · rw [max_eq_left hle]
              exact le_add_right le_rfl
      calc
        _ ≤ ∫⁻ b, F * (g b ^ p + ENNReal.ofReal (τ ^ p)) ∂ν := lintegral_mono hpow
        _ = F * ((∫⁻ b, g b ^ p ∂ν) + ENNReal.ofReal (τ ^ p)) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_right _ measurable_const,
            lintegral_const, hν, mul_one]
        _ ≤ F * (ENNReal.ofReal (τ ^ p) + ENNReal.ofReal (τ ^ p)) :=
          mul_le_mul_of_nonneg_left (add_le_add_left
            ((average_le_localMaximalAverage (fun z ↦ g z ^ p) hs.1 hs.2 hz).trans hv) _) bot_le
        _ ≤ B := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          have hLp : 0 < 2 * L := by positivity
          have h₂ : (2 : ℝ) ≤ (2 : ℝ) ^ p := by
            simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hp
          calc
            _ ≤ (2 * L) ^ p * ((2 : ℝ) ^ p * τ ^ p) := by
              rw [← two_mul]
              gcongr
            _ = (4 * L * τ) ^ p := by
              rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hτ.le,
                ← Real.mul_rpow hLp.le (by positivity)]
              congr 1
              ring
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hB
    rw [ENNReal.toReal_ofReal (by positivity)] at hh
    have hh' := Real.rpow_le_rpow ENNReal.toReal_nonneg hh (inv_nonneg.mpr hp₀.le)
    rw [← Real.rpow_mul (by positivity), mul_inv_cancel₀ hp₀.ne', Real.rpow_one] at hh'
    exact hh'
  have huy : u y ≤ (8 * K * L) * τ * r := by
    have h := hPt u hu x y
    have hux : u x = 0 := by simp [u]
    rw [hux, zero_sub, abs_neg, abs_of_nonneg ENNReal.toReal_nonneg] at h
    exact h.trans ((mul_le_mul_of_nonneg_left (add_le_add (hMax x hx) (hMax y hy))
      (by positivity)).trans_eq (by ring))
  have hlt : weightedDistance W x y < ENNReal.ofReal (C * τ * r) := by
    rw [← ENNReal.ofReal_toReal (huT y)]
    apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
    exact huy.trans_lt (by dsimp only [C]; nlinarith only [mul_pos hτ hr])
  obtain ⟨γ, hγ⟩ := iInf_lt_iff.mp hlt
  have hWlow : ENNReal.ofReal (τ * γ.duration) ≤ γ.cost W := by
    calc
      _ = ∫⁻ t in Ioc 0 γ.duration, ENNReal.ofReal τ ∂volume := by
        rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ENNReal.ofReal_mul hτ.le]
      _ ≤ γ.cost W := by
        apply setLIntegral_mono' measurableSet_Ioc
        intro t _
        change ENNReal.ofReal τ ≤ W (γ.toFun t)
        rw [hW]
        exact le_add_left le_rfl
  have hTime := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp (hWlow.trans hγ.le)
  refine ⟨γ, by nlinarith only [hTime, hτ, mul_pos hτ hr], ?_⟩
  apply (lintegral_mono fun t ↦ ?_).trans hγ.le
  change g (γ.toFun t) ≤ W (γ.toFun t)
  rw [hW]
  exact le_add_right le_rfl

end WalkDimensions
