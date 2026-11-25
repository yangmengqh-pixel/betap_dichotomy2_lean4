import WalkDimensions.TimedPaths
import WalkDimensions.PointwiseSlope

/-!
# The cost of a least expensive timed connection
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal NNReal Topology

namespace WalkDimensions

variable {X : Type*} [MetricSpace X]

/-- The infimal cost among timed paths between two endpoints. -/
noncomputable def weightedDistance (g : X → ℝ≥0∞) (x y : X) : ℝ≥0∞ :=
  ⨅ γ : TimedPath x y, γ.cost g

theorem weightedDistance_le_cost (g : X → ℝ≥0∞) {x y : X} (γ : TimedPath x y) :
    weightedDistance g x y ≤ γ.cost g :=
  iInf_le _ γ

@[simp] theorem weightedDistance_self (g : X → ℝ≥0∞) (x : X) :
    weightedDistance g x x = 0 := by
  exact le_antisymm ((weightedDistance_le_cost g (TimedPath.refl x)).trans_eq (by simp [TimedPath.cost])) bot_le

theorem weightedDistance_triangle (g : X → ℝ≥0∞) (x y z : X)
    [Nonempty (TimedPath x y)] [Nonempty (TimedPath y z)] :
    weightedDistance g x z ≤ weightedDistance g x y + weightedDistance g y z := by
  unfold weightedDistance
  rw [ENNReal.iInf_add]
  apply le_iInf
  intro γ
  rw [ENNReal.add_iInf]
  apply le_iInf
  intro η
  rw [← TimedPath.cost_append]
  exact iInf_le _ (γ.append η)

variable [ProperSpace X]

/-- The local slope of the weighted-distance potential is controlled by its weight. -/
theorem ChainCondition.exists_weightedDistanceSlope (hCC : ChainCondition X) :
    ∃ L > (0 : ℝ), ∀ (g : X → ℝ) {M : ℝ}, Continuous g → (∀ v, g v ∈ Icc 0 M) → ∀ x : X,
      (∀ y, weightedDistance (fun z ↦ ENNReal.ofReal (g z)) x y ≠ ∞) ∧
      (∃ K : ℝ≥0, LipschitzWith K (fun y ↦ (weightedDistance (fun z ↦ ENNReal.ofReal (g z)) x y).toReal)) ∧
      ∀ y, pointwiseSlope (fun v ↦ (weightedDistance (fun z ↦ ENNReal.ofReal (g z)) x v).toReal) y ≤
        ENNReal.ofReal (L * g y) := by
  obtain ⟨L, hL, hIntrinsic⟩ := hCC.exists_intrinsicDistance_le
  refine ⟨L, hL, fun g M hg hM x ↦ ?_⟩
  let G (z : X) := ENNReal.ofReal (g z)
  let u (v : X) := (weightedDistance G x v).toReal
  have hM₀ : 0 ≤ M := (hM x).1.trans (hM x).2
  have hBid (v w : X) : weightedDistance G v w ≤ ENNReal.ofReal (L * M * dist v w) := by
    obtain ⟨γ, hγ⟩ := hCC.exists_timedPath v w
    have h := (weightedDistance_le_cost G γ).trans
      (γ.cost_le_const (M := ENNReal.ofReal M) fun z _ ↦ ENNReal.ofReal_le_ofReal (hM _).2)
    refine h.trans ?_
    rw [← ENNReal.ofReal_mul hM₀]
    apply ENNReal.ofReal_le_ofReal
    rw [hγ]
    have h' := mul_le_mul_of_nonneg_left (hIntrinsic v w) hM₀
    simpa only [mul_left_comm M, mul_assoc] using h'
  have hfin (v w : X) : weightedDistance G v w ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hBid v w)
  have : ∀ v w : X, Nonempty (TimedPath v w) := fun v w ↦ ⟨(hCC.exists_timedPath v w).choose⟩
  have hInc (v w : X) : u w ≤ u v + (weightedDistance G v w).toReal := by
    have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin x v, hfin v w⟩)
      (weightedDistance_triangle G x v w)
    rwa [ENNReal.toReal_add (hfin x v) (hfin v w)] at h
  have hAbs (v w : X) {a : ℝ} (ha : 0 ≤ a)
      (hv : weightedDistance G v w ≤ ENNReal.ofReal a)
      (hw : weightedDistance G w v ≤ ENNReal.ofReal a) : |u v - u w| ≤ a := by
    have ha₁ := ENNReal.toReal_mono ENNReal.ofReal_ne_top hv
    have ha₂ := ENNReal.toReal_mono ENNReal.ofReal_ne_top hw
    rw [ENNReal.toReal_ofReal ha] at ha₁ ha₂
    exact abs_le.mpr ⟨by linarith only [hInc v w, ha₁], by linarith only [hInc w v, ha₂]⟩
  refine ⟨hfin x, ⟨⟨L * M, mul_nonneg hL.le hM₀⟩, LipschitzWith.of_dist_le_mul (fun v w ↦ ?_)⟩,
    fun y ↦ ?_⟩
  · rw [Real.dist_eq]
    apply hAbs v w (by positivity) (hBid v w)
    rw [dist_comm]
    exact hBid w v
  have hNear (e : ℝ) (he : 0 < e) :
      pointwiseSlope u y ≤ ENNReal.ofReal (L * (g y + e)) := by
    obtain ⟨δ, hδ, hBound⟩ := Metric.continuousAt_iff.mp hg.continuousAt e he
    have hden : 0 < L + 1 := by positivity
    obtain ⟨n, hn⟩ := exists_nat_gt ((L + 1) / δ)
    let s := 1 / ((n : ℝ) + 1)
    have hs : 0 < s := by dsimp only [s]; positivity
    have hsδ : (L + 1) * s < δ := by
      dsimp only [s]
      rw [mul_one_div, div_lt_iff₀ (by positivity)]
      have h := (div_lt_iff₀ hδ).mp hn
      nlinarith only [h, hδ]
    have hCost (v w : X) (hv : dist v y ≤ dist v w) (hw : dist v w < s) :
        weightedDistance G v w ≤ ENNReal.ofReal (L * (g y + e) * dist v w) := by
      obtain ⟨γ, hγ⟩ := hCC.exists_timedPath v w
      have hClose (t : ℝ) (ht : t ∈ Ioc 0 γ.duration) : dist (γ.toFun t) y < δ := by
        have h₁ := (dist_triangle (γ.toFun t) v y).trans
          (add_le_add (γ.dist_source_le_of_mem ⟨ht.1.le, ht.2⟩) hv)
        have h₂ := hγ ▸ hIntrinsic v w
        have h₃ : dist (γ.toFun t) y ≤ (L + 1) * dist v w := by linarith only [h₁, h₂, ht.2]
        exact h₃.trans_lt ((mul_lt_mul_of_pos_left hw hden).trans hsδ)
      have h := (weightedDistance_le_cost G γ).trans
        (γ.cost_le_const (M := ENNReal.ofReal (g y + e)) fun t ht ↦ by
          apply ENNReal.ofReal_le_ofReal
          have hb := hBound (hClose t ht)
          rw [Real.dist_eq] at hb
          linarith only [(abs_lt.mp hb).2])
      have hge : 0 ≤ g y + e := add_nonneg (hM y).1 he.le
      refine h.trans ?_
      rw [← ENNReal.ofReal_mul hge]
      apply ENNReal.ofReal_le_ofReal
      rw [hγ]
      calc
        _ ≤ (g y + e) * (L * dist v w) := mul_le_mul_of_nonneg_left (hIntrinsic v w) hge
        _ = _ := by ring
    apply iInf_le_of_le n
    apply iSup_le
    intro v
    change ENNReal.ofReal (|u y - u v| / dist y (v : X)) ≤ _
    by_cases hv : y = (v : X)
    · simp only [hv, sub_self, abs_zero, zero_div, ENNReal.ofReal_zero]
      exact bot_le
    have hdy : 0 < dist y (v : X) := dist_pos.mpr hv
    have hvb : dist (v : X) y < s := mem_ball.mp v.property
    have h₁ := hCost y v (by rw [dist_self]; exact dist_nonneg)
      (by rw [dist_comm]; exact hvb)
    have h₂ := hCost v y le_rfl hvb
    rw [dist_comm (v : X) y] at h₂
    apply ENNReal.ofReal_le_ofReal
    apply (div_le_iff₀ hdy).mpr
    exact hAbs y v (mul_nonneg (mul_nonneg hL.le (add_nonneg (hM y).1 he.le)) hdy.le) h₁ h₂
  have hlim : Tendsto (fun e : ℝ ↦ ENNReal.ofReal (L * (g y + e))) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal (L * g y))) := by
    have h : Continuous (fun e : ℝ ↦ ENNReal.ofReal (L * (g y + e))) :=
      ENNReal.continuous_ofReal.comp (continuous_const.mul (continuous_const.add continuous_id))
    have h₀ := (h.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    change Tendsto _ _ (𝓝 (ENNReal.ofReal (L * (g y + 0)))) at h₀
    rwa [add_zero] at h₀
  exact ge_of_tendsto hlim (eventually_mem_nhdsWithin.mono hNear)

end WalkDimensions
