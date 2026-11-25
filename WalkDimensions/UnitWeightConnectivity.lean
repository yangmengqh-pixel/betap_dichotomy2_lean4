import WalkDimensions.LowerSemicontinuousWeights

/-!
# Unit-bounded weights and rescaling weighted connections
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal

namespace WalkDimensions

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {m : Measure X} [IsFiniteMeasureOnCompacts m] [m.IsOpenPosMeasure]

theorem le_localMaximalAverage_of_lowerSemicontinuous {g : X → ℝ≥0∞}
    (hg : LowerSemicontinuous g) {R : ℝ} (hR : 0 < R) (x : X) :
    g x ≤ localMaximalAverage m g R x := by
  by_contra! h
  obtain ⟨a, ha, hax⟩ := exists_between h
  obtain ⟨r, hr, hSub⟩ := Metric.isOpen_iff.mp (hg.isOpen_preimage a) x hax
  let s := min r R
  have hs := lt_min hr hR
  apply ha.not_ge
  have h₀ : ∀ y ∈ ball x s, a ≤ g y := fun y hy ↦
    (show a < g y from hSub (ball_subset_ball (min_le_left _ _) hy)).le
  have hle : a ≤ ∫⁻ y, g y ∂normalizedBall m x s := by
    have hmem : ∀ᵐ y ∂normalizedBall m x s, y ∈ ball x s :=
      Measure.smul_absolutelyContinuous.ae_le (ae_restrict_mem measurableSet_ball)
    have h := lintegral_mono_ae (hmem.mono h₀)
    rwa [lintegral_const, normalizedBall_univ x hs, mul_one] at h
  exact hle.trans (average_le_localMaximalAverage g hs (min_le_right _ _) (mem_ball_self hs))

/-- Weighted timed connections for lower semicontinuous weights bounded by one. -/
def UnitWeightConnectivity (m : Measure X) (p C A : ℝ) : Prop :=
  ∀ (x y : X) (g : X → ℝ≥0∞), LowerSemicontinuous g → (∀ z, g z ≤ 1) →
    ∀ τ > (0 : ℝ),
      localMaximalAverage m (fun z ↦ g z ^ p) (A * dist x y) x ≤ ENNReal.ofReal (τ ^ p) →
      localMaximalAverage m (fun z ↦ g z ^ p) (A * dist x y) y ≤ ENNReal.ofReal (τ ^ p) →
      ∃ γ : TimedPath x y, γ.duration ≤ C * dist x y ∧
        γ.cost g ≤ ENNReal.ofReal (C * τ * dist x y)

theorem UnitWeightConnectivity.lowerSemicontinuousConnectivity {p C A : ℝ} (hp : 0 ≤ p)
    (h : UnitWeightConnectivity m p C A) : LowerSemicontinuousConnectivity m p C A := by
  intro x y g hg ⟨M, hMT, hm⟩ τ hτ hx hy
  by_cases hM₀ : M = 0
  · have h₀ : g = fun _ ↦ 0 := funext fun z ↦ le_antisymm (hM₀ ▸ hm z) bot_le
    subst g
    exact h x y _ hg (fun _ ↦ bot_le) τ hτ hx hy
  let a := M.toReal
  have ha : 0 < a := ENNReal.toReal_pos hM₀ hMT
  let u (z : X) := M⁻¹ * g z
  have hInv : M⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hM₀
  have hu : LowerSemicontinuous u := by
    have hCont : Continuous (fun t : ℝ≥0∞ ↦ M⁻¹ * t) :=
      continuous_iff_continuousAt.mpr fun _ ↦ ENNReal.continuousAt_const_mul (Or.inl hInv)
    exact hCont.comp_lowerSemicontinuous hg (fun _ _ hle ↦ mul_le_mul_of_nonneg_left hle bot_le)
  have hu₁ (z : X) : u z ≤ 1 :=
    (mul_le_mul_of_nonneg_left (hm z) bot_le).trans_eq (ENNReal.inv_mul_cancel hM₀ hMT)
  have hMax (z : X) (hz : localMaximalAverage m (fun z ↦ g z ^ p) (A * dist x y) z ≤ ENNReal.ofReal (τ ^ p)) :
      localMaximalAverage m (fun z ↦ u z ^ p) (A * dist x y) z ≤ ENNReal.ofReal ((τ / a) ^ p) := by
    apply iSup_le
    intro v
    apply iSup_le
    intro s
    apply iSup_le
    intro hs
    apply iSup_le
    intro hv
    simp_rw [u, ENNReal.mul_rpow_of_nonneg _ _ hp]
    rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp hInv)]
    apply (mul_le_mul_of_nonneg_left ((average_le_localMaximalAverage
      (fun w ↦ g w ^ p) hs.1 hs.2 hv).trans hz) bot_le).trans_eq
    rw [← ENNReal.ofReal_toReal hMT, ← ENNReal.ofReal_inv_of_pos ha,
      ENNReal.ofReal_rpow_of_pos (inv_pos.mpr ha), ← ENNReal.ofReal_mul (by positivity),
      div_eq_mul_inv, Real.mul_rpow hτ.le (inv_nonneg.mpr ha.le), mul_comm]
  obtain ⟨γ, hT, hCost⟩ := h x y u hu hu₁ (τ / a) (div_pos hτ ha) (hMax x hx) (hMax y hy)
  have hCost' : γ.cost g = M * γ.cost u := by
    unfold TimedPath.cost
    rw [← lintegral_const_mul' _ _ hMT]
    congr 1
    funext t
    change g (γ.toFun t) = M * (M⁻¹ * g (γ.toFun t))
    rw [← mul_assoc, ENNReal.mul_inv_cancel hM₀ hMT, one_mul]
  refine ⟨γ, hT, ?_⟩
  rw [hCost']
  apply (mul_le_mul_of_nonneg_left hCost bot_le).trans_eq
  rw [← ENNReal.ofReal_toReal hMT, ← ENNReal.ofReal_mul ha.le]
  congr 1
  field_simp [ha.ne']

end WalkDimensions
