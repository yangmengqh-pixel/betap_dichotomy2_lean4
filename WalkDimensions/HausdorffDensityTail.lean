import WalkDimensions.HausdorffDensity

/-!
# Density of the complement in a Hausdorff-dominated measure
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal Topology

namespace WalkDimensions

variable {X : Type*} [MetricSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

theorem ae_tendsto_compl_ball_density_zero (ν : Measure X) [ν.Regular] [IsFiniteMeasure ν]
    {c : ℝ} (hc : 0 < c) {J : ℝ≥0∞} (hν : ν ≤ J • μH[c])
    {W : Set X} (hW : MeasurableSet W) :
    ∀ᵐ x ∂ν.restrict W,
      Tendsto (fun r : ℝ ↦ ν (ball x r \ W) / (ENNReal.ofReal r) ^ c) (𝓝[>] 0) (𝓝 0) := by
  let m := ν.restrict Wᶜ
  have hmReg : m.Regular := Measure.Regular.restrict_of_measure_ne_top (measure_ne_top ν Wᶜ)
  let ε (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp only [ε]; positivity
  let a (n : ℕ) := ENNReal.ofReal (ε n)
  have ha₀ (n : ℕ) : a n ≠ 0 := (ENNReal.ofReal_pos.mpr (hε n)).ne'
  have haT (n : ℕ) : a n ≠ ∞ := ENNReal.ofReal_ne_top
  let Bad (n : ℕ) := {x ∈ W | ∀ δ > (0 : ℝ), ∃ r ∈ Ioo (0 : ℝ) δ,
    a n * (ENNReal.ofReal r) ^ c ≤ m (ball x r)}
  have hBad (n : ℕ) : ν (Bad n) = 0 := by
    have hnull : m (Bad n) = 0 := by
      apply measure_mono_null (show Bad n ⊆ W from fun _ hx ↦ hx.1)
      rw [Measure.restrict_apply hW, inter_compl_self, measure_empty]
    have hd : μH[c] (Bad n) ≤ (((10 : ℝ≥0∞) ^ c) * (a n)⁻¹) * m (Bad n) := by
      apply hausdorffMeasure_le_of_fine_lower_ball_mass m hc
        (ENNReal.inv_ne_top.mpr (ha₀ n))
      intro x hx δ hδ
      obtain ⟨r, hr, hm⟩ := hx.2 δ hδ
      refine ⟨r, hr, ?_⟩
      have h := mul_le_mul_of_nonneg_left hm (show 0 ≤ (a n)⁻¹ from bot_le)
      rwa [← mul_assoc, ENNReal.inv_mul_cancel (ha₀ n) (haT n), one_mul] at h
    have hd₀ : μH[c] (Bad n) = 0 := le_antisymm (by simpa only [hnull, mul_zero] using hd) bot_le
    exact le_antisymm ((hν (Bad n)).trans_eq (by rw [smul_apply, smul_eq_mul, hd₀, mul_zero])) bot_le
  have hnAE : ∀ᵐ x ∂ν, ∀ n, x ∉ Bad n :=
    ae_all_iff.mpr fun n ↦ ae_iff.2 (by simpa using hBad n)
  filter_upwards [ae_restrict_of_ae hnAE, ae_restrict_mem hW] with x hx hxW
  have hlim : Tendsto a atTop (𝓝 0) := by
    simpa only [a, ε, ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal
      tendsto_one_div_add_atTop_nhds_zero_nat
  apply tendsto_order.2
  refine ⟨fun z hz ↦ (not_lt_of_ge bot_le hz).elim, fun b hb ↦ ?_⟩
  obtain ⟨n, hn⟩ := (hlim.eventually_lt_const hb).exists
  have hNo : ¬∀ δ > (0 : ℝ), ∃ r ∈ Ioo (0 : ℝ) δ,
      a n * (ENNReal.ofReal r) ^ c ≤ m (ball x r) := fun h ↦ hx n ⟨hxW, h⟩
  push Not at hNo
  obtain ⟨δ, hδ, hδb⟩ := hNo
  filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
  have hp := ENNReal.rpow_pos (p := c) (ENNReal.ofReal_pos.mpr hr.1) ENNReal.ofReal_ne_top
  have hpt : (ENNReal.ofReal r) ^ c ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg hc.le ENNReal.ofReal_ne_top
  have hball : m (ball x r) = ν (ball x r \ W) := Measure.restrict_apply measurableSet_ball
  rw [← hball]
  apply lt_trans _ hn
  exact (ENNReal.div_lt_iff (Or.inl hp.ne') (Or.inl hpt)).mpr (hδb r hr)

end WalkDimensions
