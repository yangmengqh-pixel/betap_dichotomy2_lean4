import WalkDimensions.OscillationDensity

/-!
# A positive-mass set with Hausdorff lower density
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal Topology

namespace WalkDimensions

variable {X : Type*} [MetricSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

omit [SecondCountableTopology X] [BorelSpace X] in
theorem exists_fine_lower_ball_mass_of_oscillation {ν : Measure X} [IsFiniteMeasure ν]
    {c p A L C θ : ℝ} (hp : 1 < p) (hA : 0 < A) (hL : 1 ≤ L)
    (hC : 0 < C) (hθ : 0 < θ) {u : X → ℝ} {W : Set X}
    (hMorrey : ∀ x r, 0 < r → ∀ y ∈ ball x r, ∀ z ∈ ball x r,
      |u y - u z| ≤ C * (ν (ball x (L * r))).toReal ^ p⁻¹ * r ^ ((p - 1) * c / p))
    (hW : ∀ x ∈ W, ∀ ε > (0 : ℝ), ∃ r ∈ Ioo (0 : ℝ) ε,
      ∃ y ∈ ball x (A * r), ∃ z ∈ ball y r, θ * r ^ c < |u y - u z|) :
    ∃ a : ℝ≥0∞, 0 < a ∧ a ≠ ∞ ∧ ∀ x ∈ W, ∀ ε > (0 : ℝ),
      ∃ s ∈ Ioo (0 : ℝ) ε, a * (ENNReal.ofReal s) ^ c ≤ ν (ball x s) := by
  let b := A + 1
  let B := L * b
  let e := (p - 1) * c / p
  have hb : 0 < b := by dsimp [b]; linarith
  have hB : 0 < B := mul_pos (zero_lt_one.trans_le hL) hb
  have hC' : 0 < C * b ^ e := mul_pos hC (Real.rpow_pos_of_pos hb _)
  let a₀ := (θ / (C * b ^ e)) ^ p / B ^ c
  have ha : 0 < a₀ := by dsimp [a₀]; positivity
  refine ⟨ENNReal.ofReal a₀, ENNReal.ofReal_pos.mpr ha, ENNReal.ofReal_ne_top, ?_⟩
  intro x hx ε hε
  obtain ⟨r, hr, y, hy, z, hz, hos⟩ := hW x hx (ε / B) (div_pos hε hB)
  have hyr : y ∈ ball x (b * r) := by
    apply mem_ball.mpr
    have h := mem_ball.mp hy
    dsimp only [b]
    nlinarith only [h, hr.1]
  have hzr : z ∈ ball x (b * r) := by
    apply mem_ball.mpr
    have h := (dist_triangle z y x).trans_lt (add_lt_add (mem_ball.mp hz) (mem_ball.mp hy))
    simpa only [b, add_mul, one_mul, add_comm] using h
  let s := B * r
  have hsr : 0 < s := mul_pos hB hr.1
  have hse : s < ε := by
    have h := (lt_div_iff₀ hB).mp hr.2
    simpa only [s, mul_comm] using h
  refine ⟨s, ⟨hsr, hse⟩, ?_⟩
  let N := (ν (ball x s)).toReal
  have hs : L * (b * r) = s := by dsimp only [s, B]; ring
  have h := hos.le.trans (hMorrey x (b * r) (mul_pos hb hr.1) y hyr z hzr)
  rw [hs, Real.mul_rpow hb.le hr.1.le] at h
  change θ * r ^ c ≤ C * N ^ p⁻¹ * (b ^ e * r ^ e) at h
  have hnorm : (θ / (C * b ^ e)) * r ^ (c - e) ≤ N ^ p⁻¹ := by
    apply le_of_mul_le_mul_right _ (mul_pos hC' (Real.rpow_pos_of_pos hr.1 e))
    calc
      (θ / (C * b ^ e)) * r ^ (c - e) * (C * b ^ e * r ^ e) = θ * r ^ c := by
        rw [Real.rpow_sub hr.1]
        field_simp [(Real.rpow_pos_of_pos hr.1 e).ne']
      _ ≤ N ^ p⁻¹ * (C * b ^ e * r ^ e) := h.trans_eq (by ring)
  have hp₀ : 0 < p := zero_lt_one.trans hp
  have hcoef := (div_pos hθ hC').le
  have hrex := Real.rpow_nonneg hr.1.le (c - e)
  have hpow := Real.rpow_le_rpow (mul_nonneg hcoef hrex) hnorm hp₀.le
  rw [Real.mul_rpow hcoef hrex,
    ← Real.rpow_mul hr.1.le, ← Real.rpow_mul ENNReal.toReal_nonneg,
    inv_mul_cancel₀ hp₀.ne', Real.rpow_one] at hpow
  have he : (c - e) * p = c := by
    dsimp only [e]
    field_simp
    ring
  rw [he] at hpow
  have hreal : a₀ * s ^ c ≤ N := by
    rw [show s = B * r from rfl, Real.mul_rpow hB.le hr.1.le]
    dsimp only [a₀]
    rw [← mul_assoc, div_mul_cancel₀ _ (Real.rpow_pos_of_pos hB c).ne']
    exact hpow
  rw [ENNReal.ofReal_rpow_of_pos hsr, ← ENNReal.ofReal_mul ha.le, ← ENNReal.ofReal_toReal (measure_ne_top ν _)]
  exact ENNReal.ofReal_le_ofReal hreal

/-- At a point of the lower-density set, arbitrarily fine mass bounds persist after restriction. -/
theorem exists_point_with_fine_mass_in_set {ν : Measure X} [IsFiniteMeasure ν] [ν.Regular]
    {c : ℝ} (hc : 0 < c) {J : ℝ≥0∞} (hν : ν ≤ J • μH[c])
    {Ω W₀ : Set X} (hΩ : MeasurableSet Ω) (hΩfull : ν Ωᶜ = 0)
    (hW₀ : MeasurableSet W₀) (hWpos : 0 < ν W₀)
    {a : ℝ≥0∞} (ha : 0 < a) (haT : a ≠ ∞)
    (hDensity : ∀ x ∈ W₀, ∀ ε > (0 : ℝ), ∃ s ∈ Ioo (0 : ℝ) ε,
      a * (ENNReal.ofReal s) ^ c ≤ ν (ball x s)) :
    ∃ (W : Set X) (x : X) (K b : ℝ≥0∞), MeasurableSet W ∧ W ⊆ Ω ∧ x ∈ W ∧
      K ≠ ∞ ∧ 0 < b ∧ (∀ S ⊆ W, μH[c] S ≤ K * ν S) ∧
      Tendsto (fun r : ℝ ↦ ν (ball x r \ W) / (ENNReal.ofReal r) ^ c) (𝓝[>] 0) (𝓝 0) ∧
      ∀ ε > (0 : ℝ), ∃ s ∈ Ioo (0 : ℝ) ε, b * (ENNReal.ofReal s) ^ c ≤ ν (ball x s ∩ W) := by
  let W := W₀ ∩ Ω
  have hW : MeasurableSet W := hW₀.inter hΩ
  have hMass : ν W = ν W₀ := by
    have hzero : ν (W₀ ∩ Ωᶜ) = 0 := measure_mono_null inter_subset_right hΩfull
    have h := measure_inter_add_sdiff W₀ hΩ (μ := ν)
    rw [sdiff_eq, hzero, add_zero] at h
    exact h
  have hνW : ν.restrict W ≠ 0 := by
    intro hh
    have h := congrArg (fun μ : Measure X ↦ μ univ) hh
    change (ν.restrict W) univ = (0 : Measure X) univ at h
    simp only [Measure.restrict_apply_univ, FunLike.coe_zero, Pi.zero_apply, hMass] at h
    exact hWpos.ne' h
  have : NeBot (ae (ν.restrict W)) := ae_neBot.mpr hνW
  obtain ⟨x, hx, ht⟩ := ((ae_restrict_mem hW).and (ae_tendsto_compl_ball_density_zero ν hc hν hW)).exists
  let K := (10 : ℝ≥0∞) ^ c * a⁻¹
  let b := a / 2
  have hb : 0 < b := ENNReal.div_pos ha.ne' (by norm_num)
  refine ⟨W, x, K, b, hW, inter_subset_right, hx,
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hc.le (by norm_num))
      (ENNReal.inv_ne_top.mpr ha.ne'), hb, ?_, ht, ?_⟩
  · intro S hSW
    apply hausdorffMeasure_le_of_fine_lower_ball_mass ν hc (ENNReal.inv_ne_top.mpr ha.ne')
    intro y hy ε hε
    obtain ⟨s, hs, h⟩ := hDensity y (hSW hy).1 ε hε
    refine ⟨s, hs, ?_⟩
    have h' := mul_le_mul_of_nonneg_left h (show 0 ≤ a⁻¹ from bot_le)
    rwa [← mul_assoc, ENNReal.inv_mul_cancel ha.ne' haT, one_mul] at h'
  · intro ε hε
    have htail : ∀ᶠ s : ℝ in 𝓝[>] 0, ν (ball x s \ W) / (ENNReal.ofReal s) ^ c < b :=
      ht.eventually_lt_const hb
    obtain ⟨δ, hδ, hδtail⟩ := (mem_nhdsGT_iff_exists_Ioo_subset.mp htail)
    obtain ⟨s, hs, hm⟩ := hDensity x hx.1 (min ε δ) (lt_min hε hδ)
    have hTs : (ENNReal.ofReal s) ^ c ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hc.le ENNReal.ofReal_ne_top
    have hPs : 0 < (ENNReal.ofReal s) ^ c :=
      ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hs.1) ENNReal.ofReal_ne_top
    have hle := (ENNReal.div_lt_iff (Or.inl hPs.ne') (Or.inl hTs)).mp
      (hδtail ⟨hs.1, hs.2.trans_le (min_le_right _ _)⟩)
    refine ⟨s, ⟨hs.1, hs.2.trans_le (min_le_left _ _)⟩, ?_⟩
    have htwo : b + b = a := by
      rw [← two_mul, mul_comm]
      dsimp only [b]
      rw [ENNReal.div_mul_cancel] <;> norm_num
    rw [← htwo, add_mul, ← measure_inter_add_sdiff (ball x s) hW] at hm
    exact (ENNReal.add_le_add_iff_right (ENNReal.mul_ne_top (ENNReal.div_ne_top haT (by norm_num)) hTs)).mp
      (hm.trans (add_le_add_right hle.le _))

end WalkDimensions
