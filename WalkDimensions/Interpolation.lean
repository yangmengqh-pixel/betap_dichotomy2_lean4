import WalkDimensions.Besov
import WalkDimensions.Exponents
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.ContinuousMap.CompactlySupported

/-!
# Small-scale interpolation

The limiting estimate in Lemma 5.1 and the small-scale estimate in
Lemma 5.2 of arXiv:2611.02422v1.
-/

open Filter MeasureTheory Metric Set
open scoped ENNReal Topology

namespace WalkDimensions

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}

/-- A compactly supported continuous function with bounded (p)-moments
has vanishing (q)-energy at the same scaling exponent when (p<q). -/
theorem tendsto_besovEnergy_zero_of_bounded_same_scale {p q β : ℝ}
    (hp : 0 ≤ p) (hpq : p < q) {u : X → ℝ} (hu : Continuous u) (hc : HasCompactSupport u)
    {M : ℝ≥0∞} (hM : M ≠ ∞)
    (hbound : ∀ᶠ r in 𝓝[>] (0 : ℝ), besovEnergy m p β univ u r ≤ M) :
    Tendsto (besovEnergy m q β univ u) (𝓝[>] 0) (𝓝 0) := by
  have huc : UniformContinuous u :=
    hu.uniformContinuous_of_tendsto_cocompact hc.is_zero_at_infty
  have hlim : Tendsto (fun ε : ℝ ↦ M * (ENNReal.ofReal ε) ^ (q - p)) (𝓝 0) (𝓝 0) := by
    apply (ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hM (sub_pos.mpr hpq)).comp
    simpa only [ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.tendsto 0
  refine tendsto_order.2 ⟨fun a ha ↦ (not_lt_of_ge (bot_le : (0 : ℝ≥0∞) ≤ a) ha).elim, fun a ha ↦ ?_⟩
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), M * (ENNReal.ofReal ε) ^ (q - p) < a :=
    ((tendsto_order.1 hlim).2 a ha).filter_mono nhdsWithin_le_nhds
  obtain ⟨ε, hε, hεa⟩ := (eventually_mem_nhdsWithin.and hsmall).exists
  obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuous_iff.1 huc ε hε
  filter_upwards [hbound, Ioo_mem_nhdsGT hδ] with r hr hrad
  have hinc : ∀ x y, dist y x < r → |u x - u y| ≤ ε := by
    intro x y hxy
    have h := hδu (a := y) (b := x) (hxy.trans hrad.2)
    simpa only [Real.dist_eq, abs_sub_comm] using h.le
  have h := besovEnergy_le_of_increment_bound (m := m) (βp := β) (βq := β)
    hp hpq.le hrad.1 univ hinc
  rw [sub_self, ENNReal.rpow_zero, one_mul] at h
  rw [mul_comm M] at hεa
  exact (h.trans (mul_le_mul_of_nonneg_left hr bot_le)).trans_lt hεa


omit [BorelSpace X] in
/-- A finite bound at a strictly higher scaling exponent forces the
energy at the lower scaling exponent to vanish. -/
theorem tendsto_besovEnergy_zero_of_higher_scale {p β b : ℝ} (hβ : β < b)
    {u : X → ℝ} {M : ℝ≥0∞} (hM : M ≠ ∞)
    (hbound : ∀ᶠ r in 𝓝[>] (0 : ℝ), besovEnergy m p b univ u r ≤ M) :
    Tendsto (besovEnergy m p β univ u) (𝓝[>] 0) (𝓝 0) := by
  have hlim : Tendsto (fun r : ℝ ↦ M * (ENNReal.ofReal r) ^ (b - β)) (𝓝[>] 0) (𝓝 0) := by
    have hlim₀ : Tendsto (fun r : ℝ ↦ M * (ENNReal.ofReal r) ^ (b - β)) (𝓝 0) (𝓝 0) := by
      apply (ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hM (sub_pos.mpr hβ)).comp
      simpa only [ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.tendsto 0
    exact hlim₀.mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun _ : ℝ ↦ (0 : ℝ≥0∞))    tendsto_const_nhds hlim (Eventually.of_forall fun _ ↦ bot_le) ?_
  filter_upwards [hbound, eventually_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0)] with r hB hr
  have hr' : 0 < r := hr
  have hscale : besovEnergy m p β univ u r =
      (ENNReal.ofReal r) ^ (b - β) * besovEnergy m p b univ u r := by
    unfold besovEnergy
    rw [← mul_assoc, ← ENNReal.rpow_add _ _ (ENNReal.ofReal_ne_zero_iff.mpr hr') ENNReal.ofReal_ne_top,
      show b - β + -b = -β by ring]
  rw [hscale, mul_comm M]
  exact mul_le_mul_of_nonneg_left hB bot_le

/-- At the endpoint of Lemma 5.2, the scale factors cancel. -/
theorem besovEnergy_le_of_holder {p q β c K r : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q)
    (hc : 0 ≤ c) (hK : 0 ≤ K) (hr : 0 < r) {u : X → ℝ} (U : Set X)
    (hholder : ∀ x y, |u x - u y| ≤ K * dist x y ^ c) :
    besovEnergy m q (β + (q - p) * c) U u r ≤
      (ENNReal.ofReal K) ^ (q - p) * besovEnergy m p β U u r := by
  have hinc : ∀ x y, dist y x < r → |u x - u y| ≤ K * r ^ c := by
    intro x y hxy
    exact (hholder x y).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow dist_nonneg (by simpa only [dist_comm] using hxy.le) hc) hK)
  have h := besovEnergy_le_of_increment_bound (m := m) (βp := β)
    (βq := β + (q - p) * c) hp hpq hr U hinc
  have hq : 0 ≤ q - p := sub_nonneg.mpr hpq
  have hscale : β - (β + (q - p) * c) + c * (q - p) = 0 := by ring
  calc
    _ ≤ _ := h
    _ = _ := by
      rw [ENNReal.ofReal_mul hK, ← ENNReal.ofReal_rpow_of_nonneg hr.le hc,
        ENNReal.mul_rpow_of_nonneg _ _ hq, ← ENNReal.rpow_mul]
      calc
        _ = ((ENNReal.ofReal r) ^ (β - (β + (q - p) * c)) *
            (ENNReal.ofReal r) ^ (c * (q - p))) *
            ((ENNReal.ofReal K) ^ (q - p) * besovEnergy m p β U u r) := by ac_rfl
        _ = _ := by
          rw [← ENNReal.rpow_add _ _ (ENNReal.ofReal_ne_zero_iff.2 hr) ENNReal.ofReal_ne_top,
            hscale, ENNReal.rpow_zero, one_mul]

theorem gamma_interpolation_exponent {d p q : ℝ} {β : ℝ → ℝ} (hp : 1 < p) :
    β p + (q - p) * gamma d β p = (q - 1) * gamma d β p + d := by
  have he : (p - 1) * gamma d β p = β p - d := by
    rw [gamma, mul_comm, div_mul_cancel₀ _ (sub_pos.mpr hp).ne']
  linarith only [he]

end WalkDimensions
