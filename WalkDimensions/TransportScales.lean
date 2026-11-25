import WalkDimensions.SnowflakeTransport
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Choosing the approximation and link scales in the transport inequality
-/

open Filter Set
open scoped Topology

namespace WalkDimensions

theorem exists_pos_mul_rpow_lt {K c b t : ℝ} (hc : 0 < c) (hb : 0 < b) (ht : 0 < t) :
    ∃ s ∈ Ioo (0 : ℝ) t, K * s ^ c < b := by
  have h : Tendsto (fun s : ℝ ↦ K * s ^ c) (𝓝 0) (𝓝 0) := by
    have h := (Real.continuousAt_rpow_const 0 c (Or.inr hc.le)).tendsto.const_mul K
    simpa only [Real.zero_rpow hc.ne', mul_zero] using h
  have ht' : ∀ᶠ s : ℝ in 𝓝[>] 0, s ∈ Ioo 0 t := Ioo_mem_nhdsGT ht
  exact (ht'.and ((h.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))).eventually_lt_const hb)).exists

theorem exists_transport_scales {c H D K b : ℝ} (hc : 0 < c) (hc₁ : c < 1)
    (hb : 0 < b) :
    ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧
      (H * ε ^ c) * D + (H * ε ^ (c - 1) * δ ^ (1 - c)) * K < b := by
  obtain ⟨ε, hε, hεD⟩ := exists_pos_mul_rpow_lt (K := H * D) hc (half_pos hb) zero_lt_one
  obtain ⟨δ, hδ, hδK⟩ := exists_pos_mul_rpow_lt (K := H * ε ^ (c - 1) * K)
    (sub_pos.mpr hc₁) (half_pos hb) zero_lt_one
  refine ⟨ε, δ, hε.1, hδ.1, ?_⟩
  calc
    _ = (H * D) * ε ^ c + (H * ε ^ (c - 1) * K) * δ ^ (1 - c) := by ring
    _ < _ := by linarith only [hεD, hδK]

end WalkDimensions
