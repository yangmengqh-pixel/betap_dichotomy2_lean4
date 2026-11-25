import WalkDimensions.SeriesEnergy
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Uniform loss from a small series-energy error
-/

open Set

namespace WalkDimensions

theorem exists_series_resistance_loss {p l u ξ : ℝ}
    (hp : 1 < p) (hl : 0 < l) (hlu : l ≤ u) (hξ : 0 < ξ) :
    ∃ ε > (0 : ℝ), ∀ a ∈ Icc l u,
      a - (a ^ (1 - p) + 2 * ε) ^ (-(p - 1)⁻¹) < ξ / 2 := by
  have hq := sub_pos.mpr hp
  have hu := hl.trans_le hlu
  let A := u ^ (1 - p)
  let B := l ^ (1 - p) + 1
  let K := Icc A B
  let F (s : ℝ) := s ^ (-(p - 1)⁻¹)
  have hA : 0 < A := Real.rpow_pos_of_pos hu _
  have hF : ContinuousOn F K := continuousOn_id.rpow_const
    (fun _ hs ↦ Or.inl (hA.trans_le hs.1).ne')
  have h := isCompact_Icc.uniformContinuousOn_of_continuous hF
  obtain ⟨δ, hδ, hClose⟩ := Metric.uniformContinuousOn_iff.mp h (ξ / 2) (half_pos hξ)
  let ε := min δ 1 / 4
  have hε : 0 < ε := div_pos (lt_min hδ zero_lt_one) (by norm_num)
  refine ⟨ε, hε, fun a ha ↦ ?_⟩
  have ha₀ := hl.trans_le ha.1
  have hlo : A ≤ a ^ (1 - p) := Real.rpow_le_rpow_of_nonpos ha₀ ha.2 (sub_nonpos.mpr hp.le)
  have hhi : a ^ (1 - p) ≤ l ^ (1 - p) := Real.rpow_le_rpow_of_nonpos hl ha.1 (sub_nonpos.mpr hp.le)
  have hε₂ : 2 * ε ≤ 1 := by dsimp [ε]; linarith only [min_le_right δ (1 : ℝ)]
  have hε' : 2 * ε < δ := by dsimp [ε]; linarith only [min_le_left δ (1 : ℝ), hδ]
  have hK₁ : a ^ (1 - p) ∈ K := ⟨hlo, by dsimp [B]; linarith only [hhi]⟩
  have hK₂ : a ^ (1 - p) + 2 * ε ∈ K :=
    ⟨hlo.trans (le_add_of_nonneg_right (by positivity)), by dsimp [B]; linarith only [hhi, hε₂]⟩
  have hDist : dist (a ^ (1 - p)) (a ^ (1 - p) + 2 * ε) < δ := by
    rw [dist_comm, Real.dist_eq, add_sub_cancel_left, abs_of_nonneg (by positivity)]
    exact hε'
  have hGap := hClose _ hK₁ _ hK₂ hDist
  have hEq : F (a ^ (1 - p)) = a := by
    unfold F
    rw [← Real.rpow_mul ha₀.le, show 1 - p = -(p - 1) by ring, neg_mul_neg,
      mul_inv_cancel₀ hq.ne', Real.rpow_one]
  rw [Real.dist_eq, hEq] at hGap
  exact (le_abs_self _).trans_lt hGap

end WalkDimensions
