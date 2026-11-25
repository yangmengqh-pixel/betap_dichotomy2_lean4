import WalkDimensions.SeriesEnergy
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Semicontinuity.Basic

/-!
# Uniform stability of the series minimum

On a compact positive range of series lengths, a uniformly small energy
gap forces the intermediate value close to the unique series minimizer.
-/

open Set

namespace WalkDimensions

set_option maxHeartbeats 450000 in
theorem exists_series_energy_gap {p l u : ℝ} (hp : 1 < p) (hl : 0 < l)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η > (0 : ℝ), ∀ r ∈ Icc l u, ∀ s ∈ Icc l u, ∀ t ∈ Icc (0 : ℝ) 1,
      r ^ (1 - p) * (1 - t) ^ p + s ^ (1 - p) * t ^ p - (r + s) ^ (1 - p) < η →
      |t - s / (r + s)| < ε := by
  let K : Set (ℝ × ℝ × ℝ) := Icc l u ×ˢ Icc l u ×ˢ Icc 0 1
  let A (z : ℝ × ℝ × ℝ) := |z.2.2 - z.2.1 / (z.1 + z.2.1)|
  let G (z : ℝ × ℝ × ℝ) := z.1 ^ (1 - p) * (1 - z.2.2) ^ p +
    z.2.1 ^ (1 - p) * z.2.2 ^ p - (z.1 + z.2.1) ^ (1 - p)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hpos₁ (z : ℝ × ℝ × ℝ) (hz : z ∈ K) : 0 < z.1 := hl.trans_le hz.1.1
  have hpos₂ (z : ℝ × ℝ × ℝ) (hz : z ∈ K) : 0 < z.2.1 := hl.trans_le hz.2.1.1
  have hfst : ContinuousOn (fun z : ℝ × ℝ × ℝ ↦ z.1) K := continuous_fst.continuousOn
  have hmid : ContinuousOn (fun z : ℝ × ℝ × ℝ ↦ z.2.1) K :=
    (continuous_fst.comp continuous_snd).continuousOn
  have hlast : ContinuousOn (fun z : ℝ × ℝ × ℝ ↦ z.2.2) K :=
    (continuous_snd.comp continuous_snd).continuousOn
  have hsum (z : ℝ × ℝ × ℝ) (hz : z ∈ K) : 0 < z.1 + z.2.1 := add_pos (hpos₁ z hz) (hpos₂ z hz)
  have hA : ContinuousOn A K :=
    (hlast.sub (hmid.div (hfst.add hmid) (fun z hz ↦ (hsum z hz).ne'))).abs
  have hp' := zero_lt_one.trans hp
  have hG : ContinuousOn G K :=
    (((hfst.rpow_const (fun z hz ↦ Or.inl (hpos₁ z hz).ne')).mul
      ((continuousOn_const.sub hlast).rpow_const (fun _ _ ↦ Or.inr hp'.le))).add
      ((hmid.rpow_const (fun z hz ↦ Or.inl (hpos₂ z hz).ne')).mul
        (hlast.rpow_const (fun _ _ ↦ Or.inr hp'.le)))).sub
      ((hfst.add hmid).rpow_const (fun z hz ↦ Or.inl (hsum z hz).ne'))
  let B := K ∩ A ⁻¹' Ici ε
  have hB : IsCompact B := hA.upperSemicontinuousOn.isCompact_inter_preimage_Ici hK ε
  by_cases hne : B.Nonempty
  · obtain ⟨z, hz, hmin⟩ := hB.exists_isMinOn hne (hG.mono inter_subset_left)
    have hseries := series_energy_minimum hp (hpos₁ z hz.1) (hpos₂ z hz.1) hz.1.2.2
    have hη : 0 < G z := by
      apply sub_pos.mpr
      apply lt_of_le_of_ne hseries.1
      intro h
      have he := hseries.2.mp h.symm
      have hb : ε ≤ A z := hz.2
      change ε ≤ |z.2.2 - z.2.1 / (z.1 + z.2.1)| at hb
      rw [he, sub_self, abs_zero] at hb
      exact hε.not_ge hb
    refine ⟨G z, hη, fun r hr s hs t ht hlt ↦ ?_⟩
    by_contra! hn
    have hb : (r, s, t) ∈ B := ⟨⟨hr, hs, ht⟩, hn⟩
    have hle : G z ≤ G (r, s, t) := hmin hb
    change G (r, s, t) < G z at hlt
    exact hlt.not_ge hle
  · refine ⟨1, zero_lt_one, fun r hr s hs t ht _ ↦ ?_⟩
    by_contra! hn
    have hb : (r, s, t) ∈ B := ⟨⟨hr, hs, ht⟩, hn⟩
    exact hne ⟨(r, s, t), hb⟩

end WalkDimensions
