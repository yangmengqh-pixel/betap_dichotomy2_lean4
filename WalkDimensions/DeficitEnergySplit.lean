import WalkDimensions.SeriesStability
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Energy of the upper branch near series equality
-/

open Metric Set

namespace WalkDimensions

theorem exists_normalized_upper_energy_bound {p l u ε : ℝ}
    (hp : 1 < p) (hl : 0 < l) (hlu : l ≤ u) (hε : 0 < ε) :
    ∃ η > (0 : ℝ), ∀ {r s t ell H L : ℝ},
      r ∈ Icc l u → s ∈ Icc l u → t ∈ Icc l u → ell ∈ Icc (0 : ℝ) 1 →
      t ≤ r + s → r + s - t ≤ η →
      r ^ (1 - p) * (1 - ell) ^ p ≤ H → s ^ (1 - p) * ell ^ p ≤ L →
      H + L ≤ t ^ (1 - p) + η →
      ell < 1 ∧ H / (1 - ell) ^ p ≤ r ^ (1 - p) + ε := by
  have hu := hl.trans_le hlu
  have hp' := zero_lt_one.trans hp
  let m := l / (4 * u)
  have hm : 0 < m := div_pos hl (by positivity)
  obtain ⟨δ, hδ, hgap⟩ := exists_series_energy_gap hp hl hm
  let σ := min δ (ε * m ^ p) / 4
  have hσ : 0 < σ := div_pos (lt_min hδ (mul_pos hε (Real.rpow_pos_of_pos hm _))) (by norm_num)
  let K := Icc l (2 * u)
  have hc : ContinuousOn (fun v : ℝ ↦ v ^ (1 - p)) K := continuousOn_id.rpow_const
    (fun x hx ↦ Or.inl (hl.trans_le hx.1).ne')
  have hUC := isCompact_Icc.uniformContinuousOn_of_continuous hc
  obtain ⟨ζ, hζ, hclose⟩ := Metric.uniformContinuousOn_iff.mp hUC σ hσ
  let η := min σ (ζ / 2)
  have hη : 0 < η := lt_min hσ (half_pos hζ)
  refine ⟨η, hη, fun {r s t ell H L} hr hs ht hell htri hDef hH hL hsum ↦ ?_⟩
  have hKU : r + s ∈ K := ⟨hr.1.trans (le_add_of_nonneg_right (hl.trans_le hs.1).le), by
    linarith only [hr.2, hs.2]⟩
  have hKT : t ∈ K := ⟨ht.1, by linarith only [ht.2, hu]⟩
  have hd : dist (r + s) t < ζ := by
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr htri)]
    exact (hDef.trans (min_le_right _ _)).trans_lt (half_lt_self hζ)
  have hv := hclose (r + s) hKU t hKT hd
  rw [Real.dist_eq] at hv
  have hdif : t ^ (1 - p) - (r + s) ^ (1 - p) < σ := by
    rw [abs_sub_comm] at hv
    exact (le_abs_self _).trans_lt hv
  have hslack : H + L - (r + s) ^ (1 - p) < 2 * σ := by
    have hη' : η ≤ σ := min_le_left _ _
    linarith only [hsum, hη', hdif]
  have hσδ : 2 * σ < δ := by
    have hh := min_le_left δ (ε * m ^ p)
    dsimp [σ]
    linarith only [hh, hδ]
  have hSeries := hgap r hr s hs ell hell (by linarith only [hH, hL, hslack, hσδ])
  have hR : 0 < r + s := add_pos (hl.trans_le hr.1) (hl.trans_le hs.1)
  have hratio : 2 * m ≤ r / (r + s) := by
    calc
      _ = l / (2 * u) := by dsimp [m]; field_simp; ring
      _ ≤ r / (2 * u) := div_le_div_of_nonneg_right hr.1 (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (hl.trans_le hr.1).le hR hKU.2
  have heq : 1 - s / (r + s) = r / (r + s) := by field_simp; ring
  have hell' : m ≤ 1 - ell := by
    have ha := (abs_lt.mp hSeries).2
    linarith only [heq, ha, hratio]
  have hw : 0 < 1 - ell := hm.trans_le hell'
  have hSer := (series_energy_minimum hp (hl.trans_le hr.1) (hl.trans_le hs.1) hell).1
  let V := r ^ (1 - p) * (1 - ell) ^ p
  have hdiff : H - V ≤ H + L - (r + s) ^ (1 - p) := by
    dsimp [V]
    linarith only [hSer, hL]
  have hErr : 2 * σ ≤ ε * (1 - ell) ^ p := by
    calc
      _ ≤ ε * m ^ p := by
        have hh := min_le_right δ (ε * m ^ p)
        dsimp [σ]
        linarith only [hh, mul_nonneg hε.le (Real.rpow_nonneg hm.le p)]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hm.le hell' hp'.le) hε.le
  refine ⟨sub_pos.mp hw, (div_le_iff₀ (Real.rpow_pos_of_pos hw p)).mpr ?_⟩
  have hEnd := hdiff.trans (hslack.le.trans hErr)
  dsimp [V] at hEnd
  rw [add_mul]
  linarith only [hEnd]

end WalkDimensions
