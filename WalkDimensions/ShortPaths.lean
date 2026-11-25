import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Short paths and snowflake lengths

The weighted selection step of Proposition 7.7 and the final chain
estimate in Proposition 7.1 of arXiv:2611.02422v1.
-/

open Finset
open scoped BigOperators

namespace WalkDimensions

/-- A positive weighted increment forces a path with both the claimed
increment and the claimed length. The path decomposition supplies the
weights and the bounds in this finite selection lemma. -/
theorem exists_short_path_of_weighted_bounds {ι : Type*} (paths : Finset ι)
    {weight length increment : ι → ℝ} {boundary cost pairing osc : ℝ}
    (hb : 0 < boundary) (hp : 0 < pairing) (ho : 0 < osc)
    (hw : ∀ i ∈ paths, 0 < weight i) (hl : ∀ i ∈ paths, 0 ≤ length i)
    (hi : ∀ i ∈ paths, increment i ≤ osc)
    (hweight : ∑ i ∈ paths, weight i ≤ boundary / 2)
    (hcost : ∑ i ∈ paths, weight i * length i ≤ cost)
    (hpairing : pairing ≤ ∑ i ∈ paths, weight i * increment i) :
    ∃ i ∈ paths, length i ≤ 2 * cost * osc / pairing ∧ pairing / boundary ≤ increment i := by
  classical
  let good := paths.filter (fun i ↦ pairing / boundary ≤ increment i)
  let bad := paths.filter (fun i ↦ ¬ pairing / boundary ≤ increment i)
  have hg : good ⊆ paths := filter_subset _ _
  have hh : bad ⊆ paths := filter_subset _ _
  have hbad : ∑ i ∈ bad, weight i * increment i ≤ pairing / 2 := by
    calc
      _ ≤ ∑ i ∈ bad, weight i * (pairing / boundary) := by
        apply sum_le_sum
        intro i h
        exact mul_le_mul_of_nonneg_left (le_of_not_ge (mem_filter.1 h).2) (hw i (hh h)).le
      _ = (∑ i ∈ bad, weight i) * (pairing / boundary) := by rw [sum_mul]
      _ ≤ (boundary / 2) * (pairing / boundary) := by
        apply mul_le_mul_of_nonneg_right _ (div_nonneg hp.le hb.le)
        exact (sum_le_sum_of_subset_of_nonneg hh fun i h _ ↦ (hw i h).le).trans hweight
      _ = pairing / 2 := by field_simp
  have hgood : ∑ i ∈ good, weight i * increment i ≤ (∑ i ∈ good, weight i) * osc := by
    rw [sum_mul]
    exact sum_le_sum fun i h ↦ mul_le_mul_of_nonneg_left (hi i (hg h)) (hw i (hg h)).le
  have hsplit : (∑ i ∈ good, weight i * increment i) +
      (∑ i ∈ bad, weight i * increment i) = ∑ i ∈ paths, weight i * increment i :=
    sum_filter_add_sum_filter_not paths (fun i ↦ pairing / boundary ≤ increment i) _
  have hmass : pairing / (2 * osc) ≤ ∑ i ∈ good, weight i := by
    apply (div_le_iff₀ (by positivity)).2
    linarith only [hpairing, hsplit, hgood, hbad]
  have hgoodne : good.Nonempty := by
    by_contra! h
    rw [h, sum_empty] at hmass
    exact (not_le_of_gt (div_pos hp (by positivity))) hmass
  have hgc : ∑ i ∈ good, weight i * length i ≤ cost :=
    (sum_le_sum_of_subset_of_nonneg hg fun i h _ ↦ mul_nonneg (hw i h).le (hl i h)).trans hcost
  obtain ⟨i, hi', hmin⟩ := exists_min_image good length hgoodne
  refine ⟨i, hg hi', ?_, (mem_filter.1 hi').2⟩
  apply (le_div_iff₀ hp).2
  have hmin' : (∑ j ∈ good, weight j) * length i ≤ cost := by
    rw [sum_mul]
    exact (sum_le_sum fun j hj ↦
      mul_le_mul_of_nonneg_left (hmin j hj) (hw j (hg hj)).le).trans hgc
  have hprod := mul_le_mul_of_nonneg_right hmass (hl i (hg hi'))
  have hdiv : pairing / (2 * osc) * length i ≤ cost := hprod.trans hmin'
  rw [mul_comm, ← mul_div_assoc] at hdiv
  have hfinal := (div_le_iff₀ (show 0 < 2 * osc by positivity)).1 hdiv
  linarith only [hfinal]

variable {X : Type*} [MetricSpace X]

/-- The estimate on chains in a snowflaked metric. Here the step lengths
are in the original metric. -/
theorem dist_le_of_snowflake_chain {γ δ L : ℝ} (hγ : 0 < γ) (hγ₁ : γ ≤ 1)
    (hδ : 0 ≤ δ) (z : ℕ → X) (n : ℕ)
    (hstep : ∀ i ∈ range n, dist (z i) (z (i + 1)) ≤ δ)
    (hlength : ∑ i ∈ range n, dist (z i) (z (i + 1)) ^ γ ≤ L) :
    dist (z 0) (z n) ≤ δ ^ (1 - γ) * L := by
  have hstep' (i : ℕ) (hi : i ∈ range n) :
      dist (z i) (z (i + 1)) ≤ δ ^ (1 - γ) * dist (z i) (z (i + 1)) ^ γ := by
    let d := dist (z i) (z (i + 1))
    have hd : 0 ≤ d := dist_nonneg
    calc
      d = d ^ (1 - γ) * d ^ γ := by
        rw [← Real.rpow_add_of_nonneg hd (sub_nonneg.mpr hγ₁) hγ.le, sub_add_cancel, Real.rpow_one]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow hd (hstep i hi) (sub_nonneg.mpr hγ₁)) (Real.rpow_nonneg hd _)
  calc
    _ ≤ ∑ i ∈ range n, dist (z i) (z (i + 1)) := dist_le_range_sum_dist z n
    _ ≤ ∑ i ∈ range n, δ ^ (1 - γ) * dist (z i) (z (i + 1)) ^ γ := sum_le_sum hstep'
    _ ≤ _ := by
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left hlength (Real.rpow_nonneg hδ _)

end WalkDimensions
