import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Hausdorff measure bounded by lower densities on fine ball covers
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal Topology

namespace WalkDimensions

variable {X : Type*} [MetricSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

theorem hausdorffMeasure_le_of_fine_lower_ball_mass (ν : Measure X) [ν.OuterRegular]
    {c : ℝ} (hc : 0 < c) {K : ℝ≥0∞} (hK : K ≠ ∞) {S : Set X}
    (hdensity : ∀ x ∈ S, ∀ ε > (0 : ℝ), ∃ r ∈ Ioo (0 : ℝ) ε,
      (ENNReal.ofReal r) ^ c ≤ K * ν (ball x r)) :
    μH[c] S ≤ ((10 : ℝ≥0∞) ^ c * K) * ν S := by
  by_cases hK0 : K = 0
  · have hS : S = ∅ := eq_empty_iff_forall_notMem.mpr fun x hx ↦ by
      obtain ⟨r, hr, hmass⟩ := hdensity x hx 1 zero_lt_one
      have h : 0 < (ENNReal.ofReal r) ^ c := ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hr.1) ENNReal.ofReal_ne_top
      rw [hK0, zero_mul] at hmass
      exact h.not_ge hmass
    simp only [hS, measure_empty, mul_zero, le_refl]
  let D := (10 : ℝ≥0∞) ^ c
  have hD : D ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hc.le (by norm_num)
  let M := D * K
  have hM : M ≠ ∞ := ENNReal.mul_ne_top hD hK
  have hD0 : D ≠ 0 := (ENNReal.rpow_pos (by norm_num : (0 : ℝ≥0∞) < 10)
    (by norm_num)).ne'
  have hM0 : M ≠ 0 := mul_ne_zero hD0 hK0
  rw [show ((10 : ℝ≥0∞) ^ c * K) = M from rfl, S.measure_eq_iInf_isOpen ν,
    ENNReal.mul_iInf_of_ne hM0 hM]
  refine le_iInf fun G ↦ ?_
  rw [ENNReal.mul_iInf_of_ne hM0 hM]
  refine le_iInf fun hSG ↦ ?_
  rw [ENNReal.mul_iInf_of_ne hM0 hM]
  refine le_iInf fun hG ↦ ?_
  let ε (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp only [ε]; positivity
  have hlocal (n : ℕ) (x : S) : ∃ r : ℝ, 0 < r ∧ r ≤ ε n / 10 ∧
      ball (x : X) r ⊆ G ∧ (ENNReal.ofReal r) ^ c ≤ K * ν (ball (x : X) r) := by
    obtain ⟨δ, hδ, hδG⟩ := Metric.mem_nhds_iff.mp (hG.mem_nhds (hSG x.property))
    obtain ⟨r, hr, hm⟩ := hdensity x x.property (min δ (ε n / 10))
      (lt_min hδ (div_pos (hε n) (by norm_num)))
    exact ⟨r, hr.1, hr.2.le.trans (min_le_right _ _),
      (ball_subset_ball (hr.2.le.trans (min_le_left _ _))).trans hδG, hm⟩
  choose r hrpos hrlim hrG hrM using hlocal
  choose u _ hudis hucov using fun n ↦
    Vitali.exists_disjoint_subfamily_covering_enlargement_ball (univ : Set S)
      (fun x ↦ (x : X)) (r n) (ε n / 10) (fun x _ ↦ hrlim n x) 5 (by norm_num)
  have huCount (n : ℕ) : (u n).Countable :=
    (hudis n).countable_of_isOpen (fun _ _ ↦ isOpen_ball) (fun i _ ↦
      ⟨(i : X), mem_ball_self (hrpos n i)⟩)
  have : ∀ n, Countable (u n) := fun n ↦ (huCount n).to_subtype
  let B (n : ℕ) (i : u n) := ball ((i : S) : X) (5 * r n i)
  have hdiam (n : ℕ) (i : u n) : ediam (B n i) ≤ ENNReal.ofReal (10 * r n i) := by
    apply ediam_le_iff.mpr
    intro x hx y hy
    rw [edist_dist]
    apply ENNReal.ofReal_le_ofReal
    have hx' : dist x ((i : S) : X) < 5 * r n i := mem_ball.mp hx
    have hy' : dist y ((i : S) : X) < 5 * r n i := mem_ball.mp hy
    exact (dist_triangle_right x y ((i : S) : X)).trans (by linarith only [hx', hy'])
  have hcover (n : ℕ) : S ⊆ ⋃ i : u n, B n i := by
    intro x hx
    obtain ⟨y, hy, hyb⟩ := hucov n (⟨x, hx⟩ : S) (mem_univ _)
    exact mem_iUnion.mpr ⟨⟨y, hy⟩, hyb (mem_ball_self (hrpos n ⟨x, hx⟩))⟩
  have hcost (n : ℕ) : (∑' i : u n, ediam (B n i) ^ c) ≤ M * ν G := by
    have hball (i : u n) : ediam (B n i) ^ c ≤ M * ν (ball ((i : S) : X) (r n i)) := by
      apply (ENNReal.rpow_le_rpow (hdiam n i) hc.le).trans
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 10), ENNReal.mul_rpow_of_nonneg _ _ hc.le,
        show ENNReal.ofReal (10 : ℝ) ^ c = D by norm_num [D], show M = D * K by rfl, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hrM n i) bot_le
    calc
      _ ≤ ∑' i : u n, M * ν (ball ((i : S) : X) (r n i)) := tsum_le_tsum hball
      _ = M * ν (⋃ i : u n, ball ((i : S) : X) (r n i)) := by
        have hdis : Pairwise (Disjoint on fun i : u n ↦ ball ((i : S) : X) (r n i)) :=
          fun i j hij ↦ hudis n i.property j.property (fun he ↦ hij (Subtype.ext he))
        rw [ENNReal.tsum_mul_left, measure_iUnion hdis (fun _ ↦ measurableSet_ball)]
      _ ≤ _ := mul_le_mul_of_nonneg_left (measure_mono (iUnion_subset fun i ↦ hrG n i)) bot_le
  have hlim : Tendsto (fun n ↦ ENNReal.ofReal (ε n)) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
  refine (Measure.hausdorffMeasure_le_liminf_tsum c S (fun n ↦ ENNReal.ofReal (ε n)) hlim B
    (Eventually.of_forall fun n i ↦ (hdiam n i).trans (ENNReal.ofReal_le_ofReal
      (by have hh := hrlim n i; linarith only [hh]))) (Eventually.of_forall hcover)).trans ?_
  exact liminf_le_of_frequently_le (Frequently.of_forall hcost) (by isBoundedDefault)

end WalkDimensions
