import WalkDimensions.Doubling
import Mathlib.Order.Zorn
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Separated covers and packing on doubling spaces
-/

open MeasureTheory Metric Set
open scoped BigOperators ENNReal

namespace WalkDimensions

variable {X : Type*} [MetricSpace X]

/-- A maximal separated subset covers the prescribed set by open balls
at the separation radius. -/
theorem exists_separated_ball_cover (U : Set X) {s : ℝ} (hs : 0 < s) :
    ∃ W ⊆ U, W.Pairwise (fun x y ↦ s ≤ dist x y) ∧ U ⊆ ⋃ z ∈ W, ball z s := by
  let P := {W : Set X | W ⊆ U ∧ W.Pairwise (fun x y ↦ s ≤ dist x y)}
  obtain ⟨W, hW⟩ := zorn_subset P (by
    intro T hT hchain
    refine ⟨⋃₀ T, ⟨sUnion_subset (fun V hV ↦ (hT hV).1), ?_⟩, fun V hV ↦ subset_sUnion_of_mem hV⟩
    intro x hx y hy hxy
    obtain ⟨A, hA, hxA⟩ := mem_sUnion.mp hx
    obtain ⟨B, hB, hyB⟩ := mem_sUnion.mp hy
    rcases hchain.total hA hB with hAB | hBA
    · exact (hT hB).2 (hAB hxA) hyB hxy
    · exact (hT hA).2 hxA (hBA hyB) hxy)
  obtain ⟨hWU, hsep⟩ := hW.prop
  refine ⟨W, hWU, hsep, fun x hx ↦ ?_⟩
  by_contra hmiss
  have hxW : x ∉ W := fun h ↦ hmiss (mem_iUnion₂.mpr ⟨x, h, mem_ball_self hs⟩)
  have hxsep (y : X) (hy : y ∈ W) : s ≤ dist x y :=
    le_of_not_gt fun hh ↦ hmiss (mem_iUnion₂.mpr ⟨y, hy, mem_ball.mpr hh⟩)
  have hi : insert x W ∈ P := by
    refine ⟨insert_subset hx hWU, ?_⟩
    intro y hy z hz hyz
    by_cases hyx : y = x
    · subst y
      exact hxsep z ((mem_insert_iff.mp hz).resolve_left hyz.symm)
    · have hyW : y ∈ W := (mem_insert_iff.mp hy).resolve_left hyx
      by_cases hzx : z = x
      · subst z
        rw [dist_comm]
        exact hxsep y hyW
      · exact hsep hyW ((mem_insert_iff.mp hz).resolve_left hzx) hyz
  exact hxW (hW.eq_of_le hi (subset_insert x W) ▸ mem_insert x W)

/-- A compact set has a finite open ball cover whose centres lie in the
set and are separated by the same radius. -/
theorem exists_finset_separated_ball_cover {K : Set X} (hK : IsCompact K)
    {s : ℝ} (hs : 0 < s) :
    ∃ t : Finset X, (↑t : Set X) ⊆ K ∧ (↑t : Set X).Pairwise (fun x y ↦ s ≤ dist x y) ∧
      K ⊆ ⋃ z ∈ t, ball z s := by
  classical
  obtain ⟨W, hWK, hsep, hcover⟩ := exists_separated_ball_cover K hs
  obtain ⟨V, _, hV, hVcover⟩ := hK.finite_cover_balls (show 0 < s / 2 by positivity)
  have hnear (x : W) : ∃ z ∈ V, (x : X) ∈ ball z (s / 2) := by
    obtain ⟨z, hz, hzx⟩ := Set.mem_iUnion₂.mp (hVcover (hWK x.property))
    exact ⟨z, hz, hzx⟩
  choose z hz hzball using hnear
  have hinj : Function.Injective (fun x : W ↦ (⟨z x, hz x⟩ : V)) := by
    intro x y hxy
    have he : z x = z y := congrArg Subtype.val hxy
    apply Subtype.ext
    by_contra hne
    have hfar := hsep x.property y.property hne
    have hx := mem_ball.mp (hzball x)
    have hy := mem_ball.mp (hzball y)
    rw [← he, dist_comm (y : X)] at hy
    have htri := dist_triangle (x : X) (z x) (y : X)
    linarith
  let : Finite V := hV
  let : Finite W := Finite.of_injective _ hinj
  have hW : W.Finite := Set.toFinite _
  exact ⟨hW.toFinset, by simpa using hWK, by simpa using hsep, by simpa using hcover⟩

private theorem pairwiseDisjoint_ball_of_separation {W : Set X} {s : ℝ}
    (hsep : W.Pairwise (fun x y ↦ 2 * s ≤ dist x y)) :
    W.PairwiseDisjoint fun x ↦ ball x s := by
  intro x hx y hy hxy
  apply disjoint_left.mpr
  intro z hzx hzy
  have h := dist_triangle x z y
  rw [dist_comm x z] at h
  exact (not_lt_of_ge (hsep hx hy hxy)) (h.trans_lt (by
    have hx' := mem_ball.mp hzx
    have hy' := mem_ball.mp hzy
    linarith))

/-- The packing bound depends only on the doubling data and the ratio of
the surrounding radius to the separation radius. -/
theorem exists_card_le_of_separated_centres [MeasurableSpace X] [BorelSpace X] {m : Measure X}
    [ProperSpace X] [IsFiniteMeasureOnCompacts m] [m.IsOpenPosMeasure]
    (hvol : VolumeDoubling m) {R : ℝ} (hR : 0 ≤ R) :
    ∃ N : ℕ, 0 < N ∧ ∀ (x : X) (s : ℝ), 0 < s → ∀ t : Finset X,
      (∀ z ∈ t, dist z x ≤ R * s) →
      (↑t : Set X).Pairwise (fun y z ↦ 2 * s ≤ dist y z) → t.card ≤ N := by
  obtain ⟨D, hDpos, hD⟩ := hvol
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 * R + 1) (show (1 : ℝ) < 2 by norm_num)
  obtain ⟨N, hN⟩ := exists_nat_gt (D ^ n)
  refine ⟨N, by exact_mod_cast (pow_pos hDpos n).trans hN, fun x s hs t hin hsep ↦ ?_⟩
  let v := m (ball x ((R + 1) * s))
  have hvpos : 0 < v := measure_ball_pos _ _ (mul_pos (by linarith) hs)
  have hvfin : v ≠ ∞ := measure_ball_ne_top
  have hlocal (z : X) (hz : z ∈ t) :
      v ≤ (ENNReal.ofReal D) ^ n * m (ball z s) := by
    apply measure_ball_le_of_dist_le hD hs n
    rw [dist_comm x z]
    calc
      _ ≤ (2 * R + 1) * s := by
        have h := hin z hz
        linarith only [h]
      _ ≤ _ := mul_le_mul_of_nonneg_right hn.le hs.le
  have hunion : (⋃ z ∈ t, ball z s) ⊆ ball x ((R + 1) * s) := by
    intro y hy
    obtain ⟨z, hz, hyz⟩ := mem_iUnion₂.mp hy
    apply mem_ball.mpr
    have h := hin z hz
    exact (dist_triangle y z x).trans_lt (by have hy' := mem_ball.mp hyz; linarith only [hy', h])
  have hsum : (∑ z ∈ t, m (ball z s)) ≤ v := by
    rw [← measure_biUnion_finset (pairwiseDisjoint_ball_of_separation hsep)
      (fun _ _ ↦ measurableSet_ball)]
    exact measure_mono hunion
  have hmul : (t.card : ℝ≥0∞) * v ≤ (ENNReal.ofReal D) ^ n * v := by
    calc
      _ = ∑ _ ∈ t, v := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ z ∈ t, (ENNReal.ofReal D) ^ n * m (ball z s) := Finset.sum_le_sum hlocal
      _ = (ENNReal.ofReal D) ^ n * ∑ z ∈ t, m (ball z s) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum bot_le
  have hcard : (t.card : ℝ≥0∞) ≤ (ENNReal.ofReal D) ^ n := by
    have h : (t.card : ℝ≥0∞) * v * v⁻¹ ≤ (ENNReal.ofReal D) ^ n * v * v⁻¹ :=
      mul_le_mul_of_nonneg_right hmul bot_le
    simpa only [mul_assoc, ENNReal.mul_inv_cancel hvpos.ne' hvfin, mul_one] using h
  have hN' : (ENNReal.ofReal D) ^ n ≤ (N : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_pow hDpos.le, ← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hN.le
  exact_mod_cast hcard.trans hN'

/-- The multiplicity of enlarged balls in a separated cover is uniformly
bounded. The integral estimate applies to every nonnegative density. -/
theorem exists_sum_setLIntegral_ball_le [MeasurableSpace X] [BorelSpace X] {m : Measure X}
    [ProperSpace X] [IsFiniteMeasureOnCompacts m] [m.IsOpenPosMeasure]
    (hvol : VolumeDoubling m) {A : ℝ} (hA : 0 ≤ A) :
    ∃ N : ℕ, 0 < N ∧ ∀ (t : Finset X) (r : ℝ), 0 < r →
      (↑t : Set X).Pairwise (fun x y ↦ r ≤ dist x y) →
      ∀ f : X → ℝ≥0∞, Measurable f →
        (∑ z ∈ t, ∫⁻ x in ball z (A * r), f x ∂m) ≤ (N : ℝ≥0∞) * ∫⁻ x, f x ∂m := by
  classical
  obtain ⟨N, hN, hpack⟩ := exists_card_le_of_separated_centres hvol (R := 2 * A) (by positivity)
  refine ⟨N, hN, fun t r hr hsep f hf ↦ ?_⟩
  have hcard (x : X) : (t.filter (fun z ↦ x ∈ ball z (A * r))).card ≤ N := by
    apply hpack x (r / 2) (by positivity)
    · intro z hz
      have hh := mem_ball.mp (Finset.mem_filter.mp hz).2
      rw [dist_comm z x, show 2 * A * (r / 2) = A * r by ring]
      exact hh.le
    · intro z hz y hy hzy
      rw [show 2 * (r / 2) = r by ring]
      exact hsep (Finset.mem_filter.mp hz).1 (Finset.mem_filter.mp hy).1 hzy
  simp_rw [← lintegral_indicator measurableSet_ball]
  rw [← lintegral_finsetSum t (fun z _ ↦ hf.indicator measurableSet_ball),
    ← lintegral_const_mul' _ _ (ENNReal.natCast_ne_top N)]
  apply lintegral_mono
  intro x
  change (∑ z ∈ t, (ball z (A * r)).indicator f x) ≤ (N : ℝ≥0∞) * f x
  simp only [indicator_apply, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard x) bot_le

end WalkDimensions
