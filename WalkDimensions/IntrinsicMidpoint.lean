import WalkDimensions.IntrinsicDistance

/-!
# Midpoints of the intrinsic chain distance

A midpoint on each sufficiently fine near-minimizing chain stays in one
compact ball. Passing to a subsequence and then testing every mesh gives
an exact midpoint.
-/

open Filter Function Metric Set
open scoped Topology

namespace WalkDimensions

variable {X : Type*} [MetricSpace X] [ProperSpace X]

set_option maxHeartbeats 650000 in
theorem exists_intrinsicDistance_midpoint (hCC : ChainCondition X) (x y : X) :
    ∃ z : X, intrinsicDistance x z = intrinsicDistance x y / 2 ∧
      intrinsicDistance z y = intrinsicDistance x y / 2 := by
  let L := intrinsicDistance x y
  have hL : 0 ≤ L := dist_nonneg.trans (dist_le_intrinsicDistance hCC x y)
  obtain ⟨C, hC, hchain⟩ := hCC.exists_meshChain_length_le
  have hmesh (ε : ℝ) (hε : 0 < ε) (a b : X) :
      meshDistance ε a b ≤ C * dist a b := by
    obtain ⟨c, hc⟩ := hchain ε hε a b
    exact (meshDistance_le_length c).trans hc
  choose c hc using fun n ↦ exists_meshChain_length_lt hCC (meshWidth_pos n) x y
    ((meshDistance_le_intrinsicDistance hCC (meshWidth_pos n) x y).trans_lt
      (lt_add_of_pos_right L (meshWidth_pos n)))
  choose i hi hLeft hRight using fun n ↦ (c n).exists_middle (meshWidth_pos n).le
  let zₙ (n : ℕ) := (c n).vertex (i n)
  have hZ (n : ℕ) : zₙ n ∈ closedBall x (L / 2 + 2) := by
    apply mem_closedBall.mpr
    rw [dist_comm]
    have hm : meshWidth n ≤ 1 :=
      (meshWidth_antitone (Nat.zero_le n)).trans_eq (by norm_num [meshWidth])
    exact ((c n).initial (hi n)).dist_le_length.trans ((hLeft n).trans (by
      linarith only [hc n, hm]))
  obtain ⟨z, _, φ, hφ, hlim⟩ := (isCompact_closedBall _ _).tendsto_subseq hZ
  have hφTop := hφ.tendsto_atTop
  have hmeshlim := tendsto_meshWidth_zero.comp hφTop
  have hdistlim : Tendsto (fun n ↦ dist (zₙ (φ n)) z) atTop (𝓝 0) := by
    have hd := hlim.dist (tendsto_const_nhds (x := z))
    simpa only [dist_self, Function.comp_def] using hd
  have htotal : Tendsto (fun n ↦ L / 2 + 3 / 2 * meshWidth (φ n) + C * dist (zₙ (φ n)) z)
        atTop (𝓝 (L / 2)) := by
    simpa only [Function.comp_def, mul_zero, add_zero] using ((hmeshlim.const_mul (3 / 2 : ℝ)).const_add (L / 2)).add
      (hdistlim.const_mul C)
  have hleft : intrinsicDistance x z ≤ L / 2 := by
    apply ciSup_le
    intro k
    let ε := meshWidth k
    have hε := meshWidth_pos k
    apply ge_of_tendsto htotal
    filter_upwards [hmeshlim.eventually_lt_const hε] with n hn
    have h1 := meshDistance_triangle hCC hε x (zₙ (φ n)) z
    have h2 := meshDistance_le_length (((c (φ n)).initial (hi (φ n))).widen hn.le)
    change meshDistance ε x (zₙ (φ n)) ≤ ((c (φ n)).initial (hi (φ n))).length at h2
    have h3 := hmesh ε hε (zₙ (φ n)) z
    linarith only [h1, h2, h3, hLeft (φ n), hc (φ n)]
  have hright : intrinsicDistance z y ≤ L / 2 := by
    apply ciSup_le
    intro k
    let ε := meshWidth k
    have hε := meshWidth_pos k
    apply ge_of_tendsto htotal
    filter_upwards [hmeshlim.eventually_lt_const hε] with n hn
    have h1 := meshDistance_triangle hCC hε z (zₙ (φ n)) y
    have h2 := meshDistance_le_length (((c (φ n)).suffix (hi (φ n))).widen hn.le)
    change meshDistance ε (zₙ (φ n)) y ≤ ((c (φ n)).suffix (hi (φ n))).length at h2
    have h3 := hmesh ε hε z (zₙ (φ n))
    rw [dist_comm z] at h3
    linarith only [h1, h2, h3, hRight (φ n), hc (φ n), meshWidth_pos (φ n)]
  have hsum : L ≤ intrinsicDistance x z + intrinsicDistance z y :=
    intrinsicDistance_triangle hCC x z y
  exact ⟨z, le_antisymm hleft (by linarith only [hsum, hright]),
    le_antisymm hright (by linarith only [hsum, hleft])⟩

end WalkDimensions
