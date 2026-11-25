import WalkDimensions.ChainDistance
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Intrinsic distance under the chain condition

Fine-chain distances converge to a distance comparable with the original
metric. Compactness gives exact midpoints for the new distance.
-/

open Filter Function Metric Set
open scoped Topology

namespace WalkDimensions

variable {X : Type*} [M : MetricSpace X]

theorem ChainCondition.nonempty_meshChain (hCC : ChainCondition X)
    {ε : ℝ} (hε : 0 < ε) (x y : X) : Nonempty (MeshChain ε x y) := by
  obtain ⟨_, _, h⟩ := hCC.exists_meshChain_length_le
  obtain ⟨c, _⟩ := h ε hε x y
  exact ⟨c⟩

theorem dist_le_meshDistance (hCC : ChainCondition X) {ε : ℝ} (hε : 0 < ε) (x y : X) :
    dist x y ≤ meshDistance ε x y := by
  let _ := hCC.nonempty_meshChain hε x y
  apply le_csInf (range_nonempty _)
  rintro _ ⟨c, rfl⟩
  exact c.dist_le_length

theorem meshDistance_anti (hCC : ChainCondition X) {ε η : ℝ}
    (hε : 0 < ε) (h : ε ≤ η) (x y : X) :
    meshDistance η x y ≤ meshDistance ε x y := by
  let _ := hCC.nonempty_meshChain hε x y
  apply le_csInf (range_nonempty _)
  rintro _ ⟨c, rfl⟩
  exact meshDistance_le_length (c.widen h)

theorem meshDistance_comm (hCC : ChainCondition X) {ε : ℝ} (hε : 0 < ε) (x y : X) :
    meshDistance ε x y = meshDistance ε y x := by
  have hle (a b : X) : meshDistance ε a b ≤ meshDistance ε b a := by
    let _ := hCC.nonempty_meshChain hε b a
    apply le_csInf (range_nonempty _)
    rintro _ ⟨c, rfl⟩
    exact (meshDistance_le_length c.reverse).trans_eq c.length_reverse
  exact le_antisymm (hle x y) (hle y x)

theorem exists_meshChain_length_lt (hCC : ChainCondition X) {ε : ℝ} (hε : 0 < ε)
    (x y : X) {b : ℝ} (hb : meshDistance ε x y < b) :
    ∃ c : MeshChain ε x y, c.length < b := by
  let _ := hCC.nonempty_meshChain hε x y
  obtain ⟨_, ⟨c, rfl⟩, hc⟩ := exists_lt_of_csInf_lt (range_nonempty _) hb
  exact ⟨c, hc⟩

theorem meshDistance_triangle (hCC : ChainCondition X) {ε : ℝ} (hε : 0 < ε) (x y z : X) :
    meshDistance ε x z ≤ meshDistance ε x y + meshDistance ε y z := by
  by_contra! h
  let δ := (meshDistance ε x z - (meshDistance ε x y + meshDistance ε y z)) / 3
  have hδ : 0 < δ := div_pos (sub_pos.mpr h) (by norm_num)
  obtain ⟨a, ha⟩ := exists_meshChain_length_lt hCC hε x y (lt_add_of_pos_right _ hδ)
  obtain ⟨b, hb⟩ := exists_meshChain_length_lt hCC hε y z (lt_add_of_pos_right _ hδ)
  have hab := meshDistance_le_length (a.append b)
  rw [MeshChain.length_append] at hab
  dsimp [δ] at ha hb
  linarith only [hab, ha, hb, h]

noncomputable def meshWidth (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem meshWidth_pos (n : ℕ) : 0 < meshWidth n := by unfold meshWidth; positivity

theorem meshWidth_antitone : Antitone meshWidth := fun _ _ hij ↦
  one_div_le_one_div_of_le (by positivity) (add_le_add_left (Nat.cast_le.mpr hij) _)

theorem tendsto_meshWidth_zero : Tendsto meshWidth atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

noncomputable def intrinsicDistance (x y : X) : ℝ := ⨆ n, meshDistance (meshWidth n) x y

theorem meshDistance_meshWidth_bddAbove (hCC : ChainCondition X) (x y : X) :
    BddAbove (range fun n ↦ meshDistance (meshWidth n) x y) := by
  obtain ⟨C, _, h⟩ := hCC.exists_meshChain_length_le
  refine ⟨C * dist x y, forall_mem_range.mpr fun n ↦ ?_⟩
  obtain ⟨c, hc⟩ := h _ (meshWidth_pos n) x y
  exact (meshDistance_le_length c).trans hc

theorem meshDistance_le_intrinsicDistance (hCC : ChainCondition X) {ε : ℝ} (hε : 0 < ε) (x y : X) :
    meshDistance ε x y ≤ intrinsicDistance x y := by
  obtain ⟨n, hn⟩ := (tendsto_meshWidth_zero.eventually_lt_const hε).exists
  exact (meshDistance_anti hCC (meshWidth_pos n) hn.le x y).trans
    (le_ciSup (meshDistance_meshWidth_bddAbove hCC x y) n)

theorem dist_le_intrinsicDistance (hCC : ChainCondition X) (x y : X) :
    dist x y ≤ intrinsicDistance x y :=
  (dist_le_meshDistance hCC zero_lt_one x y).trans
    (meshDistance_le_intrinsicDistance hCC zero_lt_one x y)

theorem ChainCondition.exists_intrinsicDistance_le (hCC : ChainCondition X) :
    ∃ C > (0 : ℝ), ∀ x y : X, intrinsicDistance x y ≤ C * dist x y := by
  obtain ⟨C, hC, h⟩ := hCC.exists_meshChain_length_le
  refine ⟨C, hC, fun x y ↦ ciSup_le fun n ↦ ?_⟩
  obtain ⟨c, hc⟩ := h _ (meshWidth_pos n) x y
  exact (meshDistance_le_length c).trans hc

theorem intrinsicDistance_self (hCC : ChainCondition X) (x : X) :
    intrinsicDistance x x = 0 := by
  obtain ⟨C, _, hC⟩ := hCC.exists_intrinsicDistance_le
  exact le_antisymm (by simpa only [dist_self, mul_zero] using hC x x)
    (by simpa only [dist_self] using dist_le_intrinsicDistance hCC x x)

theorem intrinsicDistance_comm (hCC : ChainCondition X) (x y : X) :
    intrinsicDistance x y = intrinsicDistance y x := by
  unfold intrinsicDistance
  exact iSup_congr fun n ↦ meshDistance_comm hCC (meshWidth_pos n) x y

theorem intrinsicDistance_triangle (hCC : ChainCondition X) (x y z : X) :
    intrinsicDistance x z ≤ intrinsicDistance x y + intrinsicDistance y z := by
  apply ciSup_le
  intro n
  exact (meshDistance_triangle hCC (meshWidth_pos n) x y z).trans
    (add_le_add (meshDistance_le_intrinsicDistance hCC (meshWidth_pos n) x y)
      (meshDistance_le_intrinsicDistance hCC (meshWidth_pos n) y z))

theorem intrinsicDistance_continuous_fixed (hCC : ChainCondition X) (x : X) :
    Continuous (intrinsicDistance x) := by
  obtain ⟨C, hC, hbound⟩ := hCC.exists_intrinsicDistance_le
  have hlip : LipschitzWith ⟨C, hC.le⟩ (intrinsicDistance x) := by
    apply lipschitzWith_iff_dist_le_mul.mpr
    intro y z
    rw [Real.dist_eq]
    apply abs_le.mpr
    have h₁ := intrinsicDistance_triangle hCC x y z
    have h₂ := intrinsicDistance_triangle hCC x z y
    have hz := hbound y z
    rw [intrinsicDistance_comm hCC z y] at h₂
    change -(C * dist y z) ≤ intrinsicDistance x y - intrinsicDistance x z ∧
      intrinsicDistance x y - intrinsicDistance x z ≤ C * dist y z
    constructor <;> linarith only [h₁, h₂, hz]
  exact hlip.continuous

theorem exists_intrinsicMetric (hCC : ChainCondition X) :
    let T := (inferInstance : TopologicalSpace X)
    ∃ D : MetricSpace X, @Dist.dist X D.toDist = @intrinsicDistance X M ∧
      D.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace = T := by
  obtain ⟨C, hC, hbound⟩ := hCC.exists_intrinsicDistance_le
  have hzero (x y : X) (h : intrinsicDistance x y = 0) : x = y :=
    dist_eq_zero.mp (le_antisymm (h ▸ dist_le_intrinsicDistance hCC x y) dist_nonneg)
  have htopo (S : Set X) :
      IsOpen S ↔ ∀ x ∈ S, ∃ ε > 0, ∀ y, intrinsicDistance x y < ε → y ∈ S := by
    rw [Metric.isOpen_iff]
    constructor
    · intro h x hx
      obtain ⟨r, hr, hball⟩ := h x hx
      refine ⟨r, hr, fun y hy ↦ hball (mem_ball.mpr ?_)⟩
      rw [dist_comm]
      exact (dist_le_intrinsicDistance hCC x y).trans_lt hy
    · intro h x hx
      obtain ⟨ε, hε, hball⟩ := h x hx
      refine ⟨ε / C, div_pos hε hC, fun y hy ↦ hball y ?_⟩
      apply (hbound x y).trans_lt
      rw [mul_comm, ← lt_div_iff₀ hC, dist_comm]
      exact mem_ball.mp hy
  let D := MetricSpace.ofDistTopology (@intrinsicDistance X M) (intrinsicDistance_self hCC)
    (intrinsicDistance_comm hCC) (intrinsicDistance_triangle hCC) htopo hzero
  refine ⟨D, ?_, rfl⟩
  rfl

end WalkDimensions
