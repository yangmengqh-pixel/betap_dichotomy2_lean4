import WalkDimensions.Geometry
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Distances defined by fine chains

The infimum of lengths of chains of bounded mesh increases as the mesh
shrinks. The chain condition bounds the resulting distance by the original
distance up to a constant.
-/

open Filter Function Metric Set
open scoped Topology

namespace WalkDimensions

variable {X : Type*} [MetricSpace X]

structure MeshChain (ε : ℝ) (x y : X) where
  steps : ℕ
  vertex : ℕ → X
  start_eq : vertex 0 = x
  end_eq : vertex steps = y
  mesh_le : ∀ k < steps, dist (vertex k) (vertex (k + 1)) ≤ ε

namespace MeshChain

noncomputable def length {ε : ℝ} {x y : X} (c : MeshChain ε x y) : ℝ :=
  ∑ k ∈ Finset.range c.steps, dist (c.vertex k) (c.vertex (k + 1))

theorem dist_le_length {ε : ℝ} {x y : X} (c : MeshChain ε x y) : dist x y ≤ c.length := by
  simpa only [length, c.start_eq, c.end_eq] using dist_le_range_sum_dist c.vertex c.steps

def widen {ε η : ℝ} {x y : X} (c : MeshChain ε x y) (h : ε ≤ η) : MeshChain η x y where
  steps := c.steps
  vertex := c.vertex
  start_eq := c.start_eq
  end_eq := c.end_eq
  mesh_le k hk := (c.mesh_le k hk).trans h

def initial {ε : ℝ} {x y : X} (c : MeshChain ε x y) {i : ℕ} (hi : i ≤ c.steps) :
    MeshChain ε x (c.vertex i) where
  steps := i
  vertex := c.vertex
  start_eq := c.start_eq
  end_eq := rfl
  mesh_le k hk := c.mesh_le k (hk.trans_le hi)

def suffix {ε : ℝ} {x y : X} (c : MeshChain ε x y) {i : ℕ} (hi : i ≤ c.steps) :
    MeshChain ε (c.vertex i) y where
  steps := c.steps - i
  vertex k := c.vertex (i + k)
  start_eq := by simp
  end_eq := by rw [Nat.add_sub_of_le hi, c.end_eq]
  mesh_le k hk := by
    rw [← Nat.add_assoc]
    exact c.mesh_le (i + k) (by omega)

theorem length_initial_add_suffix {ε : ℝ} {x y : X} (c : MeshChain ε x y)
    {i : ℕ} (hi : i ≤ c.steps) : (c.initial hi).length + (c.suffix hi).length = c.length := by
  unfold length
  change (∑ k ∈ Finset.range i, dist (c.vertex k) (c.vertex (k + 1))) +
    (∑ k ∈ Finset.range (c.steps - i), dist (c.vertex (i + k)) (c.vertex (i + (k + 1)))) = _
  simp only [← Nat.add_assoc]
  rw [← Finset.sum_range_add, Nat.add_sub_of_le hi]

def reverse {ε : ℝ} {x y : X} (c : MeshChain ε x y) : MeshChain ε y x where
  steps := c.steps
  vertex k := c.vertex (c.steps - k)
  start_eq := by simpa only [Nat.sub_zero] using c.end_eq
  end_eq := by simpa only [Nat.sub_self] using c.start_eq
  mesh_le k hk := by
    rw [dist_comm, show c.steps - k = (c.steps - (k + 1)) + 1 by omega]
    exact c.mesh_le _ (by omega)

theorem length_reverse {ε : ℝ} {x y : X} (c : MeshChain ε x y) : c.reverse.length = c.length := by
  unfold length
  rw [← Finset.sum_range_reflect (fun k ↦ dist (c.vertex k) (c.vertex (k + 1))) c.steps]
  apply Finset.sum_congr rfl
  intro k hk
  have h : k < c.steps := Finset.mem_range.mp hk
  change dist (c.vertex (c.steps - k)) (c.vertex (c.steps - (k + 1))) = _
  rw [dist_comm]
  congr 2 <;> omega

def append {ε : ℝ} {x y z : X} (a : MeshChain ε x y) (b : MeshChain ε y z) :
    MeshChain ε x z where
  steps := a.steps + b.steps
  vertex k := if k < a.steps then a.vertex k else b.vertex (k - a.steps)
  start_eq := by
    by_cases h : 0 < a.steps
    · rw [ite_eq_left h, a.start_eq]
    · rw [ite_eq_right h, Nat.zero_sub, b.start_eq, ← a.end_eq,
        show a.steps = 0 by omega, a.start_eq]
  end_eq := by
    rw [ite_eq_right (by omega), Nat.add_sub_cancel_left, b.end_eq]
  mesh_le k hk := by
    by_cases h : k < a.steps
    · rw [ite_eq_left h]
      have he : (if k + 1 < a.steps then a.vertex (k + 1) else b.vertex (k + 1 - a.steps)) =
          a.vertex (k + 1) := by
        split
        · rfl
        · have hc : k + 1 = a.steps := by omega
          rw [hc, Nat.sub_self, b.start_eq, a.end_eq]
      rw [he]
      exact a.mesh_le k h
    · rw [ite_eq_right h, ite_eq_right (by omega), show k + 1 - a.steps = (k - a.steps) + 1 by omega]
      exact b.mesh_le _ (by omega)

theorem length_append {ε : ℝ} {x y z : X} (a : MeshChain ε x y) (b : MeshChain ε y z) :
    (a.append b).length = a.length + b.length := by
  unfold length
  change (∑ k ∈ Finset.range (a.steps + b.steps), _) = _
  rw [Finset.sum_range_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro k hk
    have h := Finset.mem_range.mp hk
    change dist (ite _ _ _) (ite _ _ _) = _
    rw [ite_eq_left h]
    by_cases hs : k + 1 < a.steps
    · rw [ite_eq_left hs]
    · have hc : k + 1 = a.steps := by omega
      rw [ite_eq_right hs, hc, Nat.sub_self, b.start_eq, a.end_eq]
  · apply Finset.sum_congr rfl
    intro k hk
    change dist (ite _ _ _) (ite _ _ _) = _
    rw [ite_eq_right (by omega), ite_eq_right (by omega),
      show a.steps + k - a.steps = k by omega,
      show a.steps + k + 1 - a.steps = k + 1 by omega]

theorem exists_middle {ε : ℝ} {x y : X} (c : MeshChain ε x y) (hε : 0 ≤ ε) :
    ∃ i : ℕ, ∃ hi : i ≤ c.steps, (c.initial hi).length ≤ c.length / 2 + ε ∧
      (c.suffix hi).length ≤ c.length / 2 := by
  classical
  let L (n : ℕ) := ∑ k ∈ Finset.range n, dist (c.vertex k) (c.vertex (k + 1))
  let hne : ∃ n : ℕ, c.length / 2 ≤ L n := ⟨c.steps, by
    change c.length / 2 ≤ c.length
    linarith only [dist_nonneg (x := x) (y := y), c.dist_le_length]⟩
  let i := Nat.find hne
  have hi : i ≤ c.steps := Nat.find_min' hne (by
    change c.length / 2 ≤ c.length
    linarith only [dist_nonneg (x := x) (y := y), c.dist_le_length])
  refine ⟨i, hi, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos i with h₀ | hpos
    · change L i ≤ _
      rw [h₀, show L 0 = 0 by simp [L]]
      linarith only [dist_nonneg (x := x) (y := y), c.dist_le_length, hε]
    · have hprev : L (i - 1) < c.length / 2 :=
        lt_of_not_ge (Nat.find_min hne (by change i - 1 < i; omega))
      have he : L i = L (i - 1) + dist (c.vertex (i - 1)) (c.vertex (i - 1 + 1)) := by
        conv_lhs => rw [show i = (i - 1) + 1 by omega]
        exact Finset.sum_range_succ _ _
      change L i ≤ _
      linarith only [he, hprev, c.mesh_le (i - 1) (by omega)]
  · have h₀ : c.length / 2 ≤ (c.initial hi).length := Nat.find_spec hne
    linarith only [c.length_initial_add_suffix hi, h₀]

end MeshChain

noncomputable def meshDistance (ε : ℝ) (x y : X) : ℝ :=
  sInf (range (MeshChain.length (ε := ε) (x := x) (y := y)))

theorem meshDistance_bddBelow (ε : ℝ) (x y : X) :
    BddBelow (range (MeshChain.length (ε := ε) (x := x) (y := y))) :=
  ⟨dist x y, fun _ ⟨c, hc⟩ ↦ hc ▸ c.dist_le_length⟩

theorem meshDistance_le_length {ε : ℝ} {x y : X} (c : MeshChain ε x y) :
    meshDistance ε x y ≤ c.length :=
  csInf_le (meshDistance_bddBelow ε x y) (mem_range_self c)

theorem ChainCondition.exists_meshChain_length_le (hCC : ChainCondition X) :
    ∃ C > (0 : ℝ), ∀ ε > (0 : ℝ), ∀ x y : X, ∃ c : MeshChain ε x y, c.length ≤ C * dist x y := by
  obtain ⟨C, hC, h⟩ := hCC
  refine ⟨C, hC, fun ε hε x y ↦ ?_⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (max (C * dist x y / ε) 1)
  have hn₁ : 1 ≤ n := by exact_mod_cast (le_max_right _ _).trans hn.le
  have hn₀ : 0 < (n : ℝ) := zero_lt_one.trans (lt_of_le_of_lt (le_max_right _ _) hn)
  obtain ⟨f, hf₀, hfn, hf⟩ := h x y n hn₁
  have he : C * dist x y / n ≤ ε := by
    apply (div_le_iff₀ hn₀).mpr
    have he' := (div_lt_iff₀ hε).mp ((le_max_left _ _).trans_lt hn)
    exact he'.le.trans_eq (mul_comm _ _)
  let c : MeshChain ε x y :=
    ⟨n, f, hf₀, hfn, fun k hk ↦ by rw [dist_comm]; exact (hf k hk).trans he⟩
  refine ⟨c, ?_⟩
  unfold MeshChain.length
  calc
    _ ≤ ∑ k ∈ Finset.range n, C * dist x y / n := by
      apply Finset.sum_le_sum
      intro k hk
      change dist (f k) (f (k + 1)) ≤ _
      rw [dist_comm]
      exact hf k (Finset.mem_range.mp hk)
    _ = C * dist x y := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm (n : ℝ)]
      exact div_mul_cancel₀ _ hn₀.ne'

end WalkDimensions
