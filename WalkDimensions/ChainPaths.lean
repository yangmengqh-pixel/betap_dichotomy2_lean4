import WalkDimensions.DyadicMidpoints
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Topology.Path

/-!
# Controlled paths from the chain condition

Dyadic midpoint chains converge to a Lipschitz path in the original
metric. This gives short paths contained in controlled balls.
-/

open Filter Function Metric Set
open scoped Topology

namespace WalkDimensions

variable {X : Type*} [MetricSpace X] [ProperSpace X]

omit [ProperSpace X] in
private theorem dist_along_dyadic_chain {z : ℕ → ℕ → X} {s : ℝ}
    (h : ∀ n k, k < (2 : ℕ) ^ n → dist (z n k) (z n (k + 1)) ≤ s / (2 : ℝ) ^ n)
    (n i j : ℕ) (hij : i ≤ j) (hj : j ≤ (2 : ℕ) ^ n) :
    dist (z n i) (z n j) ≤ (j - i : ℝ) * (s / (2 : ℝ) ^ n) := by
  have hs (k : ℕ) (hk : i + k ≤ (2 : ℕ) ^ n) :
      dist (z n i) (z n (i + k)) ≤ (k : ℝ) * (s / (2 : ℝ) ^ n) := by
    induction k with
    | zero => simp
    | succ k ih =>
        apply (dist_triangle (z n i) (z n (i + k)) (z n (i + (k + 1)))).trans
        rw [← Nat.add_assoc, Nat.cast_succ, add_mul, one_mul]
        exact add_le_add (ih (by omega)) (h n (i + k) (by omega))
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  simpa only [Nat.cast_add, add_sub_cancel_left] using hs k hj

private theorem floor_dyadic_refine {a : ℝ} (ha : 0 ≤ a) :
    let k := ⌊a⌋₊
    ⌊2 * a⌋₊ = 2 * k ∨ ⌊2 * a⌋₊ = 2 * k + 1 := by
  dsimp only
  have h₁ : 2 * ⌊a⌋₊ ≤ ⌊2 * a⌋₊ := by
    apply Nat.le_floor
    push_cast
    linarith only [Nat.floor_le ha]
  have h₂ : ⌊2 * a⌋₊ < 2 * ⌊a⌋₊ + 2 := by
    apply (Nat.floor_lt (mul_nonneg (by norm_num) ha)).mpr
    push_cast
    linarith only [Nat.lt_floor_add_one a]
  omega

theorem ChainCondition.exists_lipschitz_path (hCC : ChainCondition X) (x y : X) :
    ∃ θ : Path x y, ∀ t u : unitInterval,
      dist (θ t) (θ u) ≤ intrinsicDistance x y * |(t : ℝ) - (u : ℝ)| := by
  obtain ⟨z, he, hEven, hz⟩ := exists_intrinsic_dyadic_midpoint_chain hCC x y
  let s := intrinsicDistance x y
  let r (n : ℕ) := s / (2 : ℝ) ^ n
  have hs : 0 ≤ s := dist_nonneg.trans (dist_le_intrinsicDistance hCC x y)
  have hr (n : ℕ) : 0 ≤ r n := div_nonneg hs (by positivity)
  have hrSucc (n : ℕ) : r (n + 1) = r n / 2 := by dsimp [r]; rw [pow_succ, div_div]
  have hrLimit : Tendsto r atTop (𝓝 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    dsimp [r]
    simpa only [one_div, inv_pow, ← div_eq_mul_inv, mul_zero] using h.const_mul s
  have hStep (n k : ℕ) (h : k < (2 : ℕ) ^ n) : dist (z n k) (z n (k + 1)) ≤ r n :=
    (dist_le_intrinsicDistance hCC _ _).trans_eq (hz n k h)
  let k (n : ℕ) (t : unitInterval) := ⌊(t : ℝ) * (2 : ℝ) ^ n⌋₊
  let F (n : ℕ) (t : unitInterval) := z n (k n t)
  have hk (n : ℕ) (t : unitInterval) : k n t ≤ 2 ^ n := by
    have h : (k n t : ℝ) ≤ (2 : ℝ) ^ n :=
      (Nat.floor_le (by positivity [t.property.1])).trans
        (mul_le_of_le_one_left (by positivity) t.property.2)
    exact_mod_cast h
  have hNext (n : ℕ) (t : unitInterval) : dist (F n t) (F (n + 1) t) ≤ r (n + 1) := by
    have hk' : k (n + 1) t = 2 * k n t ∨ k (n + 1) t = 2 * k n t + 1 := by
      have hf := floor_dyadic_refine (a := (t : ℝ) * (2 : ℝ) ^ n) (by positivity [t.property.1])
      simpa only [k, pow_succ, mul_comm (2 : ℝ), mul_assoc] using hf
    rcases hk' with h | h
    · change dist (z n (k n t)) (z (n + 1) (k (n + 1) t)) ≤ _
      rw [h, hEven, dist_self]
      exact hr _
    · change dist (z n (k n t)) (z (n + 1) (k (n + 1) t)) ≤ _
      rw [h, ← hEven n (k n t)]
      apply hStep
      have hle := hk (n + 1) t
      rw [h] at hle
      omega
  have hTail (t : unitInterval) {n m : ℕ} (hnm : n ≤ m) :
      dist (F n t) (F m t) ≤ r n - r m := by
    induction m, hnm using Nat.le_induction with
    | base => simp only [dist_self, sub_self, le_refl]
    | succ m _ ih =>
        apply (dist_triangle (F n t) (F m t) (F (m + 1) t)).trans
        have hd := hNext m t
        rw [hrSucc m] at hd ⊢
        linarith only [ih, hd]
  have hLim (t : unitInterval) : ∃ v : X, Tendsto (fun n ↦ F n t) atTop (𝓝 v) := by
    apply cauchySeq_tendsto_of_complete
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hrLimit.eventually_lt_const hε)
    refine ⟨N, fun i hi j hj ↦ ?_⟩
    rcases le_total i j with hij | hij
    · exact ((hTail t hij).trans (sub_le_self _ (hr _))).trans_lt (hN i hi)
    · rw [dist_comm]
      exact ((hTail t hij).trans (sub_le_self _ (hr _))).trans_lt (hN j hj)
  choose θ hθ using hLim
  have hBound (t u : unitInterval) (htu : t ≤ u) :
      dist (θ t) (θ u) ≤ s * ((u : ℝ) - (t : ℝ)) := by
    have hlim := (hθ t).dist (hθ u)
    have hlim' : Tendsto (fun n ↦ s * ((u : ℝ) - (t : ℝ)) + r n) atTop
        (𝓝 (s * ((u : ℝ) - (t : ℝ)))) := by
      simpa only [add_zero] using hrLimit.const_add (s * ((u : ℝ) - (t : ℝ)))
    apply le_of_tendsto_of_tendsto hlim hlim'
    refine Eventually.of_forall fun n ↦ ?_
    have htu' : (t : ℝ) ≤ (u : ℝ) := htu
    have hmono : k n t ≤ k n u := Nat.floor_mono (mul_le_mul_of_nonneg_right htu' (by positivity))
    change dist (z n (k n t)) (z n (k n u)) ≤ _
    apply (dist_along_dyadic_chain hStep n (k n t) (k n u) hmono (hk n u)).trans
    have hF1 := Nat.floor_le (a := (u : ℝ) * (2 : ℝ) ^ n) (by positivity [u.property.1])
    have hF2 := Nat.lt_floor_add_one ((t : ℝ) * (2 : ℝ) ^ n)
    have hbound : (k n u : ℝ) - (k n t : ℝ) ≤
        ((u : ℝ) - (t : ℝ)) * (2 : ℝ) ^ n + 1 := by
      dsimp [k]
      linarith only [hF1, hF2]
    apply (mul_le_mul_of_nonneg_right hbound (hr n)).trans_eq
    dsimp [r]
    rw [add_mul, one_mul, mul_assoc, mul_comm ((2 : ℝ) ^ n), div_mul_cancel₀ _ (by positivity)]
    ring
  have hdist (t u : unitInterval) :
      dist (θ t) (θ u) ≤ s * |(t : ℝ) - (u : ℝ)| := by
    rcases le_total t u with h | h
    · have h' : (t : ℝ) ≤ (u : ℝ) := h
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr h')]
      exact hBound t u h
    · have h' : (u : ℝ) ≤ (t : ℝ) := h
      rw [dist_comm, abs_of_nonneg (sub_nonneg.mpr h')]
      exact hBound u t h
  have hLip : LipschitzWith ⟨s, hs⟩ θ := by
    apply lipschitzWith_iff_dist_le_mul.mpr
    intro t u
    change dist (θ t) (θ u) ≤ s * dist (t : ℝ) (u : ℝ)
    rw [Real.dist_eq]
    exact hdist t u
  have h0 : θ 0 = x := by
    apply tendsto_nhds_unique_of_forall (hθ 0) tendsto_const_nhds
    intro n
    change z n ⌊(0 : ℝ) * (2 : ℝ) ^ n⌋₊ = x
    rw [zero_mul, Nat.floor_zero]
    exact (he n).1
  have h1 : θ 1 = y := by
    apply tendsto_nhds_unique_of_forall (hθ 1) tendsto_const_nhds
    intro n
    change z n ⌊(1 : ℝ) * (2 : ℝ) ^ n⌋₊ = y
    rw [one_mul, ← Nat.cast_ofNat, ← Nat.cast_pow, Nat.floor_natCast]
    exact (he n).2
  exact ⟨⟨⟨θ, hLip.continuous⟩, h0, h1⟩, hdist⟩

end WalkDimensions
