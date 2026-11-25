import WalkDimensions.DyadicGrowth
import WalkDimensions.IntrinsicMidpoint

/-!
# Dyadic chains of exact midpoints
-/

namespace WalkDimensions

variable {X : Type*} {D : X → X → ℝ}

theorem exists_dyadic_midpoint_chain
    (hmid : ∀ x y : X, ∃ z : X, D x z = D x y / 2 ∧ D z y = D x y / 2)
    (x y : X) :
    ∃ z : ℕ → ℕ → X,
      (∀ n, z n 0 = x ∧ z n (2 ^ n) = y) ∧
      (∀ n k, z (n + 1) (2 * k) = z n k) ∧
      (∀ n k, k < (2 : ℕ) ^ n → D (z n k) (z n (k + 1)) = D x y / (2 : ℝ) ^ n) := by
  classical
  choose mid h₁ h₂ using hmid
  let z : ℕ → ℕ → X := Nat.rec (fun k ↦ if k = 0 then x else y)
    (fun _ a k ↦ if k % 2 = 0 then a (k / 2) else mid (a (k / 2)) (a (k / 2 + 1)))
  have hEven (n k : ℕ) : z (n + 1) (2 * k) = z n k := by
    change (if (2 * k) % 2 = 0 then z n ((2 * k) / 2) else _) = _
    rw [ite_eq_left (by omega), show 2 * k / 2 = k by omega]
  have hOdd (n k : ℕ) : z (n + 1) (2 * k + 1) = mid (z n k) (z n (k + 1)) := by
    change (if (2 * k + 1) % 2 = 0 then _ else
      mid (z n ((2 * k + 1) / 2)) (z n ((2 * k + 1) / 2 + 1))) = _
    rw [ite_eq_right (by omega), show (2 * k + 1) / 2 = k by omega]
  refine ⟨z, ?_, hEven, ?_⟩
  · intro n
    induction n with
    | zero => exact ⟨rfl, rfl⟩
    | succ n ih =>
        have he : (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ, mul_comm]
        rw [he, hEven n _, show z (n + 1) 0 = z n 0 from hEven n 0]
        exact ih
  · intro n
    induction n with
    | zero =>
        intro k hk
        have he : k = 0 := by simpa using hk
        subst k
        change D x y = D x y / (2 : ℝ) ^ 0
        rw [pow_zero, div_one]
    | succ n ih =>
        intro k hk
        let j := k / 2
        have hj : j < 2 ^ n := by dsimp [j]; rw [pow_succ] at hk; omega
        have hscale : D x y / (2 : ℝ) ^ (n + 1) = D x y / (2 : ℝ) ^ n / 2 := by
          rw [pow_succ, div_div]
        rw [hscale, ← ih j hj]
        by_cases hk' : k % 2 = 0
        · have he : k = 2 * j := by dsimp [j]; omega
          rw [he, hEven, hOdd, h₁]
        · have he : k = 2 * j + 1 := by dsimp [j]; omega
          rw [he, hOdd, show 2 * j + 1 + 1 = 2 * (j + 1) by omega, hEven, h₂]

theorem exists_intrinsic_dyadic_midpoint_chain [MetricSpace X] [ProperSpace X]
    (hCC : ChainCondition X) (x y : X) :
    ∃ z : ℕ → ℕ → X,
      (∀ n, z n 0 = x ∧ z n (2 ^ n) = y) ∧
      (∀ n k, z (n + 1) (2 * k) = z n k) ∧
      (∀ n k, k < (2 : ℕ) ^ n →
        intrinsicDistance (z n k) (z n (k + 1)) = intrinsicDistance x y / (2 : ℝ) ^ n) :=
  exists_dyadic_midpoint_chain (exists_intrinsicDistance_midpoint hCC) x y

end WalkDimensions
