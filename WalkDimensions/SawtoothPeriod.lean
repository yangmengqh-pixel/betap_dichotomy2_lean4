import WalkDimensions.DyadicOscillation

/-!
# Translation and reflection of the oscillation grid
-/

open Set Metric

namespace WalkDimensions

theorem sawtooth_add_period (δ t : ℝ) (j : ℤ) :
    sawtooth δ (t + 2 * δ * (j : ℝ)) = sawtooth δ t := by
  let G := range fun k : ℤ ↦ (2 * δ) * (k : ℝ)
  let Φ (x : ℝ) := x + 2 * δ * (j : ℝ)
  have hΦ : Isometry Φ := isometry_add_right _
  have hG : Φ '' G = G := by
    ext x
    constructor
    · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
      exact ⟨k + j, by push_cast; dsimp [Φ]; ring⟩
    · rintro ⟨k, rfl⟩
      refine ⟨_, ⟨k - j, rfl⟩, ?_⟩
      push_cast
      dsimp [Φ]
      ring
  change infDist (Φ t) G = infDist t G
  simpa only [hG] using (infDist_image (x := t) (t := G) hΦ)

theorem sawtooth_neg (δ t : ℝ) : sawtooth δ (-t) = sawtooth δ t := by
  let G := range fun k : ℤ ↦ (2 * δ) * (k : ℝ)
  let Φ (x : ℝ) := -x
  have hG : Φ '' G = G := by
    ext x
    constructor
    · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
      exact ⟨-k, by simp only [Int.cast_neg, mul_neg, Φ]⟩
    · rintro ⟨k, rfl⟩
      exact ⟨_, ⟨-k, rfl⟩, by simp only [Int.cast_neg, mul_neg, neg_neg, Φ]⟩
  change infDist (Φ t) G = infDist t G
  have hΦ : Isometry Φ := isometry_neg
  simpa only [hG] using (infDist_image (x := t) (t := G) hΦ)

theorem oscillationWidth_add (m n : ℕ) :
    oscillationWidth (m + n) = oscillationWidth m * oscillationWidth n :=
  pow_add _ _ _

theorem two_mul_oscillationWidth_pow (n : ℕ) :
    oscillationWidth n * (2 : ℝ) ^ n = 1 := by
  rw [oscillationWidth, ← mul_pow]
  norm_num

theorem sawtooth_add_dyadic {m n : ℕ} (hmn : m < n) (t : ℝ) (j : ℤ) :
    sawtooth (oscillationWidth n) (t + oscillationWidth m * (j : ℝ)) =
      sawtooth (oscillationWidth n) t := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hmn
  subst n
  have he : oscillationWidth m * (j : ℝ) =
      2 * oscillationWidth (m + 1 + k) * (((2 : ℤ) ^ k * j : ℤ) : ℝ) := by
    push_cast
    rw [oscillationWidth_add (m + 1) k, oscillationWidth_succ]
    calc
      _ = oscillationWidth m * (oscillationWidth k * (2 : ℝ) ^ k) * (j : ℝ) := by
          rw [two_mul_oscillationWidth_pow, mul_one]
      _ = _ := by ring
  rw [he]
  exact sawtooth_add_period _ _ _

end WalkDimensions
