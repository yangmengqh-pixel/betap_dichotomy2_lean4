import WalkDimensions.SawtoothPeriod

/-!
# Affine pieces of the sawtooth
-/

open Set

namespace WalkDimensions

/-- A closed affine piece on either side of a zero of the sawtooth. -/
def sawtoothCell (r : ℝ) (i : ℤ × Bool) : Set ℝ :=
  if i.2 then Icc (2 * r * (i.1 : ℝ)) (2 * r * (i.1 : ℝ) + r)
  else Icc (2 * r * (i.1 : ℝ) - r) (2 * r * (i.1 : ℝ))

def sawtoothSign (i : ℤ × Bool) : ℝ := if i.2 then 1 else -1

def sawtoothOffsetIndex (i : ℤ × Bool) : ℤ :=
  if i.2 then -2 * i.1 else 2 * i.1

theorem sawtoothSign_eq (i : ℤ × Bool) :
    sawtoothSign i = 1 ∨ sawtoothSign i = -1 := by
  rcases i with ⟨j, b⟩
  cases b <;> simp [sawtoothSign]

theorem isClosed_sawtoothCell (r : ℝ) (i : ℤ × Bool) : IsClosed (sawtoothCell r i) := by
  rcases i with ⟨j, b⟩
  cases b <;> simpa only [sawtoothCell, Bool.false_eq_true, ↓reduceIte] using
    (isClosed_Icc : IsClosed (Icc (_ : ℝ) _))

theorem sawtooth_eq_affine_of_mem_cell {r t : ℝ} (hr : 0 < r) {i : ℤ × Bool}
    (ht : t ∈ sawtoothCell r i) :
    sawtooth r t = sawtoothSign i * t + r * (sawtoothOffsetIndex i : ℝ) := by
  rcases i with ⟨j, b⟩
  let z := 2 * r * (j : ℝ)
  have hshift : sawtooth r t = sawtooth r (t - z) := by
    simpa only [z, sub_add_cancel] using sawtooth_add_period r (t - z) j
  rw [hshift]
  cases b
  · change z - r ≤ t ∧ t ≤ z at ht
    have ha : t - z ≤ 0 := sub_nonpos.mpr ht.2
    have hbd : |t - z| ≤ r := by rw [abs_of_nonpos ha]; linarith only [ht.1]
    rw [sawtooth_eq_abs_of_abs_le hr hbd, abs_of_nonpos ha]
    simp only [sawtoothSign, sawtoothOffsetIndex, Bool.false_eq_true, ↓reduceIte, Int.cast_mul,
      Int.cast_ofNat]
    dsimp [z]
    ring
  · change z ≤ t ∧ t ≤ z + r at ht
    have ha : 0 ≤ t - z := sub_nonneg.mpr ht.1
    have hbd : |t - z| ≤ r := by rw [abs_of_nonneg ha]; linarith only [ht.2]
    rw [sawtooth_eq_abs_of_abs_le hr hbd, abs_of_nonneg ha]
    simp only [sawtoothSign, sawtoothOffsetIndex, ↓reduceIte, Int.cast_mul, Int.cast_neg,
      Int.cast_ofNat]
    dsimp [z]
    ring

theorem exists_mem_sawtoothCell {r : ℝ} (hr : 0 < r) (t : ℝ) :
    ∃ i, t ∈ sawtoothCell r i := by
  let j := ⌊t / (2 * r)⌋
  have hr₂ : 0 < 2 * r := by positivity
  have hlo := (le_div_iff₀ hr₂).mp (Int.floor_le (t / (2 * r)))
  have hup := (div_lt_iff₀ hr₂).mp (Int.lt_floor_add_one (t / (2 * r)))
  change (j : ℝ) * (2 * r) ≤ t at hlo
  change t < ((j : ℝ) + 1) * (2 * r) at hup
  by_cases h : t ≤ 2 * r * (j : ℝ) + r
  · exact ⟨(j, true), ⟨by linarith only [hlo, mul_comm (j : ℝ) (2 * r)], h⟩⟩
  · refine ⟨(j + 1, false), ?_⟩
    change 2 * r * ((j + 1 : ℤ) : ℝ) - r ≤ t ∧ t ≤ 2 * r * ((j + 1 : ℤ) : ℝ)
    push_cast
    have h' := (lt_of_not_ge h).le
    rw [mul_comm (2 * r) ((j : ℝ) + 1)]
    constructor <;> linarith only [h', hup.le, mul_comm (2 * r) (j : ℝ)]

theorem iUnion_sawtoothCell {r : ℝ} (hr : 0 < r) :
    (⋃ i : ℤ × Bool, sawtoothCell r i) = univ := by
  apply eq_univ_of_forall
  exact fun t ↦ mem_iUnion.mpr (exists_mem_sawtoothCell hr t)

theorem mem_interior_sawtoothCell_or_eq_grid {r t : ℝ} (i : ℤ × Bool)
    (h : t ∈ sawtoothCell r i) :
    t ∈ interior (sawtoothCell r i) ∨ ∃ j : ℤ, t = r * (j : ℝ) := by
  rcases i with ⟨j, b⟩
  cases b
  · change t ∈ Icc (2 * r * (j : ℝ) - r) (2 * r * (j : ℝ)) at h
    change t ∈ interior (Icc (2 * r * (j : ℝ) - r) (2 * r * (j : ℝ))) ∨ _
    rw [interior_Icc]
    rcases h.1.lt_or_eq with h₁ | h₁
    · rcases h.2.lt_or_eq with h₂ | h₂
      · exact Or.inl ⟨h₁, h₂⟩
      · exact Or.inr ⟨2 * j, by push_cast; nlinarith only [h₂]⟩
    · exact Or.inr ⟨2 * j - 1, by push_cast; nlinarith only [h₁]⟩
  · change t ∈ Icc (2 * r * (j : ℝ)) (2 * r * (j : ℝ) + r) at h
    change t ∈ interior (Icc (2 * r * (j : ℝ)) (2 * r * (j : ℝ) + r)) ∨ _
    rw [interior_Icc]
    rcases h.1.lt_or_eq with h₁ | h₁
    · rcases h.2.lt_or_eq with h₂ | h₂
      · exact Or.inl ⟨h₁, h₂⟩
      · exact Or.inr ⟨2 * j + 1, by push_cast; nlinarith only [h₂]⟩
    · exact Or.inr ⟨2 * j, by push_cast; nlinarith only [h₁]⟩

theorem sawtooth_of_grid {r : ℝ} (hr : 0 < r) (j : ℤ) :
    sawtooth r (r * (j : ℝ)) = 0 ∨ sawtooth r (r * (j : ℝ)) = r := by
  let k := j / 2
  have hj : j = 2 * k ∨ j = 2 * k + 1 := by dsimp [k]; omega
  rcases hj with hj | hj
  · left
    have he : r * (j : ℝ) = 0 + 2 * r * (k : ℝ) := by rw [hj]; push_cast; ring
    rw [he, sawtooth_add_period, sawtooth_zero]
  · right
    have he : r * (j : ℝ) = r + 2 * r * (k : ℝ) := by rw [hj]; push_cast; ring
    rw [he, sawtooth_add_period, sawtooth_eq_abs_of_abs_le hr]
    · exact abs_of_nonneg hr.le
    · rw [abs_of_nonneg hr.le]

end WalkDimensions
