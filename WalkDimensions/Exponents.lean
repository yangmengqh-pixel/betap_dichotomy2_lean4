import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith

/-!
# Exponent comparisons and dichotomies

Scalar steps in Sections 4–7 of arXiv:2611.02422v1.
-/

open Set

namespace WalkDimensions

/-- The normalized exponent in Theorem 2.5. -/
noncomputable def gamma (d : ℝ) (β : ℝ → ℝ) (p : ℝ) : ℝ :=
  (β p - d) / (p - 1)

theorem gamma_eq_one_iff {d p : ℝ} {β : ℝ → ℝ} (hp : 1 < p) :
    gamma d β p = 1 ↔ β p = d + p - 1 := by
  rw [gamma, div_eq_iff (sub_pos.mpr hp).ne', one_mul]
  constructor <;> intro h <;> linarith

theorem gamma_le_one {d p : ℝ} {β : ℝ → ℝ} (hp : 1 < p)
    (hβ : β p ≤ d + p - 1) : gamma d β p ≤ 1 := by
  rw [gamma, div_le_iff₀ (sub_pos.mpr hp), one_mul]
  linarith

/-- The interpolation exponent in Lemma 5.2. -/
theorem gamma_le_gamma_iff {d p q : ℝ} {β : ℝ → ℝ} (hq : 1 < q) :
    gamma d β p ≤ gamma d β q ↔ (q - 1) * gamma d β p + d ≤ β q := by
  change gamma d β p ≤ (β q - d) / (q - 1) ↔ _
  rw [le_div_iff₀ (sub_pos.mpr hq), mul_comm (gamma d β p)]
  constructor <;> intro h <;> linarith

/-- The strict comparison (5.1) for the range below the Hausdorff dimension. -/
theorem gamma_lt_gamma_of_beta_le_dimension {d p q : ℝ} {β : ℝ → ℝ}
    (hp : 1 < p) (hpq : p < q) (hβpq : β p < β q) (hβp : β p ≤ d) :
    gamma d β p < gamma d β q := by
  have hq : 1 < q := hp.trans hpq
  change (β p - d) / (p - 1) < (β q - d) / (q - 1)
  calc
    (β p - d) / (p - 1) ≤ (β p - d) / (q - 1) :=
      by
        rw [div_le_div_iff₀ (sub_pos.mpr hp) (sub_pos.mpr hq)]
        have h := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hβp) (sub_nonneg.mpr hpq.le)
        linarith
    _ < (β q - d) / (q - 1) :=
      div_lt_div_of_pos_right (sub_lt_sub_right hβpq d) (sub_pos.mpr hq)

/-- The final order argument in Section 4. A nonempty parameter interval is
needed for the alternatives to be exclusive. -/
theorem beta_ratio_dichotomy_of_pairwise {I : Set ℝ} {β : ℝ → ℝ}
    (hne : I.Nonempty) (hp : ∀ p ∈ I, 0 < p)
    (hlower : ∀ p ∈ I, p ≤ β p)
    (hendpoint : ∀ p ∈ I, β p = p → ∀ q ∈ I, β q = q)
    (hanti : AntitoneOn (fun p ↦ β p / p) I)
    (hstrict : ∀ p ∈ I, ∀ q ∈ I, p < q → β q / q = β p / p → β p = p) :
    Xor (∀ p ∈ I, β p = p)
      ((∀ p ∈ I, 1 < β p / p) ∧ StrictAntiOn (fun p ↦ β p / p) I) := by
  classical
  by_cases h : ∀ p ∈ I, β p = p
  · left
    refine ⟨h, fun h' ↦ ?_⟩
    obtain ⟨p, hpI⟩ := hne
    have := h'.1 p hpI
    rw [h p hpI, div_self (hp p hpI).ne'] at this
    exact lt_irrefl _ this
  · right
    refine ⟨?_, h⟩
    constructor
    · intro p hpI
      have hnep : β p ≠ p := fun he ↦ h (hendpoint p hpI he)
      exact (one_lt_div₀ (hp p hpI)).2 ((hlower p hpI).lt_of_ne (Ne.symm hnep))
    · intro p hpI q hqI hpq
      refine (hanti hpI hqI hpq.le).lt_of_ne ?_
      exact fun he ↦ h (hendpoint p hpI (hstrict p hpI q hqI hpq he))

/-- The last dichotomy in Theorem 2.5, from its endpoint propagation and
strict comparison. -/
theorem gamma_dichotomy_of_pairwise {I : Set ℝ} {d : ℝ} {β : ℝ → ℝ}
    (hne : I.Nonempty) (hp : ∀ p ∈ I, 1 < p)
    (hupper : ∀ p ∈ I, β p ≤ d + p - 1)
    (hendpoint : ∀ p ∈ I, gamma d β p = 1 → ∀ q ∈ I, gamma d β q = 1)
    (hstrict : ∀ p ∈ I, ∀ q ∈ I, p < q → gamma d β p < 1 → gamma d β p < gamma d β q) :
    Xor (∀ p ∈ I, β p = d + p - 1)
      ((∀ p ∈ I, gamma d β p < 1) ∧ StrictMonoOn (gamma d β) I) := by
  classical
  by_cases h : ∀ p ∈ I, β p = d + p - 1
  · left
    refine ⟨h, fun h' ↦ ?_⟩
    obtain ⟨p, hpI⟩ := hne
    exact (h'.1 p hpI).ne ((gamma_eq_one_iff (hp p hpI)).2 (h p hpI))
  · right
    have hlt : ∀ p ∈ I, gamma d β p < 1 := by
      intro p hpI
      refine (gamma_le_one (hp p hpI) (hupper p hpI)).lt_of_ne ?_
      intro he
      exact h fun q hqI ↦ (gamma_eq_one_iff (hp q hqI)).1 (hendpoint p hpI he q hqI)
    exact ⟨⟨hlt, fun p hpI q hqI hpq ↦ hstrict p hpI q hqI hpq (hlt p hpI)⟩, h⟩

end WalkDimensions
