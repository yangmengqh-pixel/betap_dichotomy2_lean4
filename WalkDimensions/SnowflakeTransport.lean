import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Transport bounds for small links in a snowflaked metric

A Hölder potential can be approximated by an ordinary Lipschitz potential.
The boundary mass controls the approximation error, and short links make
the resulting transportation cost small.
-/

namespace WalkDimensions

open Finset

variable {V : Type*} [Fintype V]

private theorem sum_transport_boundary (F : V → V → ℝ) (H : V → ℝ) :
    (∑ j, (∑ i, (F i j - F j i)) * H j) =
      ∑ i, ∑ j, F i j * (H j - H i) := by
  simp only [sum_sub_distrib, sub_mul, sum_mul, mul_sub]
  rw [sum_comm (f := fun j i ↦ F i j * H j)]

/-- An infimum of distance cones gives a Lipschitz approximation at a
chosen resolution. -/
private theorem exists_lipschitz_approximation [Nonempty V]
    {D : V → V → ℝ} (hD₀ : ∀ i j, 0 ≤ D i j) (hself : ∀ i, D i i = 0)
    (hsymm : ∀ i j, D i j = D j i) (htri : ∀ i j k, D i k ≤ D i j + D j k)
    {c C : ℝ} (hc : 0 ≤ c) (hc₁ : c ≤ 1) (hC : 0 ≤ C)
    (H : V → ℝ) (hH : ∀ i j, |H i - H j| ≤ C * D i j ^ c)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ G : V → ℝ, (∀ i, |H i - G i| ≤ C * ε ^ c) ∧
      ∀ i j, |G i - G j| ≤ (C * ε ^ (c - 1)) * D i j := by
  let L := C * ε ^ (c - 1)
  have hL : 0 ≤ L := mul_nonneg hC (Real.rpow_nonneg hε.le _)
  let S (j : V) := Set.range fun i ↦ H i + L * D i j
  let G (j : V) := sInf (S j)
  have hSne (j : V) : (S j).Nonempty := Set.range_nonempty _
  have hSbdd (j : V) : BddBelow (S j) := (Set.finite_range _).bddBelow
  have hGle (j : V) : G j ≤ H j := by
    apply (csInf_le (hSbdd j) (Set.mem_range_self j)).trans_eq
    rw [hself, mul_zero, add_zero]
  have happrox (i j : V) : H j - C * ε ^ c ≤ H i + L * D i j := by
    have hh := (le_abs_self (H j - H i)).trans (hH j i)
    rw [hsymm j i] at hh
    by_cases hd : D i j ≤ ε
    · have hb := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (hD₀ i j) hd hc) hC
      have hp := mul_nonneg hL (hD₀ i j)
      linarith
    · have hdpos : 0 < D i j := hε.trans (lt_of_not_ge hd)
      have hpow := Real.rpow_le_rpow_of_nonpos hε (le_of_not_ge hd) (sub_nonpos.mpr hc₁)
      have hb : C * D i j ^ c ≤ L * D i j := by
        have hh' : D i j ^ c = D i j ^ (c - 1) * D i j := by
          calc
            _ = D i j ^ ((c - 1) + 1) := by rw [sub_add_cancel]
            _ = D i j ^ (c - 1) * D i j := by rw [Real.rpow_add hdpos, Real.rpow_one]
        rw [hh', ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC) hdpos.le
      have hp := mul_nonneg hC (Real.rpow_nonneg hε.le c)
      linarith
  refine ⟨G, fun j ↦ ?_, fun i j ↦ ?_⟩
  · have hlo : H j - C * ε ^ c ≤ G j := by
      apply le_csInf (hSne j)
      rintro _ ⟨i, rfl⟩
      exact happrox i j
    rw [abs_of_nonneg (sub_nonneg.mpr (hGle j))]
    linarith
  · have hpair (i j : V) : G j - L * D i j ≤ G i := by
      apply le_csInf (hSne i)
      rintro _ ⟨k, rfl⟩
      have hle := csInf_le (hSbdd j) (Set.mem_range_self (f := fun k ↦ H k + L * D k j) k)
      have hTriangle := mul_le_mul_of_nonneg_left (htri k i j) hL
      dsimp only [G, S] at hle ⊢
      rw [mul_add] at hTriangle
      linarith
    have h₁ := hpair i j
    have h₂ := hpair j i
    rw [hsymm j i] at h₂
    exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem transport_pairing_le_of_small_links [Nonempty V]
    {D : V → V → ℝ} (hD₀ : ∀ i j, 0 ≤ D i j) (hself : ∀ i, D i i = 0)
    (hsymm : ∀ i j, D i j = D j i) (htri : ∀ i j k, D i k ≤ D i j + D j k)
    {c C : ℝ} (hc : 0 < c) (hc₁ : c < 1) (hC : 0 ≤ C)
    (H : V → ℝ) (hH : ∀ i j, |H i - H j| ≤ C * D i j ^ c)
    (F : V → V → ℝ) (hF : ∀ i j, 0 ≤ F i j)
    {δ : ℝ} (hδ : 0 < δ) (hmesh : ∀ i j, 0 < F i j → D i j ≤ δ)
    {ε : ℝ} (hε : 0 < ε) :
    (∑ j, (∑ i, (F i j - F j i)) * H j) ≤
      (C * ε ^ c) * (∑ j, |∑ i, (F i j - F j i)|) +
        (C * ε ^ (c - 1) * δ ^ (1 - c)) * (∑ i, ∑ j, F i j * D i j ^ c) := by
  obtain ⟨G, hG, hLip⟩ :=
    exists_lipschitz_approximation hD₀ hself hsymm htri hc.le hc₁.le hC H hH hε
  let B (j : V) := ∑ i, (F i j - F j i)
  let L := C * ε ^ (c - 1)
  have hL : 0 ≤ L := mul_nonneg hC (Real.rpow_nonneg hε.le _)
  have hCost (i j : V) :
      F i j * (G j - G i) ≤ (L * δ ^ (1 - c)) * (F i j * D i j ^ c) := by
    by_cases hf : F i j = 0
    · simp [hf]
    have hd := hmesh i j ((hF i j).lt_of_ne (Ne.symm hf))
    have hpow := Real.rpow_le_rpow (hD₀ i j) hd (sub_nonneg.mpr hc₁.le)
    have hsplit : D i j ≤ δ ^ (1 - c) * D i j ^ c := by
      calc
        _ = D i j ^ (1 - c) * D i j ^ c := by
          rw [← Real.rpow_add' (hD₀ i j), sub_add_cancel, Real.rpow_one]
          norm_num
        _ ≤ _ := mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg (hD₀ i j) c)
    have hdif := (le_abs_self (G j - G i)).trans (hLip j i)
    rw [hsymm j i] at hdif
    calc
      _ ≤ F i j * (L * D i j) := mul_le_mul_of_nonneg_left hdif (hF i j)
      _ ≤ F i j * (L * (δ ^ (1 - c) * D i j ^ c)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsplit hL) (hF i j)
      _ = _ := by ring
  have hboundary :
      (∑ j, B j * (H j - G j)) ≤ (C * ε ^ c) * ∑ j, |B j| := by
    rw [mul_sum]
    apply sum_le_sum
    intro j _
    calc
      _ ≤ |B j * (H j - G j)| := le_abs_self _
      _ = |B j| * |H j - G j| := abs_mul _ _
      _ ≤ |B j| * (C * ε ^ c) := mul_le_mul_of_nonneg_left (hG j) (abs_nonneg _)
      _ = _ := mul_comm _ _
  have hcost : (∑ j, B j * G j) ≤
      (L * δ ^ (1 - c)) * (∑ i, ∑ j, F i j * D i j ^ c) := by
    dsimp only [B]
    rw [sum_transport_boundary, mul_sum]
    exact sum_le_sum fun i _ ↦ (sum_le_sum fun j _ ↦ hCost i j).trans_eq (mul_sum _ _ _).symm
  have hsplit : (∑ j, B j * H j) = (∑ j, B j * (H j - G j)) + ∑ j, B j * G j := by
    simp only [mul_sub, sum_sub_distrib, sub_add_cancel]
  rw [← show (∑ j, B j * H j) = _ from rfl, hsplit]
  exact add_le_add hboundary hcost

end WalkDimensions
