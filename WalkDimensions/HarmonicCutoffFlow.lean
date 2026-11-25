import WalkDimensions.HarmonicCutoffPairing

/-!
# Boundary, payoff and cost estimates for the harmonic coupling
-/

open Filter Function MeasureTheory Set
open scoped ENNReal

namespace WalkDimensions.PEnergy.CompactCore

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [LocallyCompactSpace X] {m : Measure X} [IsFiniteMeasureOnCompacts m] {p : ℝ} {E : PEnergy m p}
  {V : Type*} [Fintype V]

theorem exists_harmonic_cutoff_flow (u χ : E.CompactCore) (φ : V → E.CompactCore)
    {B S : Set X} (hB : MeasurableSet B) (hS : MeasurableSet S) (hSB : S ⊆ B)
    (Bφ : V → Set X) (hBφ : ∀ i, MeasurableSet (Bφ i))
    (hχ : ∀ x, χ.toFun x ∈ Icc (0 : ℝ) 1) (hφ : ∀ i x, 0 ≤ (φ i).toFun x)
    (hSuppχ : support χ.toFun ⊆ B) (hSuppφ : ∀ i, support (φ i).toFun ⊆ Bφ i)
    (hPartition : ∀ x ∈ B, ∑ i, (φ i).toFun x = 1)
    (hHarmonic : ∀ v : E.CompactCore, support v.toFun ⊆ B →
      E.energyDerivativeMeasure u.domainElement v.domainElement univ = 0)
    (a : V → ℝ) {o C₁ C₂ : ℝ} (ha : ∀ i, |a i| ≤ C₁)
    (hApprox : ∀ x ∈ B, |u.toFun x - o - ∑ i, a i * (φ i).toFun x| ≤ C₂) :
    let D := fun v : E.CompactCore ↦ E.energyDerivativeMeasure u.domainElement v.domainElement
    let T := ∑ j, ((D (φ j)).totalVariation (B \ S)).toReal
    let Q := ((D χ).totalVariation B).toReal
    ∃ F : V → V → ℝ, (∀ i j, 0 ≤ F i j) ∧ (∀ i j, 0 < F i j → (Bφ i ∩ Bφ j).Nonempty) ∧
      (∑ i, ∑ j, F i j) ≤ 2 * ∑ j, ((D (φ j)).totalVariation (S ∩ Bφ j)).toReal ∧
      (∑ j, |∑ i, (F i j - F j i)|) ≤ T + Q ∧
      weightSignedMeasure (D u) χ.toFun B - C₂ * Q - C₁ * T ≤
        ∑ j, (∑ i, (F i j - F j i)) * a j := by
  classical
  let D (v : E.CompactCore) := E.energyDerivativeMeasure u.domainElement v.domainElement
  let Z := B \ S
  have hZ : MeasurableSet Z := hB.diff hS
  let T := ∑ j, ((D (φ j)).totalVariation Z).toReal
  let Q := ((D χ).totalVariation B).toReal
  let L (i j : V) := weightSignedMeasure (D (φ j)) (χ.mul (φ i)).toFun S
  let L' (i j : V) := weightSignedMeasure (D (φ j)) (χ.mul (φ i)).toFun (S ∩ Bφ j)
  let F (i j : V) := max (L i j - L j i) 0
  have hL (i j : V) : L i j = L' i j := by
    apply weightSignedMeasure_apply_inter_of_variation _ ((χ.mul (φ i)).integrable_vectorMeasure _)
      hS (hBφ j)
    exact u.energyDerivativeMeasure_variation_zero_of_const_on (φ j) (hS.diff (hBφ j))
      (fun _ hx ↦ notMem_support.mp (fun hy ↦ hx.2 (hSuppφ j hy)))
  have hL₀ (i j : V) (h : ¬ (Bφ i ∩ Bφ j).Nonempty) : L i j = 0 := by
    rw [hL]
    apply weightSignedMeasure_apply_eq_zero_of_forall _ ((χ.mul (φ i)).integrable_vectorMeasure _)
      (hS.inter (hBφ j))
    intro x hx
    have hx' : x ∉ support (φ i).toFun := fun hv ↦ h ⟨x, hSuppφ i hv, hx.2⟩
    rw [mul_apply, notMem_support.mp hx', mul_zero]
  have hMax (i j : V) : F i j - F j i = L i j - L j i := by
    dsimp only [F]
    rcases le_total (L i j) (L j i) with h | h
    · rw [max_eq_right (sub_nonpos.mpr h), max_eq_left (sub_nonneg.mpr h)]
      ring
    · rw [max_eq_left (sub_nonneg.mpr h), max_eq_right (sub_nonpos.mpr h), sub_zero]
  have hRow (j : V) : (∑ i, (F i j - F j i)) = weightSignedMeasure (D (φ j)) χ.toFun S := by
    simp only [hMax]
    exact harmonic_cutoff_row_sum u χ φ hS hSB hPartition j
  have hDiff (j : V) := weighted_harmonic_cutoff_eq u χ (φ j) hB hS hSB hSuppχ hHarmonic
  have hZBound (j : V) : |weightSignedMeasure (D (φ j)) χ.toFun Z| ≤
      ((D (φ j)).totalVariation Z).toReal := by
    simpa only [one_mul] using abs_weightSignedMeasure_apply_le (D (φ j))
      (χ.integrable_vectorMeasure _) hZ (fun x _ ↦ (abs_of_nonneg (hχ x).1).trans_le (hχ x).2)
  refine ⟨F, fun _ _ ↦ le_max_right _ _, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    by_contra h
    have hji : ¬ (Bφ j ∩ Bφ i).Nonempty := by rwa [inter_comm]
    have hz : F i j = 0 := by simp only [F, hL₀ i j h, hL₀ j i hji, sub_zero, max_self]
    exact hij.ne' hz
  · have hEach (j : V) : (∑ i, |L i j|) ≤ ((D (φ j)).totalVariation (S ∩ Bφ j)).toReal := by
      simp only [hL]
      apply sum_abs_weightSignedMeasure_apply_le _ Finset.univ
        (fun i _ ↦ (χ.mul (φ i)).integrable_vectorMeasure _) (hS.inter (hBφ j))
      · intro i _ x _
        rw [mul_apply]
        exact mul_nonneg (hχ x).1 (hφ i x)
      · intro x hx
        simp_rw [mul_apply, ← Finset.mul_sum, hPartition x (hSB hx.1), mul_one]
        exact (hχ x).2
    have hPt (i j : V) : F i j ≤ |L i j| + |L j i| := by
      apply max_le
      · exact (le_abs_self _).trans (abs_sub _ _)
      · positivity
    calc
      _ ≤ ∑ i, ∑ j, (|L i j| + |L j i|) :=
        Finset.sum_le_sum (fun i _ ↦ Finset.sum_le_sum (fun j _ ↦ hPt i j))
      _ = 2 * ∑ j, ∑ i, |L i j| := by
        simp only [Finset.sum_add_distrib]
        rw [Finset.sum_comm (f := fun i j ↦ |L i j|), two_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ ↦ hEach j)) (by norm_num)
  · have hEach (j : V) : |weightSignedMeasure (D (φ j)) χ.toFun S| ≤
        ((D (φ j)).totalVariation Z).toReal + |weightSignedMeasure (D χ) (φ j).toFun B| := by
      rw [hDiff]
      exact (abs_sub _ _).trans (by rw [abs_neg]; gcongr; exact hZBound j)
    simp only [hRow]
    apply (Finset.sum_le_sum (fun j _ ↦ hEach j)).trans
    rw [Finset.sum_add_distrib]
    apply add_le_add_right
    exact sum_abs_weightSignedMeasure_apply_le _ Finset.univ
      (fun j _ ↦ (φ j).integrable_vectorMeasure _) hB (fun j _ x _ ↦ hφ j x)
      (fun x hx ↦ (hPartition x hx).le)
  · let w := finsetSum Finset.univ (fun j ↦ (φ j).smul (a j))
    let LZ := ∑ j, weightSignedMeasure (D (φ j)) χ.toFun Z * a j
    have hLT : LZ ≤ C₁ * T := by
      rw [show T = ∑ j, ((D (φ j)).totalVariation Z).toReal by rfl, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      calc
        _ ≤ |weightSignedMeasure (D (φ j)) χ.toFun Z * a j| := le_abs_self _
        _ = _ := abs_mul _ _
        _ ≤ ((D (φ j)).totalVariation Z).toReal * C₁ :=
          mul_le_mul (hZBound j) (ha j) (abs_nonneg _) ENNReal.toReal_nonneg
        _ = _ := mul_comm _ _
    have hχ₀ : D χ B = 0 := (u.energyDerivativeMeasure_apply_eq_univ_of_support χ hB hSuppχ).trans
      (hHarmonic χ hSuppχ)
    let e : X → ℝ := u.toFun - (fun _ ↦ o) - w.toFun
    have hIₒ : (D χ).Integrable (fun _ : X ↦ o) :=
      integrable_vectorMeasure_of_bounded _ measurable_const (fun _ ↦ le_rfl)
    have hI := ((u.integrable_vectorMeasure (D χ)).sub hIₒ).sub (w.integrable_vectorMeasure (D χ))
    have hE (x : X) (hx : x ∈ B) : |e x| ≤ C₂ := hApprox x hx
    have hErr := abs_weightSignedMeasure_apply_le (D χ) hI hB hE
    have hErrEq : weightSignedMeasure (D χ) e B =
        weightSignedMeasure (D χ) u.toFun B - weightSignedMeasure (D χ) w.toFun B := by
      dsimp only [e]
      rw [weightSignedMeasure_sub _ ((u.integrable_vectorMeasure _).sub hIₒ)
        (w.integrable_vectorMeasure _), weightSignedMeasure_sub _ (u.integrable_vectorMeasure _) hIₒ,
        sub_apply, sub_apply, weightSignedMeasure_apply_const _ _ hB, hχ₀, mul_zero, sub_zero]
    have hU := weighted_harmonic_cutoff_eq u χ u hB hB (subset_refl _) hSuppχ hHarmonic
    change weightSignedMeasure (D u) χ.toFun B = -weightSignedMeasure (D u) χ.toFun (B \ B) -
      weightSignedMeasure (D χ) u.toFun B at hU
    simp only [Set.sdiff_self, VectorMeasure.empty, neg_zero, zero_sub] at hU
    have hwS := weighted_derivative_interpolant u χ φ a S
    have hwZ := weighted_derivative_interpolant u χ φ a Z
    change (∑ j, weightSignedMeasure (D (φ j)) χ.toFun S * a j) = weightSignedMeasure (D w) χ.toFun S at hwS
    change LZ = weightSignedMeasure (D w) χ.toFun Z at hwZ
    have hw := weighted_harmonic_cutoff_eq u χ w hB hS hSB hSuppχ hHarmonic
    change weightSignedMeasure (D w) χ.toFun S = -weightSignedMeasure (D w) χ.toFun Z -
      weightSignedMeasure (D χ) w.toFun B at hw
    have he := (neg_le_abs (weightSignedMeasure (D χ) e B)).trans hErr
    rw [hErrEq] at he
    simp only [hRow]
    rw [hwS, hw, ← hwZ]
    change weightSignedMeasure (D u) χ.toFun B - C₂ * Q - C₁ * T ≤
      -LZ - weightSignedMeasure (D χ) w.toFun B
    change _ ≤ C₂ * Q at he
    linarith only [hU, he, hLT]

end WalkDimensions.PEnergy.CompactCore
