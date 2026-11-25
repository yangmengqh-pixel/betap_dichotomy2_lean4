import WalkDimensions.EnergyDerivativeWeights
import WalkDimensions.CoreCutoffSums

/-!
# The finite coupling from harmonic variations
-/

open Filter Function MeasureTheory Set
open scoped ENNReal

namespace WalkDimensions.PEnergy.CompactCore

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [LocallyCompactSpace X] {m : Measure X} [IsFiniteMeasureOnCompacts m] {p : ℝ} {E : PEnergy m p}

theorem energyDerivativeMeasure_apply_eq_univ_of_support (u g : E.CompactCore)
    {B : Set X} (hB : MeasurableSet B) (hsupp : support g.toFun ⊆ B) :
    E.energyDerivativeMeasure u.domainElement g.domainElement B =
      E.energyDerivativeMeasure u.domainElement g.domainElement univ := by
  let ν := E.energyDerivativeMeasure u.domainElement g.domainElement
  change ν B = ν univ
  have hzero : ν.totalVariation Bᶜ = 0 := u.energyDerivativeMeasure_variation_zero_of_const_on
    g hB.compl (fun _ hx ↦ notMem_support.mp (fun h ↦ hx (hsupp h)))
  have h := ν.eNorm_measure_le_variation Bᶜ
  rw [← ν.totalVariation_eq_variation, hzero, Real.eNorm_eq_ofReal_abs, nonpos_iff_eq_zero,
    ENNReal.ofReal_eq_zero] at h
  have hz := abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
  have he := VectorMeasure.of_union (v := ν) (disjoint_compl_right (a := B)) hB hB.compl
  rwa [union_compl_self, hz, add_zero, eq_comm] at he

private theorem support_mul_subset (χ v : E.CompactCore) :
    support (χ.mul v).toFun ⊆ support χ.toFun := by
  intro x hx
  by_contra he
  exact hx (by rw [mul_apply, notMem_support.mp he, zero_mul])

variable {V : Type*} [Fintype V]

/-- The two row sums of the antisymmetric coupling follow from the partition
identity and locality of the signed derivative. -/
theorem harmonic_cutoff_row_sum (u χ : E.CompactCore) (φ : V → E.CompactCore)
    {B S : Set X} (hS : MeasurableSet S) (hSB : S ⊆ B)
    (hPartition : ∀ x ∈ B, ∑ i, (φ i).toFun x = 1) :
    let D := fun v : E.CompactCore ↦ E.energyDerivativeMeasure u.domainElement v.domainElement
    let T := fun i j ↦ weightSignedMeasure (D (φ j)) (χ.mul (φ i)).toFun S
    ∀ j, (∑ i, (T i j - T j i)) = weightSignedMeasure (D (φ j)) χ.toFun S := by
  classical
  let ℓ := E.energyDerivativeLinear u.domainElement
  let D (v : E.CompactCore) := ℓ v.domainElement
  let T (i j : V) := weightSignedMeasure (D (φ j)) (χ.mul (φ i)).toFun S
  let F := finsetSum Finset.univ φ
  have hF : D F = ∑ i, D (φ i) := map_sum ℓ _ _
  have hSum (j : V) : (∑ i, T i j) = weightSignedMeasure (D (φ j)) χ.toFun S := by
    let g := finsetSum Finset.univ (fun i ↦ χ.mul (φ i))
    have hg : EqOn g.toFun χ.toFun S := by
      intro x hx
      simp only [g, finsetSum_apply, mul_apply, ← Finset.mul_sum, hPartition x (hSB hx), mul_one]
    calc
      _ = weightSignedMeasure (D (φ j)) g.toFun S := by
        have he : g.toFun = ∑ i, (χ.mul (φ i)).toFun := by funext x; simp [g, Finset.sum_apply]
        rw [he, weightSignedMeasure_finsetSum _ _ (fun i _ ↦ (χ.mul (φ i)).integrable_vectorMeasure _),
          FunLike.coe_sum, Finset.sum_apply]
      _ = _ := weightSignedMeasure_congr_on _ (g.integrable_vectorMeasure _)
        (χ.integrable_vectorMeasure _) hS hg
  have hSum' (j : V) : (∑ i, T j i) = 0 := by
    have hZero : (D F).totalVariation S = 0 := u.energyDerivativeMeasure_variation_zero_of_const_on
      F hS (fun x hx ↦ hPartition x (hSB hx))
    calc
      _ = weightSignedMeasure (D F) (χ.mul (φ j)).toFun S := by
        rw [hF, weightSignedMeasure_finsetSum_measure _ (fun _ _ ↦ (χ.mul (φ j)).integrable_vectorMeasure _),
          FunLike.coe_sum, Finset.sum_apply]
      _ = _ := by
        have h := abs_weightSignedMeasure_apply_le_lintegral (D F)
          ((χ.mul (φ j)).integrable_vectorMeasure _) (A := S)
        rw [Measure.restrict_eq_zero.mpr hZero, lintegral_zero_measure, nonpos_iff_eq_zero,
          ENNReal.ofReal_eq_zero] at h
        exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
  change ∀ j, (∑ i, (T i j - T j i)) = _
  intro j
  rw [Finset.sum_sub_distrib, hSum, hSum', sub_zero]
  rfl

/-- Harmonicity moves a weighted derivative on the selected set to the
complement and to the derivative of the large cutoff. -/
theorem weighted_harmonic_cutoff_eq (u χ g : E.CompactCore)
    {B S : Set X} (hB : MeasurableSet B) (hS : MeasurableSet S) (hSB : S ⊆ B)
    (hsupp : support χ.toFun ⊆ B)
    (hHarmonic : ∀ v : E.CompactCore, support v.toFun ⊆ B →
      E.energyDerivativeMeasure u.domainElement v.domainElement univ = 0) :
    let D := fun v : E.CompactCore ↦ E.energyDerivativeMeasure u.domainElement v.domainElement
    weightSignedMeasure (D g) χ.toFun S =
      -weightSignedMeasure (D g) χ.toFun (B \ S) - weightSignedMeasure (D χ) g.toFun B := by
  let D (v : E.CompactCore) := E.energyDerivativeMeasure u.domainElement v.domainElement
  have hv := (u.energyDerivativeMeasure_apply_eq_univ_of_support (χ.mul g) hB
    ((support_mul_subset χ g).trans hsupp)).trans
    (hHarmonic (χ.mul g) ((support_mul_subset χ g).trans hsupp))
  have hLeibniz := congrArg (fun ν : SignedMeasure X ↦ ν B) (energyDerivativeMeasure_mul u χ g)
  change D (χ.mul g) B = _ at hv
  change D (χ.mul g) B = _ at hLeibniz
  rw [hv, FunLike.coe_add, Pi.add_apply] at hLeibniz
  have hsplit := VectorMeasure.of_union (v := weightSignedMeasure (D g) χ.toFun)
    (disjoint_sdiff_right (s := S) (t := B)) hS (hB.diff hS)
  rw [union_sdiff_cancel hSB] at hsplit
  change weightSignedMeasure (D g) χ.toFun S =
    -weightSignedMeasure (D g) χ.toFun (B \ S) - weightSignedMeasure (D χ) g.toFun B
  linarith only [hLeibniz, hsplit]

/-- Summing the boundary pairings against any finite potential gives the
weighted derivative of its compact-core interpolant. -/
theorem weighted_derivative_interpolant (u χ : E.CompactCore)
    (φ : V → E.CompactCore) (a : V → ℝ) (S : Set X) :
    let D := fun v : E.CompactCore ↦ E.energyDerivativeMeasure u.domainElement v.domainElement
    let w := finsetSum Finset.univ (fun j ↦ (φ j).smul (a j))
    (∑ j, weightSignedMeasure (D (φ j)) χ.toFun S * a j) = weightSignedMeasure (D w) χ.toFun S := by
  classical
  let ℓ := E.energyDerivativeLinear u.domainElement
  let w := finsetSum Finset.univ (fun j ↦ (φ j).smul (a j))
  have he : ℓ w.domainElement = ∑ j, a j • ℓ (φ j).domainElement := by
    change ℓ (∑ j, a j • (φ j).domainElement) = _
    simp only [map_sum, map_smul]
  change _ = weightSignedMeasure (ℓ w.domainElement) χ.toFun S
  rw [he, weightSignedMeasure_finsetSum_measure _ (fun j _ ↦ χ.integrable_vectorMeasure _),
    FunLike.coe_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  have h := VectorMeasure.integral_smul_vectorMeasure
    (μ := ℓ (φ j).domainElement |>.restrict S) (B := ContinuousLinearMap.lsmul ℝ ℝ) χ.toFun (a j)
  have hEq : (a j • ℓ (φ j).domainElement).restrict S = a j • (ℓ (φ j).domainElement).restrict S :=
    map_smul (VectorMeasure.restrictₗ (R := ℝ) S) _ _
  change _ = weightSignedMeasure (a j • ℓ (φ j).domainElement) χ.toFun S
  rw [weightSignedMeasure, VectorMeasure.withDensity_apply (χ.integrable_vectorMeasure _),
    weightSignedMeasure, VectorMeasure.withDensity_apply (χ.integrable_vectorMeasure _), hEq, h,
    smul_eq_mul, mul_comm]
  rfl

end WalkDimensions.PEnergy.CompactCore
