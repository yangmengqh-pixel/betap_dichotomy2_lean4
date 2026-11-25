import WalkDimensions.EnergyMeasureDerivative

/-!
# Linearity, locality and variation bounds for the signed energy measure
-/

open Filter Function MeasureTheory Set
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {p : ℝ} (E : PEnergy μ p)

noncomputable def energyDerivativeLinear (f : E.domain) : E.domain →ₗ[ℝ] SignedMeasure X where
  toFun := E.energyDerivativeMeasure f
  map_add' g h := by
    ext A hA
    simp only [FunLike.coe_add, Pi.add_apply, E.energyDerivativeMeasure_apply _ _ hA, map_add]
  map_smul' a g := by
    ext A hA
    simp only [smul_apply, E.energyDerivativeMeasure_apply _ _ hA, map_smul,
      RingHom.id_apply]

theorem hasDerivAt_energy_of_energyDerivativeMeasure (f g : E.domain) :
    HasDerivAt (fun t : ℝ ↦ (E.energy (f + t • g) : ℝ))
      (p * E.energyDerivativeMeasure f g univ) 0 := by
  simpa only [E.energyDerivativeMeasure_apply f g MeasurableSet.univ, E.energyMeasure_univ,
    ENNReal.coe_toReal] using E.hasDerivAt_energyMeasure f g MeasurableSet.univ

theorem energyDerivativeMeasure_self (f : E.domain) {A : Set X} (hA : MeasurableSet A) :
    E.energyDerivativeMeasure f f A = (E.energyMeasure f A).toReal := by
  rw [E.energyDerivativeMeasure_apply f f hA]
  let F := (E.energyMeasure f A).toReal
  have hEq (t : ℝ) : (E.energyMeasure (f + t • f) A).toReal = |1 + t| ^ p * F := by
    rw [show f + t • f = (1 + t) • f by rw [add_smul, one_smul],
      E.energyMeasure_real_eq _ hA, map_smul_eq_mul, Real.norm_eq_abs,
      Real.mul_rpow (abs_nonneg _) (apply_nonneg _ _), ← E.energyMeasure_real_eq f hA]
  have h := E.hasDerivAt_energyMeasure f f hA
  simp_rw [hEq] at h
  have h1 : HasDerivAt (fun t : ℝ ↦ 1 + t) 1 0 := (hasDerivAt_id (0 : ℝ)).const_add 1
  have h2 := (hasDerivAt_abs_rpow (1 + (0 : ℝ)) E.one_lt).comp 0 h1
  simp only [add_zero, abs_one, Real.one_rpow, mul_one] at h2
  exact mul_left_cancel₀ (zero_lt_one.trans E.one_lt).ne' (h.unique (h2.mul_const F))

theorem energyDerivativeMeasure_eq_of_eqOn_sub_const (f g h : E.CompactCore)
    {A : Set X} (hA : MeasurableSet A) {a : ℝ}
    (hEq : EqOn (fun x ↦ g.toFun x - h.toFun x) (fun _ ↦ a) A) :
    E.energyDerivativeMeasure f.domainElement g.domainElement A =
      E.energyDerivativeMeasure f.domainElement h.domainElement A := by
  simp only [E.energyDerivativeMeasure_apply _ _ hA]
  have hg := E.hasDerivAt_energyMeasure f.domainElement g.domainElement hA
  have hh := E.hasDerivAt_energyMeasure f.domainElement h.domainElement hA
  have he (t : ℝ) :
      E.energyMeasure (f.domainElement + t • g.domainElement) A =
        E.energyMeasure (f.domainElement + t • h.domainElement) A := by
    change E.energyMeasure (f.add (g.smul t)).domainElement A =
      E.energyMeasure (f.add (h.smul t)).domainElement A
    rw [E.energyMeasure_core (f.add (g.smul t)), E.energyMeasure_core (f.add (h.smul t))]
    apply (f.add (g.smul t)).coreEnergyMeasure_eq_of_eqOn_sub_const (f.add (h.smul t)) hA
      (a := t * a)
    intro x hx
    change f.toFun x + t * g.toFun x - (f.toFun x + t * h.toFun x) = t * a
    have hg := hEq hx
    change g.toFun x - h.toFun x = a at hg
    rw [← hg]
    ring
  simp_rw [he] at hg
  exact mul_left_cancel₀ (zero_lt_one.trans E.one_lt).ne' (hg.unique hh)

theorem energyMeasureRoot_mono (f : E.domain) {A B : Set X}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : A ⊆ B) :
    E.energyMeasureRoot A hA f ≤ E.energyMeasureRoot B hB f := by
  change E.energyMeasureLaws.root A hA f ≤ E.energyMeasureLaws.root B hB f
  rw [E.energyMeasureLaws.root_apply, E.energyMeasureLaws.root_apply, measureReal_def, measureReal_def]
  exact Real.rpow_le_rpow ENNReal.toReal_nonneg
    (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hAB))
    (inv_nonneg.mpr (zero_lt_one.trans E.one_lt).le)

theorem energyDerivativeMeasure_variation_le (f g : E.domain) {A : Set X} (hA : MeasurableSet A) :
    ((E.energyDerivativeMeasure f g).totalVariation A).toReal ≤
      2 * (E.energyMeasureRoot A hA f) ^ (p - 1) * E.energyMeasureRoot A hA g := by
  let ν := E.energyDerivativeMeasure f g
  obtain ⟨P, hP, hpos, hneg, hp, hn⟩ := ν.toJordanDecomposition_spec
  change (ν.totalVariation A).toReal ≤ _
  rw [SignedMeasure.totalVariation, FunLike.coe_add, Pi.add_apply, hp, hn,
    SignedMeasure.toMeasureOfZeroLE_apply _ _ _ hA, SignedMeasure.toMeasureOfLEZero_apply _ _ _ hA,
    ENNReal.toReal_add ENNReal.coe_ne_top ENNReal.coe_ne_top, ENNReal.coe_toReal, ENNReal.coe_toReal]
  have hB (B : Set X) (hB : MeasurableSet B) (hBA : B ⊆ A) :
      |ν B| ≤ (E.energyMeasureRoot A hA f) ^ (p - 1) * E.energyMeasureRoot A hA g := by
    rw [E.energyDerivativeMeasure_apply f g hB]
    exact (E.abs_energyVariation_le f g hB).trans (mul_le_mul
      (Real.rpow_le_rpow (apply_nonneg _ _) (E.energyMeasureRoot_mono f hB hA hBA)
        (sub_nonneg.mpr E.one_lt.le))
      (E.energyMeasureRoot_mono g hB hA hBA) (apply_nonneg _ _) (Real.rpow_nonneg (apply_nonneg _ _) _))
  change ν (P ∩ A) + -ν (Pᶜ ∩ A) ≤ _
  calc
    _ ≤ |ν (P ∩ A)| + |ν (Pᶜ ∩ A)| := by
      simpa only [abs_neg] using add_le_add (le_abs_self (ν (P ∩ A))) (le_abs_self (-ν (Pᶜ ∩ A)))
    _ ≤ _ := by
      rw [mul_assoc, two_mul]
      exact add_le_add (hB _ (hP.inter hA) inter_subset_right)
        (hB _ (hP.compl.inter hA) inter_subset_right)

end WalkDimensions.PEnergy
