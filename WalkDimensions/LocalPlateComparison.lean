import WalkDimensions.NearMinimizerComparison
import WalkDimensions.PlateMinimizer

/-!
# Local comparison with a point-to-boundary plate potential
-/

open MeasureTheory Set
open scoped ENNReal

namespace WalkDimensions.PEnergy.CompactCore

variable {X : Type*} [MetricSpace X] [ProperSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
  [μ.IsOpenPosMeasure] {p : ℝ} (E : PEnergy μ p)

omit [SecondCountableTopology X] [μ.IsOpenPosMeasure] in
theorem exists_min_plate_root_gap :
    ∃ q > (0 : ℝ), ∀ (f v : E.CompactCore) {S : Set X} {x y z : X} {a : ℝ},
      0 < a → (∀ w, 0 ≤ f.toFun w) →
      f.toFun x = 1 → f.toFun y = 0 → f.toFun z = a →
      x ∉ S → y ∉ S →
      E.UnitPlate {z} S v.domainElement v.toFun →
      (∀ g w, E.UnitPlate {z} S g w → E.energy v.domainElement ≤ E.energy g) →
      let V := v.smul a
      let W := f.minAddConst V (a := 0) le_rfl
      let D := (E.energy f.domainElement : ℝ) - (E.capacity {x} {y}).toReal
      let M := ((E.energy V.domainElement : ℝ) + D) ^ p⁻¹
      E.rootSeminorm (W.domainElement - V.domainElement) ^ q ≤
        (2 * M) ^ q - (2 * E.rootSeminorm V.domainElement) ^ q := by
  obtain ⟨q, hq, hClarkson⟩ := E.exists_root_gap_bound
  refine ⟨q, hq, fun f v S x y z a ha hf hfx hfy hfz hx hy hplate hmin ↦ ?_⟩
  dsimp only
  let V := v.smul a
  let W := f.minAddConst V (a := 0) le_rfl
  let D := (E.energy f.domainElement : ℝ) - (E.capacity {x} {y}).toReal
  let M := ((E.energy V.domainElement : ℝ) + D) ^ p⁻¹
  have hp := zero_lt_one.trans E.one_lt
  have hcap := E.singleton_capacity_le_of_point_values f.ae_eq f.continuous hfx hfy
  have hD : 0 ≤ D := by
    have h := ENNReal.toReal_mono ENNReal.coe_ne_top hcap
    rw [ENNReal.coe_toReal] at h
    exact sub_nonneg.mpr h
  have hvRange : ∀ t, V.toFun t ∈ Icc (0 : ℝ) a := by
    intro t
    have h := hplate.2.2.1 t
    exact ⟨mul_nonneg ha.le h.1,
      (mul_le_mul_of_nonneg_left h.2 ha.le).trans_eq (mul_one _)⟩
  have hvZero (t : X) (ht : t ∉ S) : V.toFun t = 0 := by
    change a * v.toFun t = 0
    rw [hplate.2.2.2.2 ht, mul_zero]
  have hvz : V.toFun z = a := by
    change a * v.toFun z = a
    rw [hplate.2.2.2.1 (mem_singleton z), mul_one]
  have hwRange : ∀ t, W.toFun t ∈ Icc (0 : ℝ) a := by
    intro t
    change min (f.toFun t) (V.toFun t + 0) ∈ _
    rw [add_zero]
    exact ⟨le_min (hf t) (hvRange t).1, (min_le_right _ _).trans (hvRange t).2⟩
  have hwz : W.toFun z = a := by
    change min (f.toFun z) (V.toFun z + 0) = a
    rw [add_zero, hfz, hvz, min_self]
  have hwZero (t : X) (ht : t ∉ S) : W.toFun t = 0 := by
    change min (f.toFun t) (V.toFun t + 0) = 0
    rw [hvZero t ht, add_zero, min_eq_right (hf t)]
  let P := (W.add V).smul (1 / 2 : ℝ)
  let P₁ := P.smul a⁻¹
  have hMid : E.UnitPlate {z} S P₁.domainElement P₁.toFun := by
    refine ⟨P₁.continuous, P₁.ae_eq, ?_, ?_, ?_⟩
    · intro t
      change a⁻¹ * ((1 / 2 : ℝ) * (W.toFun t + V.toFun t)) ∈ Icc 0 1
      refine ⟨by positivity [(hwRange t).1, (hvRange t).1], ?_⟩
      calc
        _ ≤ a⁻¹ * a := mul_le_mul_of_nonneg_left
          (by linarith only [(hwRange t).2, (hvRange t).2]) (inv_nonneg.mpr ha.le)
        _ = _ := inv_mul_cancel₀ ha.ne'
    · intro t ht
      have he : t = z := mem_singleton_iff.mp ht
      subst t
      change a⁻¹ * ((1 / 2 : ℝ) * (W.toFun z + V.toFun z)) = 1
      rw [hwz, hvz, show (1 / 2 : ℝ) * (a + a) = a by ring, inv_mul_cancel₀ ha.ne']
    · intro t ht
      change a⁻¹ * ((1 / 2 : ℝ) * (W.toFun t + V.toFun t)) = 0
      rw [hwZero t ht, hvZero t ht, add_zero, mul_zero, mul_zero]
  have hMidRoot : E.rootSeminorm V.domainElement ≤ E.rootSeminorm P.domainElement := by
    have he : E.rootSeminorm v.domainElement ≤ E.rootSeminorm P₁.domainElement := by
      rw [E.rootSeminorm_apply, E.rootSeminorm_apply]
      exact Real.rpow_le_rpow (NNReal.coe_nonneg _) (NNReal.coe_le_coe.mpr (hmin _ _ hMid))
        (inv_nonneg.mpr hp.le)
    change E.rootSeminorm v.domainElement ≤ E.rootSeminorm (a⁻¹ • P.domainElement) at he
    change E.rootSeminorm (a • v.domainElement) ≤ _
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos ha]
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha)] at he
    apply (mul_le_mul_of_nonneg_left he ha.le).trans_eq
    rw [← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]
  have hVM : E.rootSeminorm V.domainElement ≤ M := by
    rw [E.rootSeminorm_apply]
    exact Real.rpow_le_rpow (NNReal.coe_nonneg _) (le_add_of_nonneg_right hD) (inv_nonneg.mpr hp.le)
  have hWM : E.rootSeminorm W.domainElement ≤ M := by
    rw [E.rootSeminorm_apply]
    exact Real.rpow_le_rpow (NNReal.coe_nonneg _)
      (f.energy_min_le_add_point_defect V hfx hfy (hvZero x hx) (hvZero y hy)) (inv_nonneg.mpr hp.le)
  exact hClarkson W.domainElement V.domainElement (apply_nonneg _ _) hVM hMidRoot hWM hVM

end WalkDimensions.PEnergy.CompactCore
