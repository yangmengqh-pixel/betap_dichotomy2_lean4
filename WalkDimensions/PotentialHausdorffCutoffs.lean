import WalkDimensions.BallPotential
import WalkDimensions.CorePotentialMeasure
import WalkDimensions.EnergyMeasureConstruction
import WalkDimensions.PotentialMeasureBounds

/-!
# Cutoffs whose energy measures are bounded by Hausdorff measure
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal NNReal

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SecondCountableTopology X] {m : Measure X}
  [IsFiniteMeasureOnCompacts m] [m.IsOpenPosMeasure] {p : ℝ} (E : PEnergy m p)

theorem exists_ball_unitPlate_minimizer_with_measure_bound {d β : ℝ}
    (hvol : AhlforsRegular m d) (hβ : d < β)
    (hPI : E.Poincare E.energyMeasure β) (hcap : E.CapacityUpperBound β)
    (hunbounded : ¬ Bornology.IsBounded (univ : Set X)) :
    let c := (β - d) / (p - 1)
    ∃ C H A : ℝ, 0 < C ∧ 0 < H ∧ 1 < A ∧
      ∀ (x : X) (r : ℝ), 0 < r →
      ∃ f : E.CompactCore, E.UnitPlate (ball x r) (closedBall x (A * r)) f.domainElement f.toFun ∧
        (∀ g w, E.UnitPlate (ball x r) (closedBall x (A * r)) g w → E.energy f.domainElement ≤ E.energy g) ∧
        (E.energy f.domainElement : ℝ) ≤ C * r ^ (d - β) ∧
        (∀ y z, |f.toFun y - f.toFun z| ≤ H * r ^ (-c) * dist y z ^ c) ∧
        E.energyMeasure f.domainElement ≤ ENNReal.ofReal (C * H * r ^ (-p * c)) • μH[c] := by
  let c := (β - d) / (p - 1)
  have hp₁ : 0 < p - 1 := sub_pos.mpr E.one_lt
  have hc : 0 < c := div_pos (sub_pos.mpr hβ) hp₁
  obtain ⟨C, A, hC, hA, hcut⟩ :=
    E.exists_ball_unitPlate_minimizer hvol hβ hPI E.energyMeasure_univ hcap hunbounded
  obtain ⟨H, hH, hHolder⟩ := E.exists_minimizer_holder_bound hvol hβ hPI E.energyMeasure_univ
  obtain ⟨_, V, hV, hVolume⟩ := hvol
  let C' := C * V
  have hC' : 0 < C' := mul_pos hC hV
  let H' := H * C' ^ (p - 1)⁻¹
  have hH' : 0 < H' := by dsimp only [H']; positivity
  refine ⟨C', H', A, hC', hH', hA, fun x r hr ↦ ?_⟩
  obtain ⟨f, u, hPlate, hmin, he⟩ := hcut x r hr
  let S := closedBall x (A * r)
  have hS : IsCompact S := isCompact_closedBall _ _
  let F : E.CompactCore :=
    ⟨f, u, hPlate.2.1, hPlate.1, HasCompactSupport.intro hS hPlate.2.2.2.2⟩
  have hE : (E.energy f : ℝ) ≤ C' * r ^ (d - β) := by
    have h := he.trans (mul_le_mul_of_nonneg_left (hVolume x r hr).2 bot_le)
    rw [← ENNReal.ofReal_mul (by positivity)] at h
    have hEq : C * r ^ (-β) * (V * r ^ d) = C' * r ^ (d - β) := by
      dsimp only [C']
      rw [sub_eq_add_neg, Real.rpow_add hr]
      ring
    rw [hEq, ← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
    exact h
  have hScale : (p - 1) * c = β - d := by
    dsimp only [c]
    rw [mul_comm, div_mul_cancel₀ _ hp₁.ne']
  have hPower : (d - β) * (p - 1)⁻¹ = -c := by
    dsimp only [c]
    rw [div_eq_mul_inv]
    ring
  have hcoef : H * (E.energy f : ℝ) ^ (p - 1)⁻¹ ≤ H' * r ^ (-c) := by
    apply (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (NNReal.coe_nonneg _) hE
      (inv_nonneg.mpr hp₁.le)) hH.le).trans_eq
    rw [Real.mul_rpow hC'.le (Real.rpow_nonneg hr.le _), ← Real.rpow_mul hr.le, hPower, mul_assoc]
  have hHC (y z : X) : |F.toFun y - F.toFun z| ≤ H' * r ^ (-c) * dist y z ^ c :=
    (hHolder hS hPlate hmin y z).trans (mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg dist_nonneg _))
  refine ⟨F, hPlate, hmin, hE, hHC, ?_⟩
  let a : ℝ≥0 := (H' * r ^ (-c)).toNNReal
  let e : ℝ≥0 := c.toNNReal
  have he' : (e : ℝ) = c := Real.coe_toNNReal _ hc.le
  have ha : (a : ℝ) = H' * r ^ (-c) := Real.coe_toNNReal _ (by positivity)
  have hHF : HolderWith a e F.toFun := by
    intro y z
    rw [edist_dist, edist_dist, Real.dist_eq, he', ENNReal.ofReal_rpow_of_nonneg dist_nonneg hc.le,
      ← ENNReal.ofReal_coe_nnreal, ha, ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (hHC y z)
  have hmass := measure_le_smul_hausdorff_of_map_eq_smul_volume
    (show 0 < e by exact_mod_cast (he'.symm ▸ hc))
    hHF (F.map_coreEnergyMeasure_of_unitPlate_minimizer hS hPlate hmin)
  rw [he'] at hmass
  rw [E.energyMeasure_core F]
  apply hmass.trans
  intro T
  rw [smul_apply, smul_apply, smul_eq_mul, smul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ bot_le
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_coe_nnreal, ha,
    ← ENNReal.ofReal_mul (NNReal.coe_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  refine (mul_le_mul_of_nonneg_right hE (by positivity)).trans_eq ?_
  rw [mul_mul_mul_comm C' _ H', ← Real.rpow_add hr]
  congr 2
  linarith only [hScale]

end WalkDimensions.PEnergy
