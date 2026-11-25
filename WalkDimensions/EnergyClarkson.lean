import WalkDimensions.PEnergy

/-!
# Clarkson estimates for the energy seminorm
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {m : Measure X} [IsFiniteMeasureOnCompacts m] {p : ℝ} (E : PEnergy m p)

theorem energy_eq_root_rpow (f : E.domain) :
    (E.energy f : ℝ) = E.rootSeminorm f ^ p := by
  have hp : 0 < p := zero_lt_one.trans E.one_lt
  rw [E.rootSeminorm_apply, ← Real.rpow_mul (NNReal.coe_nonneg _),
    inv_mul_cancel₀ hp.ne', Real.rpow_one]

theorem energy_smul_real (a : ℝ) (f : E.domain) :
    (E.energy (a • f) : ℝ) = |a| ^ p * (E.energy f : ℝ) := by
  rw [E.energy_eq_root_rpow, map_smul_eq_mul, Real.norm_eq_abs,
    Real.mul_rpow (abs_nonneg _) (apply_nonneg _ _), ← E.energy_eq_root_rpow]

/-- On a seminorm ball the two Clarkson inequalities give a power bound
for the sum and difference, with an exponent depending only on `p`. -/
theorem exists_clarkson_power :
    ∃ q : ℝ, 0 < q ∧ ∀ (f g : E.domain) (M : ℝ), 0 ≤ M →
      E.rootSeminorm f ≤ M → E.rootSeminorm g ≤ M →
      E.rootSeminorm (f + g) ^ q + E.rootSeminorm (f - g) ^ q ≤ (2 * M) ^ q := by
  have hp : 0 < p := zero_lt_one.trans E.one_lt
  let s := p - 1
  have hs : 0 < s := sub_pos.mpr E.one_lt
  have hnorm (f : E.domain) : 0 ≤ E.rootSeminorm f := apply_nonneg _ _
  have hrpow (a : ℝ) (ha : 0 ≤ a) : (a ^ (s⁻¹ : ℝ)) ^ s = a := by
    rw [← Real.rpow_mul ha, inv_mul_cancel₀ hs.ne', Real.rpow_one]
  rcases le_total 2 p with h₂ | h₂
  · refine ⟨p, hp, fun f g M hM hf hg ↦ ?_⟩
    have hEf : (E.energy f : ℝ) ≤ M ^ p := by
      rw [E.energy_eq_root_rpow]
      exact Real.rpow_le_rpow (hnorm f) hf hp.le
    have hEg : (E.energy g : ℝ) ≤ M ^ p := by
      rw [E.energy_eq_root_rpow]
      exact Real.rpow_le_rpow (hnorm g) hg hp.le
    rw [← E.energy_eq_root_rpow, ← E.energy_eq_root_rpow]
    calc
      _ ≤ 2 * ((E.energy f : ℝ) ^ s⁻¹ + (E.energy g : ℝ) ^ s⁻¹) ^ s :=
        E.clarkson_two_le h₂ f g
      _ ≤ 2 * ((M ^ p) ^ s⁻¹ + (M ^ p) ^ s⁻¹) ^ s := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Real.rpow_le_rpow (by positivity) _ hs.le
        exact add_le_add (Real.rpow_le_rpow (NNReal.coe_nonneg _) hEf (inv_nonneg.mpr hs.le))
          (Real.rpow_le_rpow (NNReal.coe_nonneg _) hEg (inv_nonneg.mpr hs.le))
      _ = (2 * M) ^ p := by
        rw [← two_mul, Real.mul_rpow (by norm_num) (by positivity),
          hrpow _ (Real.rpow_nonneg hM _), Real.mul_rpow (by norm_num) hM, ← mul_assoc]
        nth_rw 1 [← Real.rpow_one (2 : ℝ)]
        rw [← Real.rpow_add (by norm_num)]
        congr 2
        dsimp [s]
        ring
  · let q := p * s⁻¹
    have hq : 0 < q := mul_pos hp (inv_pos.mpr hs)
    refine ⟨q, hq, fun f g M hM hf hg ↦ ?_⟩
    have he (u : E.domain) :
        E.rootSeminorm u ^ q = (E.energy u : ℝ) ^ s⁻¹ := by
      rw [E.energy_eq_root_rpow, ← Real.rpow_mul (hnorm u)]
    have hplus : f + g + (f - g) = (2 : ℝ) • f := by
      rw [two_smul]
      abel
    have hminus : f + g - (f - g) = (2 : ℝ) • g := by
      rw [two_smul]
      abel
    have hclarkson := E.clarkson_le_two h₂ (f + g) (f - g)
    rw [hplus, hminus, E.energy_smul_real, E.energy_smul_real,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hclarkson
    have hb (u : E.domain) (hu : E.rootSeminorm u ≤ M) : (E.energy u : ℝ) ≤ M ^ p := by
      rw [E.energy_eq_root_rpow]
      exact Real.rpow_le_rpow (hnorm u) hu hp.le
    let L := (E.energy (f + g) : ℝ) ^ s⁻¹ + (E.energy (f - g) : ℝ) ^ s⁻¹
    change 2 * L ^ s ≤ _ at hclarkson
    have hpow : 2 * L ^ s ≤ 2 * ((2 * M) ^ q) ^ s := by
      apply hclarkson.trans
      have hqmul : q * s = p := by dsimp only [q]; rw [mul_assoc, inv_mul_cancel₀ hs.ne', mul_one]
      rw [← Real.rpow_mul (by positivity), hqmul, Real.mul_rpow (by norm_num) hM, two_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left (hb f hf) (by positivity))
        (mul_le_mul_of_nonneg_left (hb g hg) (by positivity))
    rw [he, he]
    exact (Real.rpow_le_rpow_iff (by positivity : 0 ≤ L)
      (Real.rpow_nonneg (mul_nonneg (by norm_num) hM) _) hs).1
      (by linarith only [hpow])

end WalkDimensions.PEnergy
