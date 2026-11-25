import WalkDimensions.CoreEnergyClarksonLower

/-!
# Midpoint bounds for local energy sublevels
-/

open Filter Function MeasureTheory Set
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy.CompactCore

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {p : ℝ} {E : PEnergy μ p}

noncomputable def localEnergyRoot (f : E.CompactCore) (A : Set X) : ℝ :=
  (f.coreEnergyMeasure A).toReal ^ p⁻¹

theorem localEnergyRoot_nonneg (f : E.CompactCore) (A : Set X) :
    0 ≤ f.localEnergyRoot A := Real.rpow_nonneg ENNReal.toReal_nonneg _

theorem localEnergyRoot_smul (f : E.CompactCore) (a : ℝ) (A : Set X) :
    (f.smul a).localEnergyRoot A = |a| * f.localEnergyRoot A := by
  have hp := zero_lt_one.trans E.one_lt
  unfold localEnergyRoot
  rw [f.coreEnergyMeasure_smul a, smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.rpow_nonneg (abs_nonneg a) _),
    Real.mul_rpow (Real.rpow_nonneg (abs_nonneg a) _) ENNReal.toReal_nonneg,
    ← Real.rpow_mul (abs_nonneg a), mul_inv_cancel₀ hp.ne', Real.rpow_one]

theorem coreEnergyMeasure_toReal_smul (f : E.CompactCore) (a : ℝ) (A : Set X) :
    ((f.smul a).coreEnergyMeasure A).toReal = |a| ^ p * (f.coreEnergyMeasure A).toReal := by
  rw [f.coreEnergyMeasure_smul a, smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.rpow_nonneg (abs_nonneg _) _)]

theorem pairMeasure_toReal (f g : E.CompactCore) (A : Set X) :
    (f.pairMeasure g A).toReal =
      ((f.add g).coreEnergyMeasure A).toReal + ((f.sub g).coreEnergyMeasure A).toReal := by
  simp only [pairMeasure, FunLike.coe_add, Pi.add_apply, ENNReal.toReal_add
    (measure_ne_top _ _) (measure_ne_top _ _)]

theorem coreEnergyMeasure_add_le_two_pow_max (f g : E.CompactCore)
    {A : Set X} (hA : MeasurableSet A) :
    ((f.add g).coreEnergyMeasure A).toReal ≤
      (2 : ℝ) ^ p * max (f.coreEnergyMeasure A).toReal (g.coreEnergyMeasure A).toReal := by
  let a := (f.coreEnergyMeasure A).toReal
  let b := (g.coreEnergyMeasure A).toReal
  let u := ((f.add g).coreEnergyMeasure A).toReal
  let v := ((f.sub g).coreEnergyMeasure A).toReal
  let s := p - 1
  have hs : 0 < s := sub_pos.mpr E.one_lt
  have hscale : 2 * (2 : ℝ) ^ s = (2 : ℝ) ^ p := by
    calc
      _ = (2 : ℝ) ^ (1 + s) := by rw [Real.rpow_add (by norm_num), Real.rpow_one]
      _ = _ := by congr 1; dsimp [s]; ring
  have hsingle (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
      x ≤ (x ^ s⁻¹ + y ^ s⁻¹) ^ s := by
    nth_rw 1 [← Real.rpow_one x]
    rw [← inv_mul_cancel₀ hs.ne', Real.rpow_mul hx]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hx _) (le_add_of_nonneg_right
      (Real.rpow_nonneg hy _)) hs.le
  rcases le_total p 2 with h₂ | h₂
  · let F := f.add g
    let G := f.sub g
    have hP : (F.pairMeasure G A).toReal = (2 : ℝ) ^ p * (a + b) := by
      rw [F.pairMeasure_toReal G, mul_add]
      have hPlus : (F.add G).toFun = (f.smul 2).toFun := by
        funext x
        change f.toFun x + g.toFun x + (f.toFun x - g.toFun x) = 2 * f.toFun x
        ring
      have hMinus : (F.sub G).toFun = (g.smul 2).toFun := by
        funext x
        change f.toFun x + g.toFun x - (f.toFun x - g.toFun x) = 2 * g.toFun x
        ring
      rw [(F.add G).coreEnergyMeasure_eq_on_subset_of_eqOn (f.smul 2) hA isOpen_univ
        (subset_univ _) (fun x _ ↦ congrFun hPlus x),
        (F.sub G).coreEnergyMeasure_eq_on_subset_of_eqOn (g.smul 2) hA isOpen_univ
          (subset_univ _) (fun x _ ↦ congrFun hMinus x),
        coreEnergyMeasure_toReal_smul, coreEnergyMeasure_toReal_smul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have h := F.pairMeasure_clarkson_lower G h₂ hA
    rw [hP] at h
    have ht := (mul_le_mul_of_nonneg_left (hsingle u v ENNReal.toReal_nonneg ENNReal.toReal_nonneg) (by norm_num : (0 : ℝ) ≤ 2)).trans h
    have hmax : a + b ≤ 2 * max a b := by
      rw [two_mul]
      exact add_le_add (le_max_left _ _) (le_max_right _ _)
    have ht' := ht.trans (mul_le_mul_of_nonneg_left hmax (Real.rpow_nonneg (by norm_num) _))
    change u ≤ (2 : ℝ) ^ p * max a b
    linarith only [ht']
  · have h := f.pairMeasure_clarkson_upper g h₂ hA
    rw [f.pairMeasure_toReal g] at h
    change u + v ≤ 2 * (a ^ s⁻¹ + b ^ s⁻¹) ^ s at h
    let M := max a b
    have hM : 0 ≤ M := ENNReal.toReal_nonneg.trans (le_max_left _ _)
    have hSum : a ^ s⁻¹ + b ^ s⁻¹ ≤ 2 * M ^ s⁻¹ := by
      rw [two_mul]
      exact add_le_add (Real.rpow_le_rpow ENNReal.toReal_nonneg (le_max_left _ _)
        (inv_nonneg.mpr hs.le)) (Real.rpow_le_rpow ENNReal.toReal_nonneg (le_max_right _ _)
          (inv_nonneg.mpr hs.le))
    have hB := Real.rpow_le_rpow (add_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _)
      (Real.rpow_nonneg ENNReal.toReal_nonneg _)) hSum hs.le
    rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hM _), ← Real.rpow_mul hM,
      inv_mul_cancel₀ hs.ne', Real.rpow_one] at hB
    have hle := h.trans (mul_le_mul_of_nonneg_left hB (by norm_num))
    rw [← mul_assoc, hscale] at hle
    exact (le_add_of_nonneg_right (show 0 ≤ v from ENNReal.toReal_nonneg)).trans hle

theorem localEnergyRoot_midpoint_le (f g : E.CompactCore)
    {A : Set X} (hA : MeasurableSet A) :
    ((f.add g).smul (1 / 2)).localEnergyRoot A ≤ max (f.localEnergyRoot A) (g.localEnergyRoot A) := by
  rw [localEnergyRoot_smul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hp := zero_lt_one.trans E.one_lt
  have h := Real.rpow_le_rpow ENNReal.toReal_nonneg
    (f.coreEnergyMeasure_add_le_two_pow_max g hA) (inv_nonneg.mpr hp.le)
  rw [Real.mul_rpow (Real.rpow_nonneg (by norm_num) _) (by positivity),
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), mul_inv_cancel₀ hp.ne', Real.rpow_one] at h
  have hmax : (max (f.coreEnergyMeasure A).toReal (g.coreEnergyMeasure A).toReal) ^ p⁻¹ =
      max (f.localEnergyRoot A) (g.localEnergyRoot A) := by
    unfold localEnergyRoot
    rcases le_total (f.coreEnergyMeasure A).toReal (g.coreEnergyMeasure A).toReal with hle | hge
    · rw [max_eq_right hle, max_eq_right (Real.rpow_le_rpow ENNReal.toReal_nonneg hle (inv_nonneg.mpr hp.le))]
    · rw [max_eq_left hge, max_eq_left (Real.rpow_le_rpow ENNReal.toReal_nonneg hge (inv_nonneg.mpr hp.le))]
  rw [hmax] at h
  unfold localEnergyRoot at *
  linarith only [h]

end WalkDimensions.PEnergy.CompactCore
