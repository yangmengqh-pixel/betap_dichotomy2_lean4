import WalkDimensions.EnergyClarkson
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# Complementary Clarkson inequalities

Applying the given Clarkson inequality to the sum and difference and then
using the scalar power mean proves the second inequality in each range.
-/

open MeasureTheory Set

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {m : Measure X} [IsFiniteMeasureOnCompacts m] {p : ℝ} (E : PEnergy m p)

private theorem mean_rpow_le {a b r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : 1 ≤ r) :
    ((a + b) / 2) ^ r ≤ (a ^ r + b ^ r) / 2 := by
  have h := (convexOn_rpow hr).2 (mem_Ici.mpr ha) (mem_Ici.mpr hb)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  simp only [smul_eq_mul] at h
  convert h using 1
  · congr 1
    ring
  · ring

private theorem le_mean_rpow {a b r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) :
    (a ^ r + b ^ r) / 2 ≤ ((a + b) / 2) ^ r := by
  have h := (Real.concaveOn_rpow hr₀ hr₁).2 (mem_Ici.mpr ha) (mem_Ici.mpr hb)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  simp only [smul_eq_mul] at h
  convert h using 1
  · ring
  · congr 1
    ring

private theorem energy_add_add_energy_sub_sum (f g : E.domain) :
    (E.energy ((f + g) + (f - g)) : ℝ) + (E.energy ((f + g) - (f - g)) : ℝ) =
      (2 : ℝ) ^ p * ((E.energy f : ℝ) + (E.energy g : ℝ)) := by
  have h₁ : f + g + (f - g) = (2 : ℝ) • f := by rw [two_smul]; abel
  have h₂ : f + g - (f - g) = (2 : ℝ) • g := by rw [two_smul]; abel
  rw [h₁, h₂, E.energy_smul_real, E.energy_smul_real, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), mul_add]

theorem energy_add_add_energy_sub_le_two_mul (hp₂ : p ≤ 2) (f g : E.domain) :
    (E.energy (f + g) : ℝ) + (E.energy (f - g) : ℝ) ≤
      2 * ((E.energy f : ℝ) + (E.energy g : ℝ)) := by
  let s := p - 1
  have hs : 0 < s := sub_pos.mpr E.one_lt
  let a : ℝ := E.energy (f + g)
  let b : ℝ := E.energy (f - g)
  have ha : 0 ≤ a := NNReal.coe_nonneg _
  have hb : 0 ≤ b := NNReal.coe_nonneg _
  have hk : 1 ≤ s⁻¹ := (one_le_inv₀ hs).2 (by dsimp [s]; linarith)
  have h1 := Real.rpow_le_rpow (by positivity)
    (mean_rpow_le (a := a) (b := b) ha hb hk) hs.le
  rw [← Real.rpow_mul (by positivity), inv_mul_cancel₀ hs.ne', Real.rpow_one] at h1
  have h2 := E.clarkson_le_two hp₂ (f + g) (f - g)
  rw [E.energy_add_add_energy_sub_sum] at h2
  change 2 * (a ^ s⁻¹ + b ^ s⁻¹) ^ s ≤ _ at h2
  have hpow : (2 : ℝ) ^ p = 2 * (2 : ℝ) ^ s := by
    nth_rw 2 [← Real.rpow_one (2 : ℝ)]
    rw [← Real.rpow_add (by norm_num), show 1 + s = p by dsimp [s]; ring]
  have h2' : ((a ^ s⁻¹ + b ^ s⁻¹) / 2) ^ s ≤ (E.energy f : ℝ) + (E.energy g : ℝ) := by
    rw [Real.div_rpow (by positivity) (by norm_num), div_le_iff₀ (by positivity)]
    rw [hpow] at h2
    linarith only [h2, mul_comm ((2 : ℝ) ^ s) ((E.energy f : ℝ) + (E.energy g : ℝ))]
  change a + b ≤ _
  linarith only [h1.trans h2']

theorem two_mul_le_energy_add_add_energy_sub (h₂p : 2 ≤ p) (f g : E.domain) :
    2 * ((E.energy f : ℝ) + (E.energy g : ℝ)) ≤
      (E.energy (f + g) : ℝ) + (E.energy (f - g) : ℝ) := by
  let s := p - 1
  have hs : 0 < s := sub_pos.mpr E.one_lt
  let a : ℝ := E.energy (f + g)
  let b : ℝ := E.energy (f - g)
  have ha : 0 ≤ a := NNReal.coe_nonneg _
  have hb : 0 ≤ b := NNReal.coe_nonneg _
  have hk : s⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by dsimp [s]; linarith)
  have h1 := Real.rpow_le_rpow (by positivity)
    (le_mean_rpow (a := a) (b := b) ha hb (inv_nonneg.mpr hs.le) hk) hs.le
  rw [← Real.rpow_mul (by positivity), inv_mul_cancel₀ hs.ne', Real.rpow_one] at h1
  have h2 := E.clarkson_two_le h₂p (f + g) (f - g)
  rw [E.energy_add_add_energy_sub_sum] at h2
  change _ ≤ 2 * (a ^ s⁻¹ + b ^ s⁻¹) ^ s at h2
  have hpow : (2 : ℝ) ^ p = 2 * (2 : ℝ) ^ s := by
    nth_rw 2 [← Real.rpow_one (2 : ℝ)]
    rw [← Real.rpow_add (by norm_num), show 1 + s = p by dsimp [s]; ring]
  have h2' : (E.energy f : ℝ) + (E.energy g : ℝ) ≤ ((a ^ s⁻¹ + b ^ s⁻¹) / 2) ^ s := by
    rw [Real.div_rpow (by positivity) (by norm_num), le_div_iff₀ (by positivity)]
    rw [hpow] at h2
    linarith only [h2, mul_comm ((2 : ℝ) ^ s) ((E.energy f : ℝ) + (E.energy g : ℝ))]
  change _ ≤ a + b
  linarith only [h2'.trans h1]

end WalkDimensions.PEnergy
