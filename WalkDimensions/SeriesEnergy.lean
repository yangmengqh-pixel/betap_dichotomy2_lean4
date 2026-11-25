import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The series energy identity

The scalar minimization in equation (6.3) follows by strict convexity
of the power function after normalizing by the two series lengths.
-/

open Set

namespace WalkDimensions

theorem series_energy_minimum {p r s t : ℝ} (hp : 1 < p)
    (hr : 0 < r) (hs : 0 < s) (ht : t ∈ Icc (0 : ℝ) 1) :
    (r + s) ^ (1 - p) ≤ r ^ (1 - p) * (1 - t) ^ p + s ^ (1 - p) * t ^ p ∧
    ((r ^ (1 - p) * (1 - t) ^ p + s ^ (1 - p) * t ^ p = (r + s) ^ (1 - p)) ↔
      t = s / (r + s)) := by
  let T := r + s
  have hT : 0 < T := add_pos hr hs
  have hR : 0 < r / T := div_pos hr hT
  have hS : 0 < s / T := div_pos hs hT
  let x := (1 - t) / r
  let y := t / s
  have hx : 0 ≤ x := div_nonneg (sub_nonneg.mpr ht.2) hr.le
  have hy : 0 ≤ y := div_nonneg ht.1 hs.le
  have hsum : r / T + s / T = 1 := by rw [← add_div]; exact div_self hT.ne'
  have hcenter : r / T * x + s / T * y = 1 / T := by
    dsimp only [x, y]
    field_simp [hr.ne', hs.ne', hT.ne']
    ring
  have hterm {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
      a / T * (b / a) ^ p = T⁻¹ * (a ^ (1 - p) * b ^ p) := by
    rw [Real.div_rpow hb ha.le, Real.rpow_sub ha, Real.rpow_one]
    ring
  have hone : (1 / T) ^ p = T⁻¹ * T ^ (1 - p) := by
    rw [Real.div_rpow zero_le_one hT.le, Real.one_rpow, Real.rpow_sub hT, Real.rpow_one]
    rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ hT.ne', one_mul]
  have hweighted : r / T * x ^ p + s / T * y ^ p =
      T⁻¹ * (r ^ (1 - p) * (1 - t) ^ p + s ^ (1 - p) * t ^ p) := by
    dsimp only [x, y]
    rw [hterm hr (sub_nonneg.mpr ht.2), hterm hs ht.1, mul_add]
  have hnorm {u v : ℝ} : T⁻¹ * u ≤ T⁻¹ * v ↔ u ≤ v :=
    mul_le_mul_iff_right₀ (inv_pos.mpr hT)
  have hconv := (convexOn_rpow hp.le).2 (mem_Ici.mpr hx) (mem_Ici.mpr hy) hR.le hS.le hsum
  simp only [smul_eq_mul, hcenter, hone, hweighted] at hconv
  refine ⟨hnorm.mp hconv, ?_⟩
  have hxy : x = y ↔ t = s / T := by
    dsimp only [x, y]
    rw [div_eq_div_iff hr.ne' hs.ne', eq_div_iff hT.ne']
    dsimp only [T]
    constructor <;> intro h <;> linarith only [h, show (1 - t) * s + t * (r + s) - t * r = s by ring]
  constructor
  · intro h
    by_contra hn
    have hneq : x ≠ y := fun h ↦ hn (hxy.mp h)
    have hstrict := (strictConvexOn_rpow hp).2 (mem_Ici.mpr hx) (mem_Ici.mpr hy)
      hneq hR hS hsum
    simp only [smul_eq_mul, hcenter, hone, hweighted, h] at hstrict
    exact (lt_irrefl _) hstrict
  · intro ht
    have he := hxy.mpr ht
    have hvalue : r / T * x + s / T * y = y := by rw [he, ← add_mul, hsum, one_mul]
    have hpvalue : r / T * x ^ p + s / T * y ^ p = y ^ p := by
      rw [he, ← add_mul, hsum, one_mul]
    have heq : T⁻¹ * (r ^ (1 - p) * (1 - t) ^ p + s ^ (1 - p) * t ^ p) =
        T⁻¹ * T ^ (1 - p) := by
      rw [← hweighted, hpvalue, ← hone, ← hcenter, hvalue]
    exact (mul_left_cancel₀ (inv_ne_zero hT.ne')) heq

end WalkDimensions
