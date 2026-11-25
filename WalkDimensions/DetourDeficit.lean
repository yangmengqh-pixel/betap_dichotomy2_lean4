import WalkDimensions.DeficitEnergySplit
import WalkDimensions.DetourPotentialBound
import WalkDimensions.DyadicEndpoint
import WalkDimensions.ResistanceMetric

/-!
# A detour forces a positive triangle deficit at the endpoint

A small deficit at exponent one makes the upper branch of a
near-minimizing potential a near-minimizer for the first pair of points.
The detour would force that branch to be positive at its other endpoint.
-/

open Filter MeasureTheory Metric Set
open scoped ENNReal

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [ProperSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
  [μ.IsOpenPosMeasure] {p : ℝ} (E : PEnergy μ p)

omit [ProperSpace X] [SecondCountableTopology X] [μ.IsOpenPosMeasure] in
theorem capacity_toReal_eq_pointResistanceLength_rpow (x y : X) :
    (E.capacity {x} {y}).toReal = E.pointResistanceLength x y ^ (1 - p) := by
  have hp : p - 1 ≠ 0 := (sub_pos.mpr E.one_lt).ne'
  rw [pointResistanceLength, resistance, ENNReal.toReal_inv, ← Real.rpow_mul (by positivity)]
  have he : (p - 1)⁻¹ * (1 - p) = -1 := by
    rw [show 1 - p = -(p - 1) by ring, mul_neg, inv_mul_cancel₀ hp]
  rw [he, Real.rpow_neg (by positivity), Real.rpow_one, inv_inv]

theorem exists_positive_deficit_of_detour {d β : ℝ}
    (hvol : AhlforsRegular μ d) (hend : β - d = p - 1)
    {Γ : E.domain → Measure X} (hPI : E.Poincare Γ β)
    (hΓ : ∀ f, Γ f univ = (E.energy f : ℝ≥0∞)) (hcap : E.CapacityUpperBound β)
    (hunbounded : ¬ Bornology.IsBounded (univ : Set X)) {L a lower upper : ℝ}
    (hL : 0 ≤ L) (ha : 0 < a) (hLower : 0 < lower) (hUpper : 0 < upper) :
    ∃ κ > (0 : ℝ), ∀ (x y z : X) (r : ℝ), 0 < r → BalancedWithin lower upper dist x y z r →
      (∃ φ : ℝ → X, ContinuousOn φ (Icc 0 1) ∧ φ 0 = x ∧ φ 1 = z ∧
        ∀ t ∈ Icc (0 : ℝ) 1, dist (φ t) y ≤ L * r ∧ a * r ≤ dist (φ t) y) →
      κ ≤ relativeDeficit E.pointResistanceLength 1 x y z r := by
  have hβ : d < β := sub_pos.mp (hend ▸ sub_pos.mpr E.one_lt)
  obtain ⟨η, c₀, hη, hc₀, hDetour⟩ :=
    E.exists_point_potential_lower_bound_along_detour hvol hβ hPI hΓ hcap hunbounded hL ha hLower
  obtain ⟨c, C, hc, hC, hρ⟩ := E.pointResistanceLength_comparable hvol hβ hPI hΓ hcap
  let ρ := E.pointResistanceLength
  let lo := c * lower
  let hi := lo + C * upper
  have hlo : 0 < lo := mul_pos hc hLower
  have hilo : lo ≤ hi := le_add_of_nonneg_right (by positivity)
  obtain ⟨κ, hκ, hSplit⟩ := exists_normalized_upper_energy_bound E.one_lt hlo hilo hη
  refine ⟨κ, hκ, fun x y z r hr hbal hd ↦ ?_⟩
  obtain ⟨φ, hφ, hφx, hφz, hφA⟩ := hd
  by_contra! hDef
  let t := ρ x z / r
  let s := ρ y z / r
  let b := ρ x y / r
  let R := r ^ (d - β)
  have hR : 0 < R := Real.rpow_pos_of_pos hr _
  have hComp {u v : X} (h : dist u v ∈ Icc (lower * r) (upper * r)) : ρ u v / r ∈ Icc lo hi := by
    have he : (β - d) / (p - 1) = 1 := by
      rw [hend, div_self (sub_pos.mpr E.one_lt).ne']
    obtain ⟨h₁, h₂⟩ := hρ u v
    rw [he, Real.rpow_one] at h₁ h₂
    refine ⟨(le_div_iff₀ hr).mpr ?_, (div_le_iff₀ hr).mpr ?_⟩
    · exact (show lo * r ≤ c * dist u v by
        calc
          _ = c * (lower * r) := by dsimp [lo]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_left h.1 hc.le).trans h₁
    · exact h₂.trans ((mul_le_mul_of_nonneg_left h.2 hC.le).trans
        (show C * (upper * r) ≤ hi * r by
          calc
            _ = (C * upper) * r := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hlo.le) hr.le))
  have hb : b ∈ Icc lo hi := hComp hbal.1
  have hs : s ∈ Icc lo hi := hComp hbal.2.1
  have ht : t ∈ Icc lo hi := hComp hbal.2.2
  have htri : t ≤ b + s := by
    dsimp [t, b, s, ρ]
    rw [← add_div]
    exact div_le_div_of_nonneg_right (E.pointResistanceLength_triangle hvol hβ hPI hΓ hcap x y z) hr.le
  have hΔ : b + s - t ≤ κ := by
    dsimp [b, s, t, ρ]
    rw [← add_div, ← sub_div]
    exact (by simpa only [relativeDeficit, Real.rpow_one] using hDef.le)
  have hPow (u v : X) :
      (E.capacity {u} {v}).toReal / R = (ρ u v / r) ^ (1 - p) := by
    rw [E.capacity_toReal_eq_pointResistanceLength_rpow, Real.div_rpow (E.pointResistanceLength_nonneg u v) hr.le]
    have he : d - β = 1 - p := by linarith only [hend]
    dsimp [R]
    rw [he]
  have hcapFin : E.capacity {x} {z} ≠ ∞ := by
    have hxz : x ≠ z := dist_pos.mp ((mul_pos hLower hr).trans_le hbal.2.2.1)
    obtain ⟨_, _, _, _, h⟩ := E.singleton_capacity_bounds hvol hβ hPI hΓ hcap
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h x z hxz).2
  have hlt : E.capacity {x} {z} < ENNReal.ofReal ((E.capacity {x} {z}).toReal + κ * R) := by
    calc
      _ = ENNReal.ofReal ((E.capacity {x} {z}).toReal) := (ENNReal.ofReal_toReal hcapFin).symm
      _ < _ := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg).mpr
        (lt_add_of_pos_right _ (mul_pos hκ hR))
  obtain ⟨f, u, hu, huc, hfu, huRange, hux, huz, hEnergy⟩ :=
    E.exists_compact_singleton_capacity_approximant hvol hβ hPI hΓ hlt
  let ell := u y
  have hell : ell ∈ Icc (0 : ℝ) 1 := huRange y
  obtain ⟨fL, fH, hfL, hfH, _, hEH⟩ := E.exists_split_energy_at_level f hfu hu huc hell.1
  let uL (v : X) := min (u v) ell
  let uH (v : X) := max (u v - ell) 0
  have huL : Continuous uL := hu.min continuous_const
  have huH : Continuous uH := (hu.sub continuous_const).max continuous_const
  have hLcap : (E.capacity {y} {z}).toReal * ell ^ p ≤ (E.energy fL : ℝ) := by
    apply E.capacity_toReal_mul_rpow_le fL hfL huL hell.1
    · exact min_self _
    · change min (u z) ell = 0
      rw [huz, min_eq_left hell.1]
  have hHcap : (E.capacity {x} {y}).toReal * (1 - ell) ^ p ≤ (E.energy fH : ℝ) := by
    apply E.capacity_toReal_mul_rpow_le fH hfH huH (sub_nonneg.mpr hell.2)
    · change max (u x - ell) 0 = 1 - ell
      rw [hux, max_eq_left (sub_nonneg.mpr hell.2)]
    · exact max_eq_right (by change u y - u y ≤ 0; rw [sub_self])
  let H := (E.energy fH : ℝ) / R
  let Q := (E.energy fL : ℝ) / R
  have hH : b ^ (1 - p) * (1 - ell) ^ p ≤ H := by
    rw [← hPow x y, div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right hHcap hR.le
  have hL : s ^ (1 - p) * ell ^ p ≤ Q := by
    rw [← hPow y z, div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right hLcap hR.le
  have hsum : H + Q ≤ t ^ (1 - p) + κ := by
    rw [← hPow x z]
    have he : (E.energy f : ℝ) = (E.energy fL : ℝ) + (E.energy fH : ℝ) := by rw [hEH, NNReal.coe_add]
    dsimp [H, Q]
    rw [← add_div, add_comm (E.energy fH : ℝ), ← he]
    exact (div_le_div_of_nonneg_right hEnergy.le hR.le).trans_eq (by
      rw [add_div, mul_div_cancel_right₀ _ hR.ne'])
  obtain ⟨hell₁, hnorm⟩ := hSplit hb hs ht hell htri hΔ hH hL hsum
  have hden : 0 < 1 - ell := sub_pos.mpr hell₁
  let fH' : E.CompactCore :=
    ⟨fH, uH, hfH, huH, huc.comp_left (g := fun t ↦ max (t - ell) 0)
      (max_eq_right (by linarith only [hell.1]))⟩
  let v := fH'.smul (1 - ell)⁻¹
  have hvRange (w : X) : v.toFun w ∈ Icc (0 : ℝ) 1 := by
    change (1 - ell)⁻¹ * max (u w - ell) 0 ∈ _
    refine ⟨by positivity, ?_⟩
    apply le_trans (mul_le_mul_of_nonneg_left (max_le (sub_le_sub_right (huRange w).2 _) hden.le)
      (inv_nonneg.mpr hden.le))
    rw [inv_mul_cancel₀ hden.ne']
  have hvx : v.toFun x = 1 := by
    change (1 - ell)⁻¹ * max (u x - ell) 0 = 1
    rw [hux, max_eq_left hden.le, inv_mul_cancel₀ hden.ne']
  have hvy : v.toFun y = 0 := by
    change (1 - ell)⁻¹ * max (u y - u y) 0 = 0
    rw [sub_self, max_self, mul_zero]
  have hvz : v.toFun z = 0 := by
    change (1 - ell)⁻¹ * max (u z - ell) 0 = 0
    rw [huz, zero_sub, max_eq_right (neg_nonpos.mpr hell.1), mul_zero]
  have hvE : (E.energy v.domainElement : ℝ) - (E.capacity {x} {y}).toReal ≤ η * R := by
    have he := E.energy_smul_real (1 - ell)⁻¹ fH
    change (E.energy v.domainElement : ℝ) = _ at he
    rw [abs_of_pos (inv_pos.mpr hden), Real.inv_rpow hden.le, ← div_eq_inv_mul] at he
    rw [← hPow x y] at hnorm
    change ((E.energy fH : ℝ) / R) / (1 - ell) ^ p ≤ _ at hnorm
    rw [div_right_comm, ← he] at hnorm
    have hh := (div_le_iff₀ hR).mp hnorm
    rw [add_mul, div_mul_cancel₀ _ hR.ne'] at hh
    linarith only [hh]
  have hz := hDetour r hr x y z hbal.1.1 (by rw [dist_comm]; exact hbal.2.2.1)
    φ hφ hφx hφz hφA v hvRange hvx hvy hvE
  rw [hvz] at hz
  exact hc₀.not_ge hz

end WalkDimensions.PEnergy
