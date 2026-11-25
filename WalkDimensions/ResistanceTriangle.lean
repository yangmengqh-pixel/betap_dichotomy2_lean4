import WalkDimensions.PointCapacityApproximation
import WalkDimensions.SeriesEnergy

/-!
# The resistance triangle inequality

Splitting a compact near-minimizer at its value at the middle point
bounds the two resulting energies by the corresponding point capacities.
The series energy identity then implies the triangle inequality.
-/

open MeasureTheory Metric Set
open scoped ENNReal

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {m : Measure X} [IsFiniteMeasureOnCompacts m] {p : ℝ} (E : PEnergy m p)

theorem capacity_singleton_self (x : X) : E.capacity {x} {x} = ∞ := by
  apply top_unique
  refine le_iInf fun f ↦ le_iInf fun h ↦ ?_
  obtain ⟨u, _, U, V, _, _, hU, hV, h1, h0⟩ := h
  have he : (1 : ℝ) = 0 := (h1 (hU (mem_singleton x))).symm.trans (h0 (hV (mem_singleton x)))
  exact (one_ne_zero he).elim

/-- The point resistance raised to the power (1/(p-1)\). -/
noncomputable def pointResistanceLength (x y : X) : ℝ :=
  (E.resistance {x} {y}).toReal ^ (p - 1)⁻¹

theorem pointResistanceLength_self (x : X) : E.pointResistanceLength x x = 0 := by
  have h : 0 < (p - 1)⁻¹ := inv_pos.mpr (sub_pos.mpr E.one_lt)
  rw [pointResistanceLength, resistance, E.capacity_singleton_self, ENNReal.inv_top,
    ENNReal.toReal_zero, Real.zero_rpow h.ne']

theorem pointResistanceLength_nonneg (x y : X) : 0 ≤ E.pointResistanceLength x y := by
  unfold pointResistanceLength
  positivity

theorem capacity_toReal_mul_rpow_le {u : X → ℝ} (f : E.domain)
    (hfu : (f : RealLp m p) =ᵐ[m] u) (hu : Continuous u) {x y : X} {a : ℝ}
    (ha : 0 ≤ a) (hx : u x = a) (hy : u y = 0) :
    (E.capacity {x} {y}).toReal * a ^ p ≤ (E.energy f : ℝ) := by
  have hp : 0 < p := zero_lt_one.trans E.one_lt
  rcases ha.eq_or_lt with h₀ | h₀
  · rw [← h₀, Real.zero_rpow hp.ne', mul_zero]
    positivity
  · obtain ⟨g, hg, hgE⟩ := E.exists_unitClip_comp f hfu (le_refl (0 : ℝ)) h₀
    let v : X → ℝ := unitClip 0 a ∘ u
    have hv : Continuous v := ((hu.sub continuous_const).div_const _).max continuous_const |>.min continuous_const
    have hvx : v x = 1 := unitClip_eq_one h₀ hx.ge
    have hvy : v y = 0 := unitClip_eq_zero h₀ hy.le
    have hcap := ENNReal.toReal_mono ENNReal.coe_ne_top
      (E.singleton_capacity_le_of_point_values hg hv hvx hvy)
    have h := hcap.trans (by simpa only [ENNReal.coe_toReal, sub_zero] using hgE)
    calc
      _ ≤ (a ^ (-p) * (E.energy f : ℝ)) * a ^ p :=
        mul_le_mul_of_nonneg_right h (Real.rpow_nonneg ha p)
      _ = (a ^ (-p) * a ^ p) * (E.energy f : ℝ) := by ring
      _ = _ := by rw [← Real.rpow_add h₀, neg_add_cancel, Real.rpow_zero, one_mul]

variable [ProperSpace X] [SecondCountableTopology X] [m.IsOpenPosMeasure]

theorem pointResistanceLength_triangle {d β : ℝ} (hvol : AhlforsRegular m d)
    (hβ : d < β) {Γ : E.domain → Measure X} (hPI : E.Poincare Γ β)
    (hΓ : ∀ f, Γ f univ = (E.energy f : ℝ≥0∞)) (hcap : E.CapacityUpperBound β)
    (x y z : X) :
    E.pointResistanceLength x z ≤ E.pointResistanceLength x y + E.pointResistanceLength y z := by
  by_cases hxy : x = y
  · subst y
    simp only [E.pointResistanceLength_self, zero_add, le_refl]
  by_cases hyz : y = z
  · subst z
    simp only [E.pointResistanceLength_self, add_zero, le_refl]
  by_cases hxz : x = z
  · subst z
    rw [E.pointResistanceLength_self]
    exact add_nonneg (E.pointResistanceLength_nonneg _ _) (E.pointResistanceLength_nonneg _ _)
  obtain ⟨L, U, hL, _, hC⟩ := E.singleton_capacity_bounds hvol hβ hPI hΓ hcap
  have hcapPos {a b : X} (hab : a ≠ b) : 0 < E.capacity {a} {b} :=
    (ENNReal.ofReal_pos.mpr (mul_pos hL (Real.rpow_pos_of_pos (dist_pos.mpr hab) _))).trans_le (hC a b hab).1
  have hcapFin {a b : X} (hab : a ≠ b) : E.capacity {a} {b} ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hC a b hab).2
  have hCPos {a b : X} (hab : a ≠ b) : 0 < (E.capacity {a} {b}).toReal :=
    ENNReal.toReal_pos (hcapPos hab).ne' (hcapFin hab)
  have hp : 0 < p - 1 := sub_pos.mpr E.one_lt
  have hρ (a b : X) (hab : a ≠ b) : 0 < E.pointResistanceLength a b := by
    rw [pointResistanceLength, resistance, ENNReal.toReal_inv]
    exact Real.rpow_pos_of_pos (inv_pos.mpr (hCPos hab)) _
  have hρpow (a b : X) (hab : a ≠ b) :
      (E.pointResistanceLength a b) ^ (1 - p) = (E.capacity {a} {b}).toReal := by
    have he : (p - 1)⁻¹ * (1 - p) = -1 := by
      rw [show 1 - p = -(p - 1) by ring, mul_neg, inv_mul_cancel₀ hp.ne']
    rw [pointResistanceLength, resistance, ENNReal.toReal_inv,
      ← Real.rpow_mul (inv_nonneg.mpr (hCPos hab).le), he, Real.rpow_neg_one, inv_inv]
  let R := E.pointResistanceLength x y + E.pointResistanceLength y z
  have hR : 0 < R := add_pos (hρ x y hxy) (hρ y z hyz)
  apply (Real.rpow_le_rpow_iff_of_neg hR (hρ x z hxz) (by linarith only [E.one_lt] : 1 - p < 0)).1
  rw [hρpow x z hxz]
  by_contra! hc
  obtain ⟨b, hb, hb'⟩ := exists_between hc
  have hbcap : E.capacity {x} {z} < ENNReal.ofReal b := by
    rw [← ENNReal.ofReal_toReal (hcapFin hxz)]
    exact ENNReal.ofReal_lt_ofReal_iff'.mpr ⟨hb, (hCPos hxz).trans hb⟩
  obtain ⟨f, u, hu, huc, hfu, hunit, hx, hz, hE⟩ :=
    E.exists_compact_singleton_capacity_approximant hvol hβ hPI hΓ hbcap
  let t := u y
  have ht : t ∈ Icc (0 : ℝ) 1 := hunit y
  obtain ⟨l, h, hl, hh, _, hsum⟩ := E.exists_split_energy_at_level f hfu hu huc ht.1
  have hlow := E.capacity_toReal_mul_rpow_le l hl (hu.min continuous_const) ht.1
    (x := y) (y := z) (min_self _) (by simp only [hz, min_eq_left ht.1])
  have hhigh := E.capacity_toReal_mul_rpow_le h hh ((hu.sub continuous_const).max continuous_const)
    (sub_nonneg.mpr ht.2) (x := x) (y := y)
    (by simp only [hx, max_eq_left (sub_nonneg.mpr ht.2)]) (by simp [t])
  have hseries := (series_energy_minimum E.one_lt (hρ x y hxy) (hρ y z hyz) ht).1
  rw [hρpow x y hxy, hρpow y z hyz] at hseries
  have hEf : (E.energy f : ℝ) = (E.energy l : ℝ) + (E.energy h : ℝ) := by
    rw [hsum, NNReal.coe_add]
  exact (not_lt_of_ge ((hseries.trans (by
    rw [hEf, add_comm (E.energy l : ℝ)]
    exact add_le_add hhigh hlow)) : R ^ (1 - p) ≤ (E.energy f : ℝ))) (hE.trans hb')

end WalkDimensions.PEnergy
