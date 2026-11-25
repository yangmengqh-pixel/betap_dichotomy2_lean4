import WalkDimensions.CapacityCutoffs
import WalkDimensions.EnergyClarkson
import WalkDimensions.Morrey

/-!
# Point capacity and resistance

The Morrey inequality supplies the lower bound on point capacity.
The ball capacity estimate supplies the upper bound.
-/

open Filter MeasureTheory Metric Set
open scoped ENNReal

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SecondCountableTopology X] {m : Measure X}
  [IsFiniteMeasureOnCompacts m] [m.IsOpenPosMeasure] {p : ℝ} (E : PEnergy m p)

/-- The effective resistance of the paper, including the zero and infinite
capacity conventions. -/
noncomputable def resistance (S T : Set X) : ℝ≥0∞ := (E.capacity S T)⁻¹

omit [ProperSpace X] [SecondCountableTopology X] [m.IsOpenPosMeasure] in
theorem resistance_anti {S T S' T' : Set X} (hS : S ⊆ S') (hT : T ⊆ T') :
    E.resistance S' T' ≤ E.resistance S T :=
  ENNReal.inv_le_inv.mpr (E.capacity_mono hS hT)

/-- Two-sided comparability of singleton capacities in the positive Morrey
range. -/
theorem singleton_capacity_bounds {d β : ℝ} (hvol : AhlforsRegular m d)
    (hβ : d < β) {Γ : E.domain → Measure X} (hPI : E.Poincare Γ β)
    (hΓ : ∀ f, Γ f univ = (E.energy f : ℝ≥0∞)) (hcap : E.CapacityUpperBound β) :
    ∃ L U : ℝ, 0 < L ∧ 0 < U ∧ ∀ x y : X, x ≠ y →
      ENNReal.ofReal (L * dist x y ^ (d - β)) ≤ E.capacity {x} {y} ∧
      E.capacity {x} {y} ≤ ENNReal.ofReal (U * dist x y ^ (d - β)) := by
  obtain ⟨H, hH, hholder⟩ := E.exists_holder_representative hvol hβ hPI hΓ
  obtain ⟨_, V, hV, hVbound⟩ := hvol
  obtain ⟨C, A, hC, hA, hCbound⟩ := hcap
  have hApos : 0 < A := zero_lt_one.trans hA
  have hp : 0 < p := zero_lt_one.trans E.one_lt
  refine ⟨(H ^ p)⁻¹, C * V * (2 * A) ^ (β - d), by positivity, by positivity, ?_⟩
  intro x y hxy
  let r := dist x y
  have hr : 0 < r := dist_pos.mpr hxy
  constructor
  · refine le_iInf fun f ↦ le_iInf fun hf ↦ ?_
    obtain ⟨u, hfu, S, T, hS, hT, hxS, hyT, hSu, hTu⟩ := hf
    obtain ⟨v, hv, hfv, hvbound⟩ := hholder f
    have huv := hfv.symm.trans hfu
    have hval (W : Set X) (hW : IsOpen W) (c : ℝ) (hWu : EqOn u (fun _ ↦ c) W) :
        EqOn v (fun _ ↦ c) W := by
      apply Measure.eqOn_open_of_ae_eq (μ := m) _ hW hv.continuousOn continuousOn_const
      filter_upwards [ae_restrict_of_ae (s := W) huv, ae_restrict_mem hW.measurableSet] with z hz hzW
      exact hz.trans (hWu hzW)
    have h1 := hval S hS 1 hSu (hxS (mem_singleton x))
    have h0 := hval T hT 0 hTu (hyT (mem_singleton y))
    have hh := hvbound x y
    rw [h1, h0, sub_zero, abs_one] at hh
    have h := Real.rpow_le_rpow (zero_le_one : (0 : ℝ) ≤ 1) hh hp.le
    rw [Real.one_rpow, Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow hH.le (apply_nonneg _ _), ← E.energy_eq_root_rpow,
      ← Real.rpow_mul hr.le, div_mul_cancel₀ _ hp.ne'] at h
    have hpow : r ^ (d - β) = (r ^ (β - d))⁻¹ := by
      rw [show d - β = -(β - d) by ring, Real.rpow_neg hr.le]
    rw [hpow, ← mul_inv]
    have hden : 0 < H ^ p * r ^ (β - d) := by positivity
    have hreal : (H ^ p * r ^ (β - d))⁻¹ ≤ (E.energy f : ℝ) := by
      rw [inv_eq_one_div, div_le_iff₀ hden]
      simpa only [mul_left_comm (E.energy f : ℝ), mul_assoc] using h
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal hreal
  · let s := r / (2 * A)
    have hs : 0 < s := by dsimp [s]; positivity
    have hys : y ∉ ball x (A * s) := by
      intro hy
      have hb := mem_ball.mp hy
      rw [dist_comm y x] at hb
      have he : A * s = r / 2 := by dsimp only [s]; field_simp
      rw [he] at hb
      exact (not_lt_of_ge (half_le_self hr.le)) hb
    calc
      _ ≤ E.capacity (ball x s) (ball x (A * s))ᶜ :=
        E.capacity_mono (singleton_subset_iff.mpr (mem_ball_self hs)) (singleton_subset_iff.mpr hys)
      _ ≤ ENNReal.ofReal (C * s ^ (-β)) * m (ball x s) := hCbound x s hs
      _ ≤ ENNReal.ofReal (C * s ^ (-β)) * ENNReal.ofReal (V * s ^ d) :=
        mul_le_mul_of_nonneg_left (hVbound x s hs).2 bot_le
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        calc
          _ = C * V * (s ^ (-β) * s ^ d) := by ring
          _ = C * V * s ^ (d - β) := by rw [← Real.rpow_add hs, sub_eq_neg_add]
          _ = _ := by
            dsimp only [s]
            rw [Real.div_rpow hr.le (by positivity), div_eq_mul_inv, ← Real.rpow_neg (by positivity),
              show -(d - β) = β - d by ring]
            ring

end WalkDimensions.PEnergy
