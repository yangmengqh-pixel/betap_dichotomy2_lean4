import WalkDimensions.BallPotential
import WalkDimensions.CompactCore

/-!
# A point-to-boundary barrier

A compactly supported point-plate minimizer stays uniformly positive
near its prescribed point by the Morrey estimate.
-/

open Filter MeasureTheory Metric Set
open scoped ENNReal

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [ProperSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
  [μ.IsOpenPosMeasure] {p : ℝ} (E : PEnergy μ p)

theorem exists_point_barrier {d β : ℝ} (hvol : AhlforsRegular μ d)
    (hβ : d < β) {Γ : E.domain → Measure X} (hPI : E.Poincare Γ β)
    (hΓ : ∀ f, Γ f univ = (E.energy f : ℝ≥0∞)) (hcap : E.CapacityUpperBound β)
    (hunbounded : ¬ Bornology.IsBounded (univ : Set X)) :
    ∃ C A b : ℝ, 0 < C ∧ 1 < A ∧ 0 < b ∧ ∀ (z : X) (r : ℝ), 0 < r →
      ∃ v : E.CompactCore, E.UnitPlate {z} (closedBall z (A * r)) v.domainElement v.toFun ∧
        (∀ g w, E.UnitPlate {z} (closedBall z (A * r)) g w → E.energy v.domainElement ≤ E.energy g) ∧
        (E.energy v.domainElement : ℝ) ≤ C * r ^ (d - β) ∧
        ∀ w, dist w z ≤ b * r → (1 / 2 : ℝ) ≤ v.toFun w := by
  obtain ⟨D, A, hD, hA, hcut⟩ := E.exists_continuous_ball_cutoff hvol hβ hPI hΓ hcap
  obtain ⟨H, hH, hu⟩ := E.exists_holder_representative hvol hβ hPI hΓ
  obtain ⟨hd, V, hV, hVol⟩ := hvol
  let C := D * V
  have hC : 0 < C := mul_pos hD hV
  have hp := zero_lt_one.trans E.one_lt
  let e := (β - d) / p
  have he : 0 < e := div_pos (sub_pos.mpr hβ) hp
  let T := H * C ^ p⁻¹
  have hT : 0 < T := mul_pos hH (Real.rpow_pos_of_pos hC _)
  let b := (1 / (2 * T)) ^ e⁻¹
  have hb : 0 < b := Real.rpow_pos_of_pos (by positivity) _
  have hbpow : T * b ^ e = 1 / 2 := by
    dsimp [b]
    rw [← Real.rpow_mul (by positivity), inv_mul_cancel₀ he.ne', Real.rpow_one]
    field_simp [hT.ne']
  refine ⟨C, A, b, hC, hA, hb, fun z r hr ↦ ?_⟩
  let S := closedBall z (A * r)
  have hS : IsCompact S := isCompact_closedBall _ _
  have hSproper : Sᶜ.Nonempty := by
    by_contra! h
    exact hunbounded ((compl_empty_iff.mp h) ▸ hS.isBounded)
  obtain ⟨g, u, hgu, hgE⟩ := hcut z r hr
  have hgu' : E.UnitPlate {z} S g u :=
    ⟨hgu.1, hgu.2.1, hgu.2.2.1,
      hgu.2.2.2.1.mono (singleton_subset_iff.mpr (mem_ball_self hr)), hgu.2.2.2.2⟩
  obtain ⟨f, v, hv, hmin⟩ :=
    E.exists_unitPlate_minimizer ⟨hd, V, hV, hVol⟩ hβ hPI hΓ hS hSproper ⟨g, u, hgu'⟩
  let f' : E.CompactCore := ⟨f, v, hv.2.1, hv.1, HasCompactSupport.intro hS hv.2.2.2.2⟩
  have hE : (E.energy f : ℝ) ≤ C * r ^ (d - β) := by
    have h₁ : (E.energy f : ℝ≥0∞) ≤ ENNReal.ofReal (C * r ^ (d - β)) := by
      calc
        _ ≤ (E.energy g : ℝ≥0∞) := ENNReal.coe_le_coe.mpr (hmin g u hgu')
        _ ≤ _ := hgE
        _ ≤ ENNReal.ofReal (D * r ^ (-β)) * ENNReal.ofReal (V * r ^ d) :=
          mul_le_mul_of_nonneg_left (hVol z r hr).2 bot_le
        _ = _ := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [sub_eq_add_neg, Real.rpow_add hr]
          dsimp [C]
          ring
    rw [← ENNReal.ofReal_coe_nnreal] at h₁
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h₁
  refine ⟨f', hv, hmin, hE, ?_⟩
  intro w hw
  obtain ⟨u', hu', hfu', hBound⟩ := hu f
  have heq := Measure.eq_of_ae_eq (hfu'.symm.trans hv.2.1) hu' hv.1
  have hroot : E.rootSeminorm f ≤ C ^ p⁻¹ * r ^ (-e) := by
    rw [E.rootSeminorm_apply]
    have h := Real.rpow_le_rpow (NNReal.coe_nonneg _) hE (inv_nonneg.mpr hp.le)
    rw [Real.mul_rpow hC.le (by positivity), ← Real.rpow_mul hr.le] at h
    have heq : (d - β) * p⁻¹ = -e := by dsimp [e]; rw [div_eq_mul_inv]; ring
    rwa [heq] at h
  have hdiff := hBound z w
  rw [heq, hv.2.2.2.1 (mem_singleton z), dist_comm z w] at hdiff
  have hW : dist w z ^ e ≤ (b * r) ^ e := Real.rpow_le_rpow dist_nonneg hw he.le
  have hf : |1 - v w| ≤ 1 / 2 := by
    apply hdiff.trans
    calc
      _ ≤ H * (C ^ p⁻¹ * r ^ (-e)) * (b * r) ^ e :=
        mul_le_mul (mul_le_mul_of_nonneg_left hroot hH.le) hW (by positivity) (by positivity)
      _ = _ := by
        rw [Real.mul_rpow hb.le hr.le]
        calc
          _ = (T * b ^ e) * (r ^ (-e) * r ^ e) := by dsimp [T]; ring
          _ = _ := by rw [hbpow, ← Real.rpow_add hr, neg_add_cancel, Real.rpow_zero, mul_one]
  linarith only [le_abs_self (1 - v w), hf]

end WalkDimensions.PEnergy
