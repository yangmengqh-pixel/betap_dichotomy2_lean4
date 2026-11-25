import WalkDimensions.LocalPlateComparison
import WalkDimensions.PointBarrier

/-!
# Propagation of positivity for near-minimizing point potentials
-/

open Filter MeasureTheory Metric Set
open scoped ENNReal

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [ProperSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
  [μ.IsOpenPosMeasure] {p : ℝ} (E : PEnergy μ p)

private theorem exists_uniform_power_gap {p q C t : ℝ} (hp : 0 < p) (hq : 0 < q)
    (ht : 0 < t) :
    ∃ δ > (0 : ℝ), ∀ a ∈ Icc (0 : ℝ) C, ∀ b ∈ Icc (0 : ℝ) δ,
      (2 * (a + b) ^ p⁻¹) ^ q - (2 * a ^ p⁻¹) ^ q < t ^ q := by
  let F (s : ℝ) := (2 * s ^ p⁻¹) ^ q
  have hF : Continuous F :=
    (Real.continuous_rpow_const hq.le).comp ((Real.continuous_rpow_const (inv_nonneg.mpr hp.le)).const_mul 2)
  have hUC := isCompact_Icc.uniformContinuousOn_of_continuous
    (s := Icc (0 : ℝ) (C + 1)) hF.continuousOn
  obtain ⟨δ, hδ, hgap⟩ := Metric.uniformContinuousOn_iff.mp hUC (t ^ q) (Real.rpow_pos_of_pos ht q)
  refine ⟨min (δ / 2) 1, lt_min (half_pos hδ) zero_lt_one, fun a ha b hb ↦ ?_⟩
  have hA : a ∈ Icc (0 : ℝ) (C + 1) := ⟨ha.1, by linarith only [ha.2]⟩
  have hB : a + b ∈ Icc (0 : ℝ) (C + 1) :=
    ⟨add_nonneg ha.1 hb.1, add_le_add ha.2 (hb.2.trans (min_le_right _ _))⟩
  have h := hgap (a + b) hB a hA (by
    rw [Real.dist_eq, add_sub_cancel_left, abs_of_nonneg hb.1]
    exact (hb.2.trans (min_le_left _ _)).trans_lt (half_lt_self hδ))
  rw [Real.dist_eq] at h
  exact (le_abs_self _).trans_lt h

theorem exists_point_propagation {d β : ℝ} (hvol : AhlforsRegular μ d)
    (hβ : d < β) {Γ : E.domain → Measure X} (hPI : E.Poincare Γ β)
    (hΓ : ∀ f, Γ f univ = (E.energy f : ℝ≥0∞)) (hcap : E.CapacityUpperBound β)
    (hunbounded : ¬ Bornology.IsBounded (univ : Set X)) :
    ∃ A b : ℝ, 1 < A ∧ 0 < b ∧ ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ (f : E.CompactCore) (x y z w : X) (r : ℝ), 0 < r →
        (∀ t, f.toFun t ∈ Icc (0 : ℝ) 1) → f.toFun x = 1 → f.toFun y = 0 →
        A * r < dist x z → A * r < dist y z → dist w z ≤ b * r →
        (E.energy f.domainElement : ℝ) - (E.capacity {x} {y}).toReal ≤ δ * r ^ (d - β) →
        f.toFun z / 2 - ε ≤ f.toFun w := by
  obtain ⟨C, A, b, hC, hA, hb, hbarrier⟩ := E.exists_point_barrier hvol hβ hPI hΓ hcap hunbounded
  obtain ⟨q, hq, hcomp⟩ := CompactCore.exists_min_plate_root_gap E
  obtain ⟨H, hH, hHolder⟩ := E.exists_holder_representative hvol hβ hPI hΓ
  have hp := zero_lt_one.trans E.one_lt
  let e := (β - d) / p
  have he : 0 < e := div_pos (sub_pos.mpr hβ) hp
  refine ⟨A, b, hA, hb, fun ε hε ↦ ?_⟩
  let t := ε / (H * b ^ e)
  have ht : 0 < t := div_pos hε (mul_pos hH (Real.rpow_pos_of_pos hb _))
  obtain ⟨δ, hδ, hgap⟩ := exists_uniform_power_gap hp hq (C := C) ht
  refine ⟨δ, hδ, fun f x y z w r hr hf hfx hfy hx hy hw hDef ↦ ?_⟩
  let a := f.toFun z
  by_cases ha : 0 < a
  swap
  · have hzero : a = 0 := le_antisymm (le_of_not_gt ha) (hf z).1
    change a / 2 - ε ≤ f.toFun w
    rw [hzero, zero_div, zero_sub]
    exact (neg_nonpos.mpr hε.le).trans (hf w).1
  obtain ⟨v, hplate, hmin, hvE, hvw⟩ := hbarrier z r hr
  let V := v.smul a
  let W := f.minAddConst V (a := 0) le_rfl
  let D := (E.energy f.domainElement : ℝ) - (E.capacity {x} {y}).toReal
  let R := r ^ (d - β)
  have hR : 0 < R := Real.rpow_pos_of_pos hr _
  let s := (E.energy V.domainElement : ℝ) / R
  let k := D / R
  have hs : s ∈ Icc (0 : ℝ) C := by
    refine ⟨div_nonneg (NNReal.coe_nonneg _) hR.le, (div_le_iff₀ hR).mpr ?_⟩
    have hEnergy := E.energy_smul_real a v.domainElement
    change (E.energy V.domainElement : ℝ) = _ at hEnergy
    have hA : |a| ^ p ≤ 1 := by
      rw [abs_of_pos ha]
      exact Real.rpow_le_one (hf z).1 (hf z).2 hp.le
    rw [hEnergy]
    exact (mul_le_mul_of_nonneg_right hA (NNReal.coe_nonneg _)).trans (by simpa only [one_mul] using hvE)
  have hk : k ∈ Icc (0 : ℝ) δ := by
    have hc := ENNReal.toReal_mono ENNReal.coe_ne_top
      (E.singleton_capacity_le_of_point_values f.ae_eq f.continuous hfx hfy)
    rw [ENNReal.coe_toReal] at hc
    exact ⟨div_nonneg (sub_nonneg.mpr hc) hR.le, (div_le_iff₀ hR).mpr hDef⟩
  have hx' : x ∉ closedBall z (A * r) := fun h ↦ hx.not_ge (mem_closedBall.mp h)
  have hy' : y ∉ closedBall z (A * r) := fun h ↦ hy.not_ge (mem_closedBall.mp h)
  have hbound := hcomp f v ha (fun u ↦ (hf u).1) hfx hfy rfl hx' hy' hplate hmin
  change E.rootSeminorm (W.domainElement - V.domainElement) ^ q ≤
    (2 * ((E.energy V.domainElement : ℝ) + D) ^ p⁻¹) ^ q -
      (2 * E.rootSeminorm V.domainElement) ^ q at hbound
  have hEqE : (E.energy V.domainElement : ℝ) = s * R := by
    exact (div_mul_cancel₀ _ hR.ne').symm
  have hEqD : D = k * R := (div_mul_cancel₀ _ hR.ne').symm
  have hrootR : R ^ p⁻¹ = r ^ (-e) := by
    rw [← Real.rpow_mul hr.le]
    congr 1
    dsimp [e]
    rw [div_eq_mul_inv]
    ring
  rw [E.rootSeminorm_apply V.domainElement, hEqE, hEqD, ← add_mul,
    Real.mul_rpow (add_nonneg hs.1 hk.1) hR.le, Real.mul_rpow hs.1 hR.le, hrootR] at hbound
  have heqpow (u : ℝ) (hu : 0 ≤ u) :
      (2 * (u ^ p⁻¹ * r ^ (-e))) ^ q = (2 * u ^ p⁻¹) ^ q * (r ^ (-e)) ^ q := by
    rw [← mul_assoc, Real.mul_rpow (by positivity) (Real.rpow_nonneg hr.le _)]
  rw [heqpow (s + k) (add_nonneg hs.1 hk.1), heqpow s hs.1, ← sub_mul] at hbound
  have hg := mul_lt_mul_of_pos_right (hgap s hs k hk)
    (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hr (-e)) q)
  have hrootlt : E.rootSeminorm (W.domainElement - V.domainElement) < t * r ^ (-e) := by
    apply (Real.rpow_lt_rpow_iff (apply_nonneg _ _) (by positivity) hq).mp
    rw [Real.mul_rpow ht.le (by positivity)]
    exact hbound.trans_lt hg
  let J := W.sub V
  obtain ⟨u, hu, hJu, hJuBound⟩ := hHolder J.domainElement
  have hEq := Measure.eq_of_ae_eq (hJu.symm.trans J.ae_eq) hu J.continuous
  have hVz : V.toFun z = a := by
    change a * v.toFun z = a
    rw [hplate.2.2.2.1 (mem_singleton z), mul_one]
  have hWz : W.toFun z = a := by
    change min (f.toFun z) (V.toFun z + 0) = a
    rw [add_zero, hVz, min_self]
  have hJz : J.toFun z = 0 := by
    change W.toFun z + -V.toFun z = 0
    rw [hWz, hVz, add_neg_cancel]
  have hBound := hJuBound w z
  rw [hEq, hJz, sub_zero] at hBound
  have hJdiff : |J.toFun w| ≤ ε := by
    apply hBound.trans
    change H * E.rootSeminorm (W.domainElement + -V.domainElement) * dist w z ^ e ≤ _
    rw [← sub_eq_add_neg]
    calc
      _ ≤ H * (t * r ^ (-e)) * (b * r) ^ e :=
        mul_le_mul (mul_le_mul_of_nonneg_left hrootlt.le hH.le)
          (Real.rpow_le_rpow dist_nonneg hw he.le) (by positivity) (by positivity)
      _ = (H * b ^ e) * t := by
        rw [Real.mul_rpow hb.le hr.le]
        calc
          _ = (H * b ^ e) * t * (r ^ (-e) * r ^ e) := by ring
          _ = _ := by rw [← Real.rpow_add hr, neg_add_cancel, Real.rpow_zero, mul_one]
      _ = _ := by dsimp [t]; field_simp
  have hLower := (neg_le_abs (J.toFun w)).trans hJdiff
  have hW₀ : W.toFun w ≤ f.toFun w := min_le_left _ _
  have hV₀ : a / 2 ≤ V.toFun w := by
    change a / 2 ≤ a * v.toFun w
    rw [div_eq_mul_inv, ← one_div]
    exact mul_le_mul_of_nonneg_left (hvw w hw) ha.le
  have hJw : J.toFun w = W.toFun w - V.toFun w := rfl
  change a / 2 - ε ≤ _
  linarith only [hLower, hW₀, hV₀, hJw]

end WalkDimensions.PEnergy
