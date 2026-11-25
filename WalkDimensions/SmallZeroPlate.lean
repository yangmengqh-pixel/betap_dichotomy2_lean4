import WalkDimensions.BallPotential
import WalkDimensions.PointCapacityApproximation
import WalkDimensions.PointResistance
import WalkDimensions.CompactCore

/-!
# Enlarging a zero plate by a small ball
-/

open Filter MeasureTheory Metric Set
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [ProperSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
  [μ.IsOpenPosMeasure] {p : ℝ} (E : PEnergy μ p)

theorem exists_compact_test_zero_on_small_ball {d β : ℝ}
    (hvol : AhlforsRegular μ d) (hβ : d < β) {Γ : E.domain → Measure X}
    (hPI : E.Poincare Γ β) (hΓ : ∀ f, Γ f univ = (E.energy f : ℝ≥0∞))
    (hcap : E.CapacityUpperBound β) {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ (x y : X) (r : ℝ), 0 < r → a * r ≤ dist x y →
      ∃ f : E.CompactCore,
        (∀ z, f.toFun z ∈ Icc (0 : ℝ) 1) ∧ f.toFun x = 1 ∧
        EqOn f.toFun (fun _ ↦ 0) (closedBall y (δ * r)) ∧
        (E.energy f.domainElement : ℝ) ≤ (E.capacity {x} {y}).toReal + ε * r ^ (d - β) := by
  obtain ⟨_, C, _, hC, hCaps⟩ := E.singleton_capacity_bounds hvol hβ hPI hΓ hcap
  obtain ⟨H, hH, hHolder⟩ := E.exists_holder_representative hvol hβ hPI hΓ
  have hp := zero_lt_one.trans E.one_lt
  let e := (β - d) / p
  have he : 0 < e := div_pos (sub_pos.mpr hβ) hp
  let M := C * a ^ (d - β) + 1
  have hM : 0 < M := by dsimp [M]; positivity
  let C₀ := H * M ^ p⁻¹
  have hC₀ : 0 < C₀ := mul_pos hH (Real.rpow_pos_of_pos hM _)
  let ε₀ := min 1 (ε / 2)
  have hε₀ : 0 < ε₀ := lt_min zero_lt_one (half_pos hε)
  have hnear : ∀ᶠ t in 𝓝[>] (0 : ℝ), (1 - t) ^ (-p) < 1 + ε / (2 * M) := by
    have hBase : ContinuousAt (fun t : ℝ ↦ 1 - t) 0 := continuousAt_const.sub continuousAt_id
    have hf := hBase.rpow_const (p := -p) (Or.inl (by norm_num))
    have ht : (fun t : ℝ ↦ (1 - t) ^ (-p)) 0 < 1 + ε / (2 * M) := by
      simp only [sub_zero, Real.one_rpow]
      exact lt_add_of_pos_right _ (by positivity)
    exact (hf.tendsto.eventually_lt_const ht).filter_mono nhdsWithin_le_nhds
  have hRangeNear : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo (0 : ℝ) 1 :=
    Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)
  obtain ⟨t, ht, htE⟩ := (hRangeNear.and hnear).exists
  let δ := (t / C₀) ^ e⁻¹
  have hδ : 0 < δ := Real.rpow_pos_of_pos (div_pos ht.1 hC₀) _
  have hδE : C₀ * δ ^ e = t := by
    dsimp [δ]
    rw [← Real.rpow_mul (div_nonneg ht.1.le hC₀.le), inv_mul_cancel₀ he.ne', Real.rpow_one]
    field_simp [hC₀.ne']
  refine ⟨δ, hδ, fun x y r hr hxy ↦ ?_⟩
  let R := r ^ (d - β)
  have hR : 0 < R := Real.rpow_pos_of_pos hr _
  have hxy₀ : x ≠ y := dist_pos.mp ((mul_pos ha hr).trans_le hxy)
  have hCapRange := (hCaps x y hxy₀).2
  have hcapFin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hCapRange
  have hcapReal : (E.capacity {x} {y}).toReal ≤ C * a ^ (d - β) * R := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hCapRange
    rw [ENNReal.toReal_ofReal (by positivity)] at h
    apply h.trans
    rw [mul_assoc, ← Real.mul_rpow ha.le hr.le]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (mul_pos ha hr) hxy
      (sub_nonpos.mpr hβ.le)) hC.le
  have hlt : E.capacity {x} {y} < ENNReal.ofReal ((E.capacity {x} {y}).toReal + ε₀ * R) := by
    calc
      _ = ENNReal.ofReal ((E.capacity {x} {y}).toReal) := (ENNReal.ofReal_toReal hcapFin).symm
      _ < _ := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg).mpr
        (lt_add_of_pos_right _ (mul_pos hε₀ hR))
  obtain ⟨f, u, hu, huc, hfu, hRange, hux, huy, hfE⟩ :=
    E.exists_compact_singleton_capacity_approximant hvol hβ hPI hΓ hlt
  have hE : (E.energy f : ℝ) ≤ M * R := by
    have hε₀' : ε₀ * R ≤ 1 * R := mul_le_mul_of_nonneg_right (min_le_left _ _) hR.le
    dsimp [M]
    rw [add_mul]
    linarith only [hfE, hcapReal, hε₀']
  have hroot : E.rootSeminorm f ≤ M ^ p⁻¹ * r ^ (-e) := by
    rw [E.rootSeminorm_apply]
    have h := Real.rpow_le_rpow (NNReal.coe_nonneg _) hE (inv_nonneg.mpr hp.le)
    change (E.energy f : ℝ) ^ p⁻¹ ≤ (M * r ^ (d - β)) ^ p⁻¹ at h
    rw [Real.mul_rpow hM.le (by positivity), ← Real.rpow_mul hr.le,
      show (d - β) * p⁻¹ = -e by dsimp [e]; rw [div_eq_mul_inv]; ring] at h
    exact h
  obtain ⟨v, hv, hfv, hHol⟩ := hHolder f
  have hEq := Measure.eq_of_ae_eq (hfv.symm.trans hfu) hv hu
  have hSmall (z : X) (hz : z ∈ closedBall y (δ * r)) : u z ≤ t := by
    have h := hHol z y
    rw [hEq, huy, sub_zero, abs_of_nonneg (hRange z).1] at h
    have hdist : dist z y ^ e ≤ (δ * r) ^ e := Real.rpow_le_rpow dist_nonneg (mem_closedBall.mp hz) he.le
    apply h.trans
    calc
      _ ≤ H * (M ^ p⁻¹ * r ^ (-e)) * (δ * r) ^ e := mul_le_mul
        (mul_le_mul_of_nonneg_left hroot hH.le) hdist (by positivity) (by positivity)
      _ = _ := by
        rw [Real.mul_rpow hδ.le hr.le]
        calc
          _ = (C₀ * δ ^ e) * (r ^ (-e) * r ^ e) := by dsimp [C₀]; ring
          _ = _ := by rw [hδE, ← Real.rpow_add hr, neg_add_cancel, Real.rpow_zero, mul_one]
  obtain ⟨g, hg, hgE⟩ := E.exists_unitClip_comp f hfu ht.1.le ht.2
  let w := unitClip t 1 ∘ u
  have hw : Continuous w := ((hu.sub continuous_const).div_const _).max continuous_const |>.min continuous_const
  let G : E.CompactCore := ⟨g, w, hg, hw, huc.comp_left (unitClip_eq_zero ht.2 ht.1.le)⟩
  refine ⟨G, fun z ↦ unitClip_mem_Icc _ _ _, ?_, fun z hz ↦ unitClip_eq_zero ht.2 (hSmall z hz), ?_⟩
  · change unitClip t 1 (u x) = 1
    rw [hux]
    exact unitClip_eq_one ht.2 le_rfl
  · change (E.energy g : ℝ) ≤ _
    apply hgE.trans
    have hFactor : (1 - t) ^ (-p) * (E.energy f : ℝ) ≤
        (1 + ε / (2 * M)) * (E.energy f : ℝ) :=
      mul_le_mul_of_nonneg_right htE.le (NNReal.coe_nonneg _)
    apply hFactor.trans
    have hExtra : ε / (2 * M) * (E.energy f : ℝ) ≤ ε / 2 * R := by
      apply (mul_le_mul_of_nonneg_left hE (by positivity)).trans_eq
      field_simp [hM.ne']
    have hεBound : ε₀ * R ≤ (ε / 2) * R :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) hR.le
    rw [add_mul, one_mul]
    linarith only [hExtra, hεBound, hfE]

end WalkDimensions.PEnergy
