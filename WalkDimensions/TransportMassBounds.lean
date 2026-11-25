import WalkDimensions.EnergyDerivativeWeights
import WalkDimensions.PotentialMeasureBounds

/-!
# Mass and variation bounds in a rescaled ball
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal Topology

namespace WalkDimensions

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem eventually_closedBall_compl_mass_le {ν : Measure X} [IsFiniteMeasure ν]
    {x : X} {W : Set X} {c A b : ℝ} (hA : 0 ≤ A) (hb : 0 < b)
    (ht : Tendsto (fun r : ℝ ↦ ν (ball x r \ W) / (ENNReal.ofReal r) ^ c) (𝓝[>] 0) (𝓝 0)) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, (ν (closedBall x (A * r) \ W)).toReal ≤ b * r ^ c := by
  let L := A + 1
  have hL : 0 < L := by dsimp only [L]; linarith only [hA]
  let q := b / L ^ c
  have hq : 0 < q := div_pos hb (Real.rpow_pos_of_pos hL _)
  have hq' := ht.eventually_lt_const (ENNReal.ofReal_pos.mpr hq)
  obtain ⟨ε, hε, hfine⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hq'
  filter_upwards [Ioo_mem_nhdsGT (div_pos hε hL)] with r hr
  have hr' : L * r ∈ Ioo 0 ε := ⟨mul_pos hL hr.1, by
    rw [mul_comm]
    exact (lt_div_iff₀ hL).mp hr.2⟩
  have hpos := ENNReal.ofReal_pos.mpr hr'.1
  have hp := ENNReal.rpow_pos (p := c) hpos ENNReal.ofReal_ne_top
  have hT : (ENNReal.ofReal (L * r)) ^ c ≠ ∞ :=
    ENNReal.rpow_ne_top_of_ne_zero hpos.ne' ENNReal.ofReal_ne_top
  have hbound := ((ENNReal.div_lt_iff (Or.inl hp.ne') (Or.inl hT)).mp (hfine hr')).le
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hT) hbound
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hq.le, ENNReal.ofReal_rpow_of_pos hr'.1,
    ENNReal.toReal_ofReal (Real.rpow_nonneg hr'.1.le _), Real.mul_rpow hL.le hr.1.le] at hreal
  have hsub : closedBall x (A * r) \ W ⊆ ball x (L * r) \ W := by
    apply sdiff_subset_sdiff_left
    apply closedBall_subset_ball
    dsimp only [L]
    nlinarith only [hr.1]
  apply (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)).trans
  refine hreal.trans_eq ?_
  dsimp only [q]
  rw [← mul_assoc, div_mul_cancel₀ _ (Real.rpow_pos_of_pos hL _).ne']

theorem exists_closedBall_mass_bound_of_holder {ν : Measure X} [IsFiniteMeasure ν]
    {u : X → ℝ} {c H A : ℝ} (hc : 0 ≤ c) (hH : 0 < H) (hA : 0 ≤ A)
    (hu : Continuous u) (hHolder : ∀ y z, |u y - u z| ≤ H * dist y z ^ c)
    {M : ℝ≥0∞} (hM : M ≠ ∞)
    (hmap : ν.map u = M • volume.restrict (Icc (0 : ℝ) 1)) :
    ∃ C : ℝ, 0 < C ∧ ∀ x r, 0 < r → (ν (closedBall x (A * r))).toReal ≤ C * r ^ c := by
  let L := A + 1
  have hL : 0 < L := by dsimp only [L]; linarith only [hA]
  let C := M.toReal * (2 * H) * L ^ c + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, fun x r hr ↦ ?_⟩
  have hs : 0 < L * r := mul_pos hL hr
  have hball : closedBall x (A * r) ⊆ ball x (L * r) := closedBall_subset_ball (by
    dsimp only [L]
    nlinarith only [hr])
  calc
    _ ≤ (ν (ball x (L * r))).toReal := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hball)
    _ ≤ (M * ENNReal.ofReal (2 * H * (L * r) ^ c)).toReal :=
      ENNReal.toReal_mono (ENNReal.mul_ne_top hM ENNReal.ofReal_ne_top)
        (measure_ball_le_of_holder_and_map_eq_smul_volume hc hH.le hu hHolder hmap x (L * r))
    _ ≤ _ := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), Real.mul_rpow hL.le hr.le]
      rw [← mul_assoc, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (Real.rpow_nonneg hr.le _)

namespace PEnergy.CompactCore

variable [LocallyCompactSpace X] {m : Measure X} [IsFiniteMeasureOnCompacts m]
  {p : ℝ} {E : PEnergy m p}

theorem energyDerivativeMeasure_variation_le_global_root (u v : E.CompactCore)
    {S : Set X} (hS : MeasurableSet S) :
    ((E.energyDerivativeMeasure u.domainElement v.domainElement).totalVariation S).toReal ≤
      2 * (E.energyMeasure u.domainElement S).toReal ^ ((p - 1) / p) *
        E.rootSeminorm v.domainElement := by
  have h := (E.energyDerivativeMeasure_variation_le u.domainElement v.domainElement hS).trans
    (mul_le_mul_of_nonneg_left (E.energyMeasureRoot_le S hS v.domainElement)
      (mul_nonneg (by norm_num) (Real.rpow_nonneg (apply_nonneg _ _) _)))
  change _ ≤ 2 * (E.energyMeasureLaws.root S hS u.domainElement) ^ (p - 1) * _ at h
  rw [E.energyMeasureLaws.root_apply S hS u.domainElement, measureReal_def,
    ← Real.rpow_mul ENNReal.toReal_nonneg, mul_comm p⁻¹, ← div_eq_mul_inv] at h
  exact h

theorem le_weighted_self_of_cutoff (u χ : E.CompactCore) {B S : Set X}
    (hB : MeasurableSet B) (hS : MeasurableSet S) (hSB : S ⊆ B)
    (hχ : ∀ x, 0 ≤ χ.toFun x) (hχS : EqOn χ.toFun (fun _ ↦ 1) S) :
    (E.energyMeasure u.domainElement S).toReal ≤ weightSignedMeasure
      (E.energyDerivativeMeasure u.domainElement u.domainElement) χ.toFun B := by
  let ν := E.energyMeasure u.domainElement
  have hSelf : E.energyDerivativeMeasure u.domainElement u.domainElement = ν.toSignedMeasure := by
    ext A hA
    rw [E.energyDerivativeMeasure_self _ hA, Measure.toSignedMeasure_apply_measurable hA]
    rfl
  rw [hSelf, weightSignedMeasure_of_toSignedMeasure_apply _ (χ.integrable_vectorMeasure _) hB]
  let f : X → ℝ := S.indicator (fun _ ↦ 1)
  have hI : Integrable χ.toFun ν := by
    obtain ⟨K, hK⟩ := χ.continuous.bounded_above_of_compact_support χ.compactSupport
    exact Integrable.of_bound χ.continuous.aestronglyMeasurable K (Eventually.of_forall hK)
  have hF : Integrable f ν := (integrable_const _).indicator hS
  have hpt (x : X) : f x ≤ χ.toFun x := by
    by_cases hx : x ∈ S
    · rw [show f x = 1 from indicator_of_mem hx _, hχS hx]
    · rw [show f x = 0 from indicator_of_notMem hx _]
      exact hχ x
  have h := integral_mono hF.integrableOn hI.integrableOn hpt (μ := ν.restrict B)
  change (∫ x, S.indicator (1 : X → ℝ) x ∂ν.restrict B) ≤ _ at h
  rw [integral_indicator_one hS, measureReal_def, Measure.restrict_apply hS, inter_eq_left.mpr hSB] at h
  exact h

end PEnergy.CompactCore

end WalkDimensions
