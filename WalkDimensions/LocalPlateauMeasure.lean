import WalkDimensions.LocalBesovDomain

/-!
# Vanishing energy measure on an almost-everywhere constant open set
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SecondCountableTopology X] {m : Measure X}
  [m.Regular] [m.IsOpenPosMeasure] [SFinite m] {p : ℝ} (E : PEnergy m p)

theorem energyMeasure_eq_zero_of_ae_const_on_open {β : ℝ} (hβ : 0 < β)
    (hvol : VolumeDoubling m) (hPI : E.Poincare E.energyMeasure β)
    (hcap : E.CapacityUpperBound β) {f : E.domain} {U : Set X}
    (hU : IsOpen U) {c : ℝ} (hf : (f : RealLp m p) =ᵐ[m.restrict U] (fun _ ↦ c)) :
    E.energyMeasure f U = 0 := by
  obtain ⟨C, _, _, hRev⟩ := E.exists_local_besov_reverse hβ hvol hPI hcap
  rw [hU.measure_eq_iSup_isCompact]
  apply ENNReal.iSup_eq_zero.mpr
  intro K
  apply ENNReal.iSup_eq_zero.mpr
  intro hKU
  apply ENNReal.iSup_eq_zero.mpr
  intro hK
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_thickening_subset_open hU hKU
  let V := thickening (δ / 2) K
  have hKV : K ⊆ V := self_subset_thickening (by positivity) _
  have hVU : V ⊆ U := (thickening_mono (by linarith) _).trans hδU
  have hAE : ∀ᶠ r in 𝓝[>] (0 : ℝ), besovEnergy m p β V (f : RealLp m p) r = 0 := by
    filter_upwards [Ioo_mem_nhdsGT (show 0 < δ / 2 by positivity)] with r hr
    unfold besovEnergy
    suffices (∫⁻ x in V, ballMoment m p (f : RealLp m p) r x ∂m) = 0 by rw [this, mul_zero]
    let u : RealLp m p := f
    apply (lintegral_congr_ae (g := fun _ ↦ 0) ?_).trans lintegral_zero
    filter_upwards [ae_mono (Measure.restrict_mono hVU le_rfl) hf,
      ae_restrict_mem (μ := m) (s := V) isOpen_thickening.measurableSet] with x hx hxV
    obtain ⟨z, hzK, hxz⟩ := mem_thickening_iff.mp hxV
    have hBall : ball x r ⊆ U := by
      intro y hy
      apply hδU
      exact mem_thickening_iff.mpr ⟨z, hzK, (dist_triangle y x z).trans_lt (by
        have h := mem_ball.mp hy
        linarith only [h, hxz, hr.2])⟩
    have hfy : u =ᵐ[normalizedBall m x r] (fun _ ↦ c) := by
      apply (Measure.smul_absolutelyContinuous (c := (m (ball x r))⁻¹)).ae_le
      exact ae_mono (Measure.restrict_mono hBall le_rfl) hf
    unfold ballMoment
    apply (lintegral_congr_ae (g := fun _ ↦ 0) ?_).trans lintegral_zero
    filter_upwards [hfy] with y hy
    change u x = c at hx
    change u y = c at hy
    rw [hx, hy, sub_self, abs_zero, ENNReal.ofReal_zero,
      ENNReal.zero_rpow_of_pos (zero_lt_one.trans E.one_lt)]
  have hLi : liminf (besovEnergy m p β V (f : RealLp m p)) (𝓝[>] 0) = 0 := by
    rw [liminf_congr hAE, liminf_const]
  exact measure_mono_null hKV (le_antisymm
    ((hRev f V isOpen_thickening).trans (by rw [hLi, mul_zero])) bot_le)

end WalkDimensions.PEnergy
