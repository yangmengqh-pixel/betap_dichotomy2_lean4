import WalkDimensions.BesovExponentAntitone
import WalkDimensions.BesovHolder

/-!
# Compactly supported tests in a supercritical Besov space

Uniform continuity and the lower volume bound force every positive
absolute-value level set of an integrable function to be compact.
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal Topology

namespace WalkDimensions

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  [SecondCountableTopology X] [Nonempty X] {m : Measure X} [IsFiniteMeasureOnCompacts m]
  [SFinite m] [m.IsOpenPosMeasure]

omit [SecondCountableTopology X] [IsFiniteMeasureOnCompacts m] [SFinite m] [m.IsOpenPosMeasure] in
theorem isCompact_abs_superlevel_of_memLp_of_uniformContinuous {d p : ℝ}
    (hvol : AhlforsRegular m d) (hp : 0 < p) {v : X → ℝ}
    (hv : UniformContinuous v) (hvLp : MemLp v (ENNReal.ofReal p) m) {ε : ℝ} (hε : 0 < ε) :
    IsCompact {x | ε ≤ |v x|} := by
  obtain ⟨_, V, hV, hVol⟩ := hvol
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  obtain ⟨r, hr, hnear⟩ := Metric.uniformContinuous_iff.mp hv (ε / 2) (half_pos hε)
  let S := {x | ε / 2 ≤ |v x|}
  let A := {x | ε ≤ |v x|}
  have hS : MeasurableSet S :=
    (isClosed_le continuous_const (continuous_abs.comp hv.continuous)).measurableSet
  have hA : IsClosed A := isClosed_le continuous_const (continuous_abs.comp hv.continuous)
  let F (x : X) := ENNReal.ofReal |v x| ^ p
  let B := (ENNReal.ofReal (ε / 2)) ^ p
  have hB : B ≠ 0 := (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr (half_pos hε)) ENNReal.ofReal_ne_top).ne'
  have hF : Measurable F := ((continuous_abs.measurable.comp hv.continuous.measurable).ennreal_ofReal).pow_const _
  have hFfin : (∫⁻ x, F x ∂m) < ∞ := by
    simpa only [F, ENNReal.toReal_ofReal hp.le, Real.eNorm_eq_ofReal_abs] using
      lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top (ENNReal.ofReal_ne_zero_iff.mpr hp)
        ENNReal.ofReal_ne_top hvLp.eLpNorm_lt_top
  have hSfin : m S ≠ ∞ := by
    intro h
    have hle : B * m S ≤ ∫⁻ x, F x ∂m := by
      refine (mul_le_mul_of_nonneg_left (measure_mono ?_) bot_le).trans (mul_meas_ge_le_lintegral hF (μ := m) B)
      intro x hx
      exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hx) hp.le
    exact hFfin.not_ge (by simpa [h, hB] using hle)
  let T (n : ℕ) := S \ ball x₀ (n : ℝ)
  have hT : Antitone T := fun i j h ↦ sdiff_subset_sdiff_right (ball_subset_ball (Nat.cast_le.mpr h))
  have hEmpty : (⋂ n, T n) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro y hy
    obtain ⟨n, hn⟩ := exists_nat_gt (dist y x₀)
    exact ((mem_iInter.mp hy n).2) (mem_ball.mpr hn)
  have hTlim := tendsto_measure_iInter_atTop (μ := m) (s := T)
    (fun n ↦ (hS.diff (measurableSet_ball : MeasurableSet (ball x₀ (n : ℝ)))).nullMeasurableSet)
    hT ⟨0, measure_ne_top_of_subset (sdiff_subset : T 0 ⊆ S) hSfin⟩
  rw [hEmpty, measure_empty] at hTlim
  have hL : 0 < ENNReal.ofReal (r ^ d / V) := ENNReal.ofReal_pos.mpr (div_pos (Real.rpow_pos_of_pos hr _) hV)
  obtain ⟨n, hn⟩ := (hTlim.eventually_lt_const hL).exists
  have hAb : A ⊆ closedBall x₀ (n + r) := by
    intro x hx
    apply mem_closedBall.mpr
    by_contra! hfar
    have hball : ball x r ⊆ T n := by
      intro y hy
      have hyd := mem_ball.mp hy
      have hclose : |v x - v y| < ε / 2 := by
        rw [← Real.dist_eq]
        exact hnear (by simpa only [dist_comm x y] using hyd)
      have hyt : ε / 2 ≤ |v y| := by
        have ht := abs_sub_abs_le_abs_sub (v x) (v y)
        linarith only [show ε ≤ |v x| from hx, ht, hclose]
      refine ⟨hyt, fun hyB ↦ ?_⟩
      exact hfar.not_ge ((dist_triangle x y x₀).trans (by
        rw [dist_comm x y]
        linarith only [hyd, mem_ball.mp hyB]))
    exact hn.not_ge ((hVol x r hr).1.trans (measure_mono hball))
  exact (isCompact_closedBall _ _).of_isClosed_subset hA hAb

omit [SFinite m] in
theorem exists_compact_besov_test_of_supercritical {d p α : ℝ} (hp : 1 ≤ p)
    (hvol : AhlforsRegular m d) (hα : d < p * α)
    {u : X → ℝ} (hu : InBesov m p α u) (hnc : ¬ ∃ c : ℝ, u =ᵐ[m] fun _ ↦ c) :
    ∃ v : X → ℝ, Continuous v ∧ HasCompactSupport v ∧ InBesov m p α v ∧
      ¬ ∃ c : ℝ, v =ᵐ[m] fun _ ↦ c := by
  let M := ⨆ r : Ioi (0 : ℝ), besovEnergy m p (p * α) univ u r
  obtain ⟨H, hH, v, hv, huv, hvHolder⟩ :=
    exists_holder_representative_of_besov_bound hp hvol hα hu.1 (M := M) hu.2.ne
      (fun r hr ↦ le_iSup_of_le ⟨r, hr⟩ le_rfl)
  have hp' := zero_lt_one.trans_le hp
  have hve : 0 < (p * α - d) / p := div_pos (sub_pos.mpr hα) hp'
  have hvUC : UniformContinuous v := by
    apply Metric.uniformContinuous_iff.mpr
    intro ε hε
    have hcont := (Real.continuous_rpow_const hve.le).const_mul H
    obtain ⟨r, hr, hbound⟩ := Metric.continuousAt_iff.mp (hcont.continuousAt (x := 0)) ε hε
    refine ⟨r, hr, fun x y hxy ↦ ?_⟩
    have he := hbound (x := dist x y) (by simpa only [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg] using hxy)
    change dist (H * dist x y ^ ((p * α - d) / p)) (H * (0 : ℝ) ^ ((p * α - d) / p)) < ε at he
    rw [Real.dist_eq, Real.zero_rpow hve.ne', mul_zero, sub_zero, abs_of_nonneg (by positivity)] at he
    rw [Real.dist_eq]
    exact (hvHolder x y).trans_lt he
  have hvB : InBesov m p α v := ⟨hu.1.ae_eq huv, by simpa only [← besovEnergy_congr_ae huv] using hu.2⟩
  have hvnc : ¬ ∃ c : ℝ, v =ᵐ[m] fun _ ↦ c := by
    rintro ⟨c, hc⟩
    exact hnc ⟨c, huv.trans hc⟩
  obtain ⟨δ, hδ, hw⟩ := exists_softThreshold_nonconstant hvnc
  let w := softThreshold δ ∘ v
  have hwCon : Continuous w := (lipschitzWith_softThreshold δ).continuous.comp hv
  have hS := isCompact_abs_superlevel_of_memLp_of_uniformContinuous hvol hp' hvUC hvB.1 hδ
  have hwC : HasCompactSupport w :=
    HasCompactSupport.intro hS (fun x hx ↦ softThreshold_zero_of_abs_lt (lt_of_not_ge hx))
  refine ⟨w, hwCon, hwC, ⟨hwCon.memLp_of_hasCompactSupport hwC, ?_⟩, hw⟩
  apply lt_of_le_of_lt _ hvB.2
  apply iSup_mono
  intro r
  simpa only [ENNReal.coe_one, ENNReal.one_rpow, one_mul] using
    besovEnergy_lipschitz_comp_le hp'.le (lipschitzWith_softThreshold δ) v r

end WalkDimensions
