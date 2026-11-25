import WalkDimensions.PointwiseSlope
import WalkDimensions.LocalBesovDomain
import WalkDimensions.CriticalBesov

/-!
# First-order energy control by the local Lipschitz slope
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal NNReal Topology

namespace WalkDimensions

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SecondCountableTopology X] {m : Measure X}
  [IsFiniteMeasureOnCompacts m] [m.IsOpenPosMeasure]

theorem besovEnergy_firstOrder_le_slope {p : ℝ} (hp : 0 < p)
    {u : X → ℝ} (hu : Continuous u) (U : Set X) {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) :
    besovEnergy m p p U u r ≤ ∫⁻ x in U, (ballSlope u s x) ^ p ∂m := by
  let P := (ENNReal.ofReal r) ^ p
  have hP : 0 < P := ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hr) ENNReal.ofReal_ne_top
  have hPT : P ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.ofReal_ne_top
  have hbound (x : X) : ballMoment m p u r x ≤ (ballSlope u s x) ^ p * P := by
    unfold ballMoment
    calc
      _ ≤ ∫⁻ _ : X, (ballSlope u s x) ^ p * P ∂normalizedBall m x r := by
        apply lintegral_mono_ae
        have hpos : (normalizedBall m x r) (ball x r)ᶜ = 0 := by
          rw [normalizedBall, smul_apply, Measure.restrict_apply measurableSet_ball.compl,
            compl_inter_self, measure_empty, smul_zero]
        filter_upwards [ae_iff.mpr hpos] with y hy
        have hy' : y ∈ ball x r := hy
        have hd : dist x y ≤ r := by rw [dist_comm]; exact (mem_ball.mp hy').le
        have h := (ofReal_abs_sub_le_ballSlope_mul_dist (u := u) (ball_subset_ball hrs hy')).trans
          (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hd) bot_le)
        exact (ENNReal.rpow_le_rpow h hp.le).trans_eq (ENNReal.mul_rpow_of_nonneg _ _ hp.le)
      _ = _ := by rw [lintegral_const, normalizedBall_univ x hr, mul_one]
  unfold besovEnergy
  rw [ENNReal.rpow_neg]
  refine (mul_le_mul_of_nonneg_left (lintegral_mono hbound) bot_le).trans_eq ?_
  rw [lintegral_mul_const _ ((measurable_ballSlope hu s).pow_const p)]
  calc
    _ = (P⁻¹ * P) * ∫⁻ x in U, (ballSlope u s x) ^ p ∂m := by ac_rfl
    _ = _ := by rw [ENNReal.inv_mul_cancel hP.ne' hPT, one_mul]

theorem liminf_besovEnergy_firstOrder_le_pointwiseSlope {p : ℝ} (hp : 0 < p)
    {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) {U : Set X} (hU : m U ≠ ∞) :
    liminf (besovEnergy m p p U u) (𝓝[>] (0 : ℝ)) ≤
      ∫⁻ x in U, pointwiseSlope u x ^ p ∂m := by
  let s (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  let f (n : ℕ) (x : X) := (ballSlope u (s n) x) ^ p
  have hAnti : Antitone f := by
    intro i j hij x
    apply ENNReal.rpow_le_rpow _ hp.le
    apply ballSlope_mono u x
    exact one_div_le_one_div_of_le (by positivity)
      (add_le_add_left (Nat.cast_le.mpr hij) 1)
  have hLim (n : ℕ) : liminf (besovEnergy m p p U u) (𝓝[>] (0 : ℝ)) ≤
      ∫⁻ x in U, f n x ∂m := by
    have hI : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioo 0 (s n) :=
      Ioo_mem_nhdsGT (by dsimp only [s]; positivity)
    exact liminf_le_of_frequently_le
      (hI.mono (fun r hr ↦ besovEnergy_firstOrder_le_slope hp hu.continuous U hr.1 hr.2.le)).frequently
      (by isBoundedDefault)
  have hFin : (∫⁻ x in U, f 0 x ∂m) ≠ ∞ := by
    apply ne_top_of_le_ne_top (b := (K : ℝ≥0∞) ^ p * m U)
      (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.coe_ne_top) hU)
    rw [← setLIntegral_const]
    exact lintegral_mono fun x ↦ ENNReal.rpow_le_rpow (ballSlope_le_of_lipschitzWith hu _ _) hp.le
  have he : (fun x ↦ pointwiseSlope u x ^ p) = (fun x ↦ ⨅ n, f n x) := by
    funext x
    change (⨅ n, ballSlope u (s n) x) ^ p = ⨅ n, (ballSlope u (s n) x) ^ p
    exact ENNReal.iInf_rpow_of_pos hp _
  rw [he]
  rw [lintegral_iInf (fun n ↦ (measurable_ballSlope hu.continuous (s n)).pow_const _) hAnti hFin]
  exact le_iInf hLim

namespace PEnergy

variable [m.Regular] [SFinite m] {p : ℝ} (E : PEnergy m p)

theorem exists_energy_of_compact_lipschitz_at_firstOrder
    (hvol : VolumeDoubling m) (hPI : E.Poincare E.energyMeasure p)
    (hcap : E.CapacityUpperBound p) :
    ∃ C : ℝ≥0∞, 0 < C ∧ C ≠ ∞ ∧
      ∀ (u : X → ℝ) {K : ℝ≥0}, LipschitzWith K u → HasCompactSupport u →
      ∃ f : E.domain, (f : RealLp m p) =ᵐ[m] u ∧ ∀ U : Set X, IsOpen U → m U ≠ ∞ →
        E.energyMeasure f U ≤ C * ∫⁻ x in U, pointwiseSlope u x ^ p ∂m := by
  have hp := zero_lt_one.trans E.one_lt
  obtain ⟨C, hC, hCT, hLocal⟩ := E.exists_local_besov_reverse hp hvol hPI hcap
  obtain ⟨_, _, hRecover⟩ := E.exists_energy_of_besov_liminf hp hvol hcap
  refine ⟨C, hC, hCT, fun u K hu hc ↦ ?_⟩
  have hB := inBesov_one_of_lipschitz hp hvol hu hc
  have hQ : liminf (besovEnergy m p p univ u) (𝓝[>] (0 : ℝ)) < ∞ := by
    apply (liminf_le_of_frequently_le ?_ (by isBoundedDefault)).trans_lt hB.2
    have hp' : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r := eventually_mem_nhdsWithin
    apply (hp'.mono ?_).frequently
    intro r hr
    simpa only [mul_one] using
      le_iSup (fun r : Ioi (0 : ℝ) ↦ besovEnergy m p (p * 1) univ u r) ⟨r, hr⟩
  obtain ⟨f, hf, _⟩ := hRecover hB.1 hQ
  refine ⟨f, hf, fun U hU hUfin ↦ (hLocal f U hU).trans ?_⟩
  rw [funext (besovEnergy_congr_ae hf p p U)]
  exact mul_le_mul_of_nonneg_left (liminf_besovEnergy_firstOrder_le_pointwiseSlope hp hu hUfin) bot_le

end PEnergy

end WalkDimensions
