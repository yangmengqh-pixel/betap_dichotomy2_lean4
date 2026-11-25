import WalkDimensions.OscillationLimit

/-!
# Changing the threshold of a localized oscillation

At a fixed oscillation width a shift of the threshold has small graph norm.
Its difference is a nonnegative available height cut off by a thin ramp.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal Topology

namespace WalkDimensions

private theorem oscillation_shift_diff {s r U : ℝ} (hr : 0 ≤ r)
    (hU₀ : 0 ≤ U) (hU : U ≤ s) (a v : ℝ) :
    min U (sublevelRamp s (a + r) v) - min U (sublevelRamp s a v) =
      min (max (U - max (a + s - v) 0) 0) (sublevelRamp r (a + s) v) := by
  let q := a + s - v
  unfold sublevelRamp
  rw [show a + r + s - v = q + r by dsimp [q]; ring,
    show a + s + r - v = q + r by dsimp [q]; ring]
  change min U (max (min (q + r) s) 0) - min U (max (min q s) 0) =
    min (max (U - max q 0) 0) (max (min (q + r) r) 0)
  have hclip (t : ℝ) : min U (max (min t s) 0) = min U (max t 0) := by
    rcases le_total t s with h | h
    · rw [min_eq_left h]
    · rw [min_eq_right h, max_eq_left (hU₀.trans hU), min_eq_left hU,
        min_eq_left (hU.trans (h.trans (le_max_left _ _)))]
  simp only [hclip]
  rcases le_total q 0 with hq | hq
  · have hqr : q + r ≤ r := by linarith only [hq]
    rw [max_eq_right hq, sub_zero, max_eq_left hU₀, min_eq_left hqr, min_eq_right hU₀, sub_zero]
  · rw [max_eq_left hq, max_eq_left (add_nonneg hq hr),
      min_eq_right (by linarith only [hq] : r ≤ q + r), max_eq_left hr]
    rcases le_total U q with h | h
    · rw [min_eq_left h, min_eq_left (h.trans (le_add_of_nonneg_right hr)), sub_self,
        max_eq_right (sub_nonpos.mpr h), min_eq_left hr]
    · rw [min_eq_right h, max_eq_left (sub_nonneg.mpr h)]
      rcases le_total U (q + r) with h' | h'
      · rw [min_eq_left h', min_eq_left (by linarith only [h'])]
      · rw [min_eq_right h', min_eq_right (by linarith only [h'])]
        ring

private theorem oscillation_shift_midpoint {a r s t D v : ℝ} (hr : 0 ≤ r)
    (hrs : r ≤ s) (hrt : r ≤ t) :
    min D (sublevelRamp r a v) =
      min (min ((min D (sublevelRamp s a v) + min D (sublevelRamp t a v)) / 2) r)
        (sublevelRamp r a v) := by
  have hmono {b c : ℝ} (hbc : b ≤ c) : sublevelRamp b a v ≤ sublevelRamp c a v := by
    unfold sublevelRamp
    exact max_le_max (min_le_min (by linarith only [hbc]) hbc) le_rfl
  have hcap : sublevelRamp r a v ≤ r := max_le (min_le_right _ _) hr
  have hlo₁ := min_le_min (le_refl D) (hmono hrs)
  have hlo₂ := min_le_min (le_refl D) (hmono hrt)
  apply le_antisymm
  · apply le_min (le_min (by linarith only [hlo₁, hlo₂]) ((min_le_right _ _).trans hcap))
    exact min_le_right _ _
  · have hi₁ : min D (sublevelRamp s a v) ≤ D := min_le_left _ _
    have hi₂ : min D (sublevelRamp t a v) ≤ D := min_le_left _ _
    exact le_min ((min_le_left _ _).trans ((min_le_left _ _).trans (by linarith only [hi₁, hi₂])))
      (min_le_right _ _)

namespace PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {p : ℝ} (E : PEnergy μ p)

theorem tendsto_graph_localized_oscillation_shift (g w : E.domain) {u v : X → ℝ}
    (hgv : (g : RealLp μ p) =ᵐ[μ] v) (hcv : HasCompactSupport v) (hcu : HasCompactSupport u)
    {s : ℝ} (hs : 0 < s) (a : ℝ) (w' : ℕ → E.domain)
    (hw : (w : RealLp μ p) =ᵐ[μ] fun x ↦ min (sawtooth s (u x)) (sublevelRamp s a (v x)))
    (hw' : ∀ n, (w' n : RealLp μ p) =ᵐ[μ] fun x ↦
      min (sawtooth s (u x)) (sublevelRamp s (a + oscillationWidth n) (v x))) :
    Tendsto (fun n ↦ E.graphSeminorm (w' n - w)) atTop (𝓝 0) := by
  let _ : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt.le⟩
  let ε := oscillationWidth
  let z (n : ℕ) := w' n - w
  let D (x : X) := max (sawtooth s (u x) - max (a + s - v x) 0) 0
  let Z (n : ℕ) (x : X) := min (D x) (sublevelRamp (ε n) (a + s) (v x))
  have hz (n : ℕ) : (z n : RealLp μ p) =ᵐ[μ] Z n := by
    filter_upwards [Lp.coeFn_sub (w' n : RealLp μ p) (w : RealLp μ p), hw, hw' n] with x hx hy hu
    change ((w' n : RealLp μ p) - (w : RealLp μ p)) x = _
    rw [hx, Pi.sub_apply, hu, hy]
    exact oscillation_shift_diff (oscillationWidth_pos n).le (sawtooth_nonneg _ _)
      (sawtooth_le hs _) a _
  have hZ₀ (n : ℕ) (x : X) : 0 ≤ Z n x := le_min (le_max_right _ _) (sublevelRamp_nonneg _ _ _)
  have hZ (n : ℕ) (x : X) : |Z n x| ≤ (tsupport u).indicator (fun _ ↦ ε n) x := by
    rw [abs_of_nonneg (hZ₀ n x)]
    by_cases hx : x ∈ tsupport u
    · rw [indicator_of_mem hx]
      exact (min_le_right _ _).trans (max_le (min_le_right _ _) (oscillationWidth_pos n).le)
    · rw [indicator_of_notMem hx]
      have hu : u x = 0 := notMem_support.mp fun hx' ↦ hx (subset_closure hx')
      apply (min_le_left _ _).trans
      dsimp [D]
      rw [hu, sawtooth_zero, zero_sub, max_eq_right (neg_nonpos.mpr (le_max_right _ _))]
  let B := (μ.real (tsupport u)) ^ p⁻¹
  have hnorm (n : ℕ) : ‖(z n : RealLp μ p)‖ ≤ ε n * B := by
    apply norm_realLp_le_of_ae_abs_bound (zero_lt_one.trans E.one_lt) _ isClosed_closure.measurableSet
      (hcu.isCompact.measure_lt_top (μ := μ)).ne (oscillationWidth_pos n).le
    filter_upwards [hz n] with x hx
    rw [hx]
    exact hZ n x
  have hLp : Tendsto (fun n ↦ ‖(z n : RealLp μ p)‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ ↦ norm_nonneg _) hnorm
      (by simpa only [zero_mul] using tendsto_oscillationWidth.mul_const B)
  obtain ⟨ramps, hramps, hramps_lim⟩ := E.exists_ramp_graph_tendsto_zero g hgv hcv (a + s) ε
    (fun n ↦ (oscillationWidth_pos n).le) oscillationWidth_antitone tendsto_oscillationWidth
  have hR : Tendsto (fun n ↦ E.rootSeminorm (ramps n)) atTop (𝓝 0) :=
    squeeze_zero (fun _ ↦ apply_nonneg _ _) (fun n ↦ E.rootSeminorm_le_graphSeminorm (ramps n))
      hramps_lim
  have hE := E.tendsto_root_zero_of_midpoint_error z hLp _ hR (by
    intro i j n hi hj
    let F := (z i : RealLp μ p)
    let G := (z j : RealLp μ p)
    let k := (1 / 2 : ℝ) • (z i + z j)
    have hk : (k : RealLp μ p) =ᵐ[μ] (fun x ↦ (Z i x + Z j x) / 2) := by
      filter_upwards [Lp.coeFn_smul (1 / 2 : ℝ) (F + G), Lp.coeFn_add F G, hz i, hz j]
        with x hx hsum hfx hgx
      change ((1 / 2 : ℝ) • (F + G)) x = _
      rw [hx, Pi.smul_apply, smul_eq_mul, hsum, Pi.add_apply, hfx, hgx]
      ring
    obtain ⟨b, hb, hbE⟩ := E.exists_lipschitz_one_comp k hk (fun t ↦ min t (ε n))
      (LipschitzWith.id.min_const _) (min_eq_left (oscillationWidth_pos n).le)
    obtain ⟨c, hc, hcE⟩ := E.exists_min_add_const b (ramps n) hb (hramps n)
      (sublevelRamp_nonneg _ _ _)
    have he : c = z n := by
      apply Subtype.ext
      apply Lp.ext
      filter_upwards [hc, hz n] with x hx hy
      rw [hx, hy]
      change min (min ((Z i x + Z j x) / 2) (ε n))
        (offsetRamp (ε n) (a + s) (v x) + sublevelRamp (ε n) (a + s) 0) = Z n x
      simpa only [offsetRamp, sub_add_cancel, Z] using
        (oscillation_shift_midpoint (oscillationWidth_pos n).le (oscillationWidth_antitone hi)
          (oscillationWidth_antitone hj)).symm
    have hbroot : E.rootSeminorm b ≤ E.rootSeminorm k := by
      rw [E.rootSeminorm_apply, E.rootSeminorm_apply]
      exact Real.rpow_le_rpow (NNReal.coe_nonneg _) (NNReal.coe_le_coe.mpr hbE)
        (inv_nonneg.mpr (zero_lt_one.trans E.one_lt).le)
    exact (he ▸ hcE).trans (add_le_add_left hbroot _))
  exact squeeze_zero (fun _ ↦ apply_nonneg _ _) (fun n ↦ E.graphSeminorm_le_add (z n))
    (by simpa only [zero_add] using hE.add hLp)

end PEnergy
end WalkDimensions
