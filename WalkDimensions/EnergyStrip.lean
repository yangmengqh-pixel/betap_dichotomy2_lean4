import WalkDimensions.CompactCore
import WalkDimensions.SublevelDistribution

/-!
# Energy of a strip between two level sets

Disjointness of the lower oscillation and the strip makes their energies
add. Cutting the upper oscillation by two ramps bounds this sum.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal Topology

namespace WalkDimensions

private theorem min_sublevelRamp_eq_band {r : ℝ} (b c t : ℝ) :
    min (sublevelRamp r c t) (sublevelRamp r (-b) (-t)) =
      sublevelRamp r ((c - b) / 2) |t - (b + c) / 2| := by
  have h : min (c + r - t) (-b + r - -t) =
      (c - b) / 2 + r - |t - (b + c) / 2| := by
    rcases le_total t ((b + c) / 2) with ht | ht
    · rw [abs_of_nonpos (sub_nonpos.mpr ht), min_eq_right (by linarith only [ht])]
      ring
    · rw [abs_of_nonneg (sub_nonneg.mpr ht), min_eq_left (by linarith only [ht])]
      ring
  unfold sublevelRamp
  rw [← max_min_distrib_right]
  have he : min (min (c + r - t) r) (min (-b + r - -t) r) =
      min (min (c + r - t) (-b + r - -t)) (min r r) := by ac_rfl
  rw [he, min_self, h]

namespace PEnergy.CompactCore

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {p : ℝ} {E : PEnergy μ p}

noncomputable def oscillationCore (f g : E.CompactCore) (a : ℝ) (n : ℕ) : E.CompactCore where
  domainElement := f.oscillation g a n
  toFun x := min (sawtooth (oscillationWidth n) (f.toFun x))
    (sublevelRamp (oscillationWidth n) a (g.toFun x))
  ae_eq := f.oscillation_ae g a n
  continuous := ((lipschitzWith_sawtooth _).continuous.comp f.continuous).min
    ((lipschitzWith_sublevelRamp _ _).continuous.comp g.continuous)
  compactSupport := by
    apply f.compactSupport.isCompact.of_isClosed_subset isClosed_closure
    apply closure_mono
    intro x hx
    by_contra h
    have hzero := notMem_support.mp h
    apply hx
    change min (sawtooth (oscillationWidth n) (f.toFun x))
      (sublevelRamp (oscillationWidth n) a (g.toFun x)) = 0
    rw [hzero, sawtooth_zero, min_eq_left (sublevelRamp_nonneg _ _ _)]

noncomputable def bandTest (g : E.CompactCore) (b c : ℝ) : E.CompactCore :=
  g.mapLipschitz (fun t ↦ |t - (b + c) / 2| - |0 - (b + c) / 2|)
    (by
      apply lipschitzWith_iff_dist_le_mul.mpr
      intro s t
      simpa only [Real.dist_eq, NNReal.coe_one, one_mul, sub_sub_sub_cancel_right] using
        abs_abs_sub_abs_le_abs_sub (s - (b + c) / 2) (t - (b + c) / 2))
    (sub_self _)

noncomputable def bandThreshold (b c : ℝ) : ℝ := (c - b) / 2 - |0 - (b + c) / 2|

theorem band_ramp_eq (g : E.CompactCore) (b c r : ℝ) (x : X) :
    sublevelRamp r (bandThreshold b c) ((g.bandTest b c).toFun x) =
      min (sublevelRamp r c (g.toFun x)) (sublevelRamp r (-b) (-g.toFun x)) := by
  rw [min_sublevelRamp_eq_band]
  unfold sublevelRamp
  have he : bandThreshold b c + r - (g.bandTest b c).toFun x =
      (c - b) / 2 + r - |g.toFun x - (b + c) / 2| := by
    change (c - b) / 2 - |0 - (b + c) / 2| + r -
      (|g.toFun x - (b + c) / 2| - |0 - (b + c) / 2|) =
      (c - b) / 2 + r - |g.toFun x - (b + c) / 2|
    ring
  rw [he]

private theorem add_oscillation_eq_min {r a b c U v : ℝ} (hr : 0 < r) (hU₀ : 0 ≤ U)
    (hU : U ≤ r) (hab : a + 2 * r < b) (hbc : b < c) :
    min U (sublevelRamp r a v) +
        min U (min (sublevelRamp r c v) (sublevelRamp r (-b) (-v))) =
      min (min U (sublevelRamp r c v)) (sublevelRamp r a v + sublevelRamp r (-b) (-v)) := by
  by_cases hv : a + r ≤ v
  · rw [sublevelRamp_eq_zero hv, min_eq_right hU₀, zero_add, zero_add, min_assoc]
  · have hb : -b + r ≤ -v := by linarith only [lt_of_not_ge hv, hab]
    have hc : v ≤ c := by linarith only [lt_of_not_ge hv, hab, hbc, hr]
    rw [sublevelRamp_eq_zero hb, min_eq_right (sublevelRamp_nonneg r c v), min_eq_right hU₀,
      add_zero, add_zero, sublevelRamp_eq_cap hr.le hc, min_eq_left hU]

theorem band_energy_le (f g : E.CompactCore) {a b c : ℝ} (hab : a < b) (hbc : b < c) :
    f.sublevelDistribution (g.bandTest b c) (bandThreshold b c) ≤
      f.sublevelDistribution g c - f.sublevelDistribution g a := by
  let τ := bandThreshold b c
  let A (n : ℕ) := f.oscillationCore g a n
  let B (n : ℕ) := f.oscillationCore (g.bandTest b c) τ n
  let C (n : ℕ) := f.oscillationCore g c n
  let s (n : ℕ) := oscillationWidth n
  obtain ⟨u, hu, hU⟩ := E.exists_ramp_graph_tendsto_zero g.domainElement g.ae_eq g.compactSupport
    a s (fun n ↦ (oscillationWidth_pos n).le) oscillationWidth_antitone tendsto_oscillationWidth
  obtain ⟨v, hv, hV⟩ := E.exists_ramp_graph_tendsto_zero g.neg.domainElement g.neg.ae_eq
    g.neg.compactSupport (-b) s (fun n ↦ (oscillationWidth_pos n).le)
    oscillationWidth_antitone tendsto_oscillationWidth
  have hsum (n : ℕ) : ((u n + v n : E.domain) : RealLp μ p) =ᵐ[μ]
      fun x ↦ offsetRamp (s n) a (g.toFun x) + offsetRamp (s n) (-b) (-g.toFun x) := by
    filter_upwards [Lp.coeFn_add (u n : RealLp μ p) (v n : RealLp μ p), hu n, hv n] with x hx hy hz
    change ((u n : RealLp μ p) + (v n : RealLp μ p)) x = _
    rw [hx, Pi.add_apply, hy, hz]
    rfl
  let e (n : ℕ) := E.graphSeminorm (u n) + E.graphSeminorm (v n)
  have he : Tendsto e atTop (𝓝 0) := by
    simpa only [zero_add] using hU.add hV
  have hend := (f.tendsto_sublevelEnergyRoot g c).add he
  have hpow : Tendsto (fun n ↦ (E.rootSeminorm (C n).domainElement + e n) ^ p)
      atTop (𝓝 (f.sublevelDistribution g c)) := by
    change Tendsto (fun n ↦ (E.rootSeminorm (f.oscillation g c n) + e n) ^ p)
      atTop (𝓝 (f.sublevelEnergyRoot g c ^ p))
    simpa only [Function.comp_def, add_zero] using
      ((Real.continuous_rpow_const (zero_lt_one.trans E.one_lt).le).tendsto
        (f.sublevelEnergyRoot g c + 0)).comp hend
  rw [le_sub_iff_add_le]
  apply le_of_tendsto_of_tendsto
    ((f.tendsto_oscillation_energy (g.bandTest b c) τ).add (f.tendsto_oscillation_energy g a)) hpow
  filter_upwards [tendsto_oscillationWidth.eventually_lt_const (show 0 < (b - a) / 2 by linarith)]
    with n hn
  let r := s n
  have hr : 0 < r := oscillationWidth_pos n
  have hgap : a + 2 * r < b := by dsimp [r, s]; linarith only [hn]
  have hd : Disjoint (support (A n).toFun) (support (B n).toFun) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    have hnear : g.toFun x < a + r := by
      by_contra! h
      apply hx
      change min _ (sublevelRamp r a (g.toFun x)) = 0
      rw [sublevelRamp_eq_zero h, min_eq_right (sawtooth_nonneg _ _)]
    apply hy
    change min _ (sublevelRamp r τ ((g.bandTest b c).toFun x)) = 0
    rw [band_ramp_eq, sublevelRamp_eq_zero (a := -b) (t := -g.toFun x) (by linarith only [hgap, hnear]),
      min_eq_right (sublevelRamp_nonneg _ _ _), min_eq_right (sawtooth_nonneg _ _)]
  obtain ⟨w, hw, hW⟩ := E.exists_min_add_const (C n).domainElement (u n + v n)
    (C n).ae_eq (hsum n) (add_nonneg (sublevelRamp_nonneg r a 0) (sublevelRamp_nonneg r (-b) 0))
  have hw' : w = ((A n).add (B n)).domainElement := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [hw, ((A n).add (B n)).ae_eq] with x hx hy
    rw [hx, hy]
    change min (min (sawtooth r (f.toFun x)) (sublevelRamp r c (g.toFun x)))
      ((offsetRamp r a (g.toFun x) + offsetRamp r (-b) (-g.toFun x)) +
        (sublevelRamp r a 0 + sublevelRamp r (-b) 0)) =
      min (sawtooth r (f.toFun x)) (sublevelRamp r a (g.toFun x)) +
        min (sawtooth r (f.toFun x)) (sublevelRamp r τ ((g.bandTest b c).toFun x))
    rw [band_ramp_eq]
    have hramp : (offsetRamp r a (g.toFun x) + offsetRamp r (-b) (-g.toFun x)) +
        (sublevelRamp r a 0 + sublevelRamp r (-b) 0) =
        sublevelRamp r a (g.toFun x) + sublevelRamp r (-b) (-g.toFun x) := by
      unfold offsetRamp
      ring
    rw [hramp]
    exact (add_oscillation_eq_min hr (sawtooth_nonneg _ _) (sawtooth_le hr _) hgap hbc).symm
  have hroot : E.rootSeminorm w ≤ E.rootSeminorm (C n).domainElement + e n := by
    exact hW.trans (add_le_add_right ((E.rootSeminorm.add_le' _ _).trans
      (add_le_add (E.rootSeminorm_le_graphSeminorm _) (E.rootSeminorm_le_graphSeminorm _))) _)
  have hEnergy : (E.energy w : ℝ) ≤ (E.rootSeminorm (C n).domainElement + e n) ^ p := by
    rw [E.energy_eq_root_rpow]
    exact Real.rpow_le_rpow (apply_nonneg _ _) hroot (zero_lt_one.trans E.one_lt).le
  rw [hw', (A n).energy_add_of_disjoint_support (B n) hd, NNReal.coe_add, add_comm] at hEnergy
  exact hEnergy

end PEnergy.CompactCore
end WalkDimensions
