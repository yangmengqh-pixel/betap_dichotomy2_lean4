import WalkDimensions.DyadicOscillation
import WalkDimensions.RampEnergy
import WalkDimensions.SawtoothEnergy

/-!
# Convergence of localized oscillation energies

The dyadic refinement identity bounds the energy of each finer oscillation
by the energy at a fixed coarse scale and two vanishing ramp errors.
-/

open Filter Function MeasureTheory Set
open scoped Topology

namespace WalkDimensions

theorem tendsto_oscillationWidth : Tendsto oscillationWidth atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

private theorem offsetRamp_neg_add_width {r s U : ℝ} (hrs : r ≤ s)
    (hU : U ≤ s) : -(offsetRamp r (-s) (-U)) + r = min (s - U) r := by
  have hzero : sublevelRamp r (-s) 0 = 0 := sublevelRamp_eq_zero (by linarith only [hrs])
  have hcap : -s + r - -U ≤ r := by linarith only [hU]
  unfold offsetRamp
  rw [hzero, sub_zero, sublevelRamp, min_eq_left hcap]
  by_cases h : s - U ≤ r
  · rw [min_eq_left h, max_eq_left (by linarith only [h])]
    ring
  · rw [min_eq_right (le_of_not_ge h), max_eq_right (by linarith only [lt_of_not_ge h]),
      neg_zero, zero_add]

namespace PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {p : ℝ} (E : PEnergy μ p)

private theorem exists_refinement_error (f : E.domain) {u : X → ℝ}
    (hfu : (f : RealLp μ p) =ᵐ[μ] u) (hu : Continuous u) (hc : HasCompactSupport u) (n : ℕ) :
    ∃ k : ℕ → E.domain,
      (∀ m > n, (k m : RealLp μ p) =ᵐ[μ]
        fun x ↦ min (oscillationWidth n - sawtooth (oscillationWidth n) (u x))
          (oscillationWidth m) - oscillationWidth m) ∧
      Tendsto (fun m ↦ E.rootSeminorm (k m)) atTop (𝓝 0) := by
  let s := oscillationWidth n
  obtain ⟨f', hf', _⟩ := E.exists_sawtooth_energy_eq f hfu hu hc (oscillationWidth_pos n)
  have hneg : ((-f' : E.domain) : RealLp μ p) =ᵐ[μ] (fun x ↦ -sawtooth s (u x)) := by
    filter_upwards [Lp.coeFn_neg (f' : RealLp μ p), hf'] with x hx hy
    change (-(f' : RealLp μ p)) x = _
    rw [hx, Pi.neg_apply, hy]
    rfl
  have hc' : HasCompactSupport (fun x ↦ -sawtooth s (u x)) :=
    hc.comp_left (g := fun t ↦ -sawtooth s t) (show -(sawtooth s 0) = 0 by rw [sawtooth_zero, neg_zero])
  obtain ⟨k, hk, hlim⟩ := E.exists_ramp_graph_tendsto_zero (-f') hneg hc' (-s) oscillationWidth
    (fun m ↦ (oscillationWidth_pos m).le) oscillationWidth_antitone tendsto_oscillationWidth
  refine ⟨fun m ↦ -k m, ?_, ?_⟩
  · intro m hm
    filter_upwards [Lp.coeFn_neg (k m : RealLp μ p), hk m] with x hx hy
    change (-(k m : RealLp μ p)) x = _
    rw [hx, Pi.neg_apply, hy]
    have h := offsetRamp_neg_add_width (oscillationWidth_antitone hm.le)
      (sawtooth_le (oscillationWidth_pos n) (u x))
    change -(offsetRamp (oscillationWidth m) (-s) (-sawtooth s (u x))) = _
    linarith only [h]
  · simpa only [map_neg_eq_map] using
      (squeeze_zero (fun m ↦ apply_nonneg (E.rootSeminorm) (k m))
        (fun m ↦ E.rootSeminorm_le_graphSeminorm (k m)) hlim)

theorem tendsto_root_localized_oscillation (f g : E.domain) {u v : X → ℝ}
    (hfu : (f : RealLp μ p) =ᵐ[μ] u) (hgv : (g : RealLp μ p) =ᵐ[μ] v)
    (hu : Continuous u) (hv : Continuous v) (hc : HasCompactSupport u) (hcv : HasCompactSupport v)
    (a : ℝ) (w : ℕ → E.domain)
    (hw : ∀ n, (w n : RealLp μ p) =ᵐ[μ] fun x ↦
      min (sawtooth (oscillationWidth n) (u x)) (sublevelRamp (oscillationWidth n) a (v x))) :
    Tendsto (fun n ↦ E.rootSeminorm (w n)) atTop (𝓝 (⨅ n, E.rootSeminorm (w n))) := by
  let ε := oscillationWidth
  let H (n : ℕ) (x : X) := min (sawtooth (ε n) (u x)) (sublevelRamp (ε n) a (v x))
  let A (n : ℕ) := E.rootSeminorm (w n)
  obtain ⟨ramps, hramps, hramps_lim⟩ := E.exists_ramp_graph_tendsto_zero g hgv hcv a ε
    (fun m ↦ (oscillationWidth_pos m).le) oscillationWidth_antitone tendsto_oscillationWidth
  have hR : Tendsto (fun m ↦ E.rootSeminorm (ramps m)) atTop (𝓝 0) :=
    squeeze_zero (fun _ ↦ apply_nonneg _ _) (fun m ↦ E.rootSeminorm_le_graphSeminorm (ramps m))
      hramps_lim
  have hupper (n : ℕ) : ∃ err : ℕ → ℝ, Tendsto err atTop (𝓝 0) ∧
      ∀ m > n, A m ≤ A n + err m := by
    obtain ⟨stripes, hstripes, hS⟩ := E.exists_refinement_error f hfu hu hc n
    refine ⟨fun m ↦ E.rootSeminorm (ramps m) + E.rootSeminorm (stripes m), ?_, ?_⟩
    · simpa only [zero_add] using hR.add hS
    · intro m hm
      obtain ⟨_, _, hcont, hcomp, _⟩ := E.exists_localized_oscillation f g hfu hgv hu hv hc (ε n) a
      obtain ⟨t, ht, hEt⟩ :=
        E.exists_sawtooth_energy_eq (w n) (hw n) hcont hcomp (oscillationWidth_pos m)
      obtain ⟨b, hb, hEb⟩ :=
        E.exists_min_add_const t (ramps m) ht (hramps m) (sublevelRamp_nonneg (ε m) a 0)
      obtain ⟨d, hd, hEd⟩ :=
        E.exists_min_add_const b (stripes m) hb (hstripes m hm) (oscillationWidth_pos m).le
      have hdw : d = w m := by
        apply Subtype.ext
        apply Lp.ext
        filter_upwards [hd, hw m] with x hx hy
        rw [hx, hy]
        change min (min (sawtooth (ε m) (H n x))
            (offsetRamp (ε m) a (v x) + sublevelRamp (ε m) a 0))
            (min (ε n - sawtooth (ε n) (u x)) (ε m) - ε m + ε m) = H m x
        simpa only [H, offsetRamp, sub_add_cancel] using
          (localized_oscillation_refine hm a (u x) (v x)).symm
      have hAt : E.rootSeminorm t = A n := by
        dsimp only [A]
        rw [E.rootSeminorm_apply, E.rootSeminorm_apply, hEt]
      dsimp [A] at *
      rw [← hdw]
      linarith only [hEd, hEb, hAt]
  have hbdd : BddBelow (range A) := ⟨0, by rintro _ ⟨n, rfl⟩; exact apply_nonneg _ _⟩
  exact tendsto_of_eventually_le_add_vanishing hbdd hupper

end PEnergy
end WalkDimensions
