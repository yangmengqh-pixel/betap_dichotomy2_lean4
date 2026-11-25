import WalkDimensions.CoreEnergyOscillation
import WalkDimensions.CoreLatticeConvergence
import WalkDimensions.CoreEnergySublevels

/-!
# Upper semicontinuity on compact sets

At a fixed oscillation scale the localized energy is continuous under
graph-norm convergence. The fixed-scale energy dominates the compact
set's measure, and the oscillation limit recovers that measure.
-/

open Filter Function MeasureTheory Set TopologicalSpace
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy.CompactCore

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {p : ℝ} {E : PEnergy μ p}

theorem coreEnergyMeasure_compact_lt_eventually {f : E.CompactCore} {g : ℕ → E.CompactCore}
    (hLp : Tendsto (fun n ↦ ‖((g n).domainElement : RealLp μ p) -
      (f.domainElement : RealLp μ p)‖) atTop (𝓝 0))
    (hRoot : Tendsto (fun n ↦ E.rootSeminorm ((g n).domainElement - f.domainElement))
      atTop (𝓝 0)) (K : Compacts X) {b : ℝ} (hb : (f.coreEnergyMeasure K).toReal < b) :
    ∀ᶠ n in atTop, ((g n).coreEnergyMeasure K).toReal < b := by
  obtain ⟨v, hv, _⟩ := E.exists_compactCore_sublevel_eq K.isCompact'
    isOpen_univ (subset_univ _)
  change {x | v.toFun x ≤ -1} = (K : Set X) at hv
  have hval : (f.coreEnergyMeasure K).toReal = f.sublevelDistribution v (-1) := by
    rw [← hv, f.coreEnergyMeasure_sublevel]
    exact ENNReal.toReal_ofReal (by
      change 0 ≤ f.sublevelEnergyRoot v (-1) ^ p
      exact Real.rpow_nonneg (f.sublevelEnergyRoot_nonneg v _) _)
  rw [hval] at hb
  have hp : ∀ᶠ n in atTop, f.sublevelDistribution v (-1 + 1 * oscillationWidth n) < b :=
    (f.tendsto_sublevelDistribution_add_width v (-1) 1 zero_le_one).eventually_lt_const hb
  obtain ⟨j, hj, hj'⟩ := (hp.and (tendsto_oscillationWidth.eventually_lt_const
    (show (0 : ℝ) < 1 by norm_num))).exists
  let a := -1 + 1 * oscillationWidth j
  have ha₀ : a < 0 := by dsimp [a]; linarith only [hj']
  have ha₁ : -1 < a := by dsimp [a]; linarith only [oscillationWidth_pos j]
  obtain ⟨k, hk, hk'⟩ := (((f.tendsto_oscillation_energy v a).eventually_lt_const hj).and
    (tendsto_oscillationWidth.eventually_lt_const (neg_pos.mpr ha₀))).exists
  have hk₀ : a + oscillationWidth k ≤ 0 := by linarith only [hk']
  have hbound (u : E.CompactCore) :
      u.coreEnergyMeasure K ≤ (E.energy (u.oscillation v a k) : ℝ≥0∞) := by
    let O := {x | v.toFun x < a}
    have hO : IsOpen O := isOpen_lt v.continuous continuous_const
    have hKO : (K : Set X) ⊆ O := by
      intro x hx
      have h := show x ∈ {y | v.toFun y ≤ -1} from hv.symm ▸ hx
      exact (show v.toFun x ≤ -1 from h).trans_lt ha₁
    let w := u.oscillationCore v a k
    have heq : EqOn w.toFun (sawtooth (oscillationWidth k) ∘ u.toFun) O := by
      intro x hx
      change min (sawtooth (oscillationWidth k) (u.toFun x))
        (sublevelRamp (oscillationWidth k) a (v.toFun x)) = _
      rw [sublevelRamp_eq_cap (oscillationWidth_pos k).le (show v.toFun x < a from hx).le,
        min_eq_left (sawtooth_le (oscillationWidth_pos k) _)]
      rfl
    rw [← u.coreEnergyMeasure_eq_of_eqOn_sawtooth_dyadic (A := (K : Set X)) w K.isCompact'.isClosed.measurableSet
      hO hKO k heq]
    exact (measure_mono (subset_univ _)).trans_eq w.coreEnergyMeasure_univ
  have ht := tendsto_oscillation_energy_of_graph_sub_tendsto v a k hk₀ hLp hRoot
  filter_upwards [ht.eventually_lt_const hk] with n hn
  have h := ENNReal.toReal_mono ENNReal.coe_ne_top (hbound (g n))
  rw [ENNReal.coe_toReal] at h
  exact h.trans_lt hn

end WalkDimensions.PEnergy.CompactCore
