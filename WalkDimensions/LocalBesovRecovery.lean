import WalkDimensions.BesovMaskedOscillation
import WalkDimensions.BesovRecovery
import WalkDimensions.CoreLatticeConvergence
import WalkDimensions.CoreRestriction
import WalkDimensions.EnergyMeasureConstruction
import WalkDimensions.LocalBesov
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# The reverse local Besov estimate

Oscillations preserve the local measure on a compact set. Masking them
by a cutoff adds an increment term that vanishes with the oscillation
width, allowing global recovery to bound the localized measure.
-/

open Filter Function MeasureTheory Metric Set TopologicalSpace
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SecondCountableTopology X] {m : Measure X}
  [m.Regular] [m.IsOpenPosMeasure] [SFinite m] {p : ℝ} (E : PEnergy m p)

theorem exists_local_besov_reverse_core {β : ℝ} (hβ : 0 < β)
    (hvol : VolumeDoubling m) (hPI : E.Poincare E.energyMeasure β)
    (hcap : E.CapacityUpperBound β) :
    ∃ C : ℝ≥0∞, 0 < C ∧ C ≠ ∞ ∧
      ∀ f : E.CompactCore, ∀ U : Set X, IsOpen U →
        E.energyMeasure f.domainElement U ≤ C * liminf (besovEnergy m p β U f.toFun) (𝓝[>] 0) := by
  obtain ⟨K, hK, hRecover⟩ := E.exists_energy_of_besov_liminf hβ hvol hcap
  obtain ⟨L, _, hL, hForward⟩ := E.global_besov_bound hvol hPI E.energyMeasure_univ
  let P := (2 : ℝ≥0∞) ^ p
  have hp := zero_lt_one.trans E.one_lt
  have hP : P ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hp.le (by norm_num)
  let C := (K + 1) * P
  have hC : C ≠ ∞ := ENNReal.mul_ne_top (ENNReal.add_ne_top.mpr ⟨hK, ENNReal.one_ne_top⟩) hP
  have hKpos : 0 < K + 1 := (show (0 : ℝ≥0∞) < 1 by norm_num).trans_le (le_add_of_nonneg_left bot_le)
  have hPpos : 0 < P := ENNReal.rpow_pos (by norm_num) (by norm_num)
  have hCpos : 0 < C := pos_iff_ne_zero.mpr (mul_ne_zero hKpos.ne' hPpos.ne')
  refine ⟨C, hCpos, hC, fun f U hU ↦ ?_⟩
  let B := liminf (besovEnergy m p β U f.toFun) (𝓝[>] 0)
  by_cases hB : B = ∞
  · change _ ≤ C * B
    rw [hB, ENNReal.mul_top hCpos.ne']
    exact le_top
  change E.energyMeasure f.domainElement U ≤ C * B
  rw [E.energyMeasure_core f, hU.measure_eq_iSup_isCompact f.coreEnergyMeasure]
  refine iSup_le fun S ↦ iSup_le fun hSU ↦ iSup_le fun hS ↦ ?_
  obtain ⟨v, ξ, hξ, hξC, hva, hξRange, hξOne, hξU⟩ :=
    E.exists_core_cutoff_of_isCompact_subset_isOpen hS hU hSU
  let V : E.CompactCore := ⟨v, ξ, hva, hξ, hξC⟩
  let M := L * (E.energy v : ℝ≥0∞)
  have hM : M ≠ ∞ := ENNReal.mul_ne_top hL ENNReal.coe_ne_top
  have hξB (s : ℝ) (hs : 0 < s) : besovEnergy m p β univ ξ s ≤ M := by
    rw [← besovEnergy_congr_ae hva]
    exact (le_iSup (fun t : Ioi (0 : ℝ) ↦ besovEnergy m p β univ (v : RealLp m p) t)
      ⟨s, hs⟩).trans (hForward v)
  have hBound (r : ℝ) (hr : 0 < r) :
      f.coreEnergyMeasure S ≤ C * (B + (ENNReal.ofReal r) ^ p * M) := by
    obtain ⟨w, hw⟩ := V.exists_core_mul (f.saw r)
    have hwVal (x : X) : w.toFun x = ξ x * sawtooth r (f.toFun x) := by
      rw [hw]
      rfl
    have hW : liminf (besovEnergy m p β univ w.toFun) (𝓝[>] 0) ≤
        P * (B + (ENNReal.ofReal r) ^ p * M) := by
      have hPt : ∀ᶠ s in 𝓝[>] (0 : ℝ), besovEnergy m p β univ w.toFun s ≤
          P * (besovEnergy m p β U f.toFun s + (ENNReal.ofReal r) ^ p * M) := by
        refine eventually_mem_nhdsWithin.mono fun s hs ↦ ?_
        rw [funext hwVal]
        refine (besovEnergy_masked_sawtooth_le hp hr f.continuous.measurable hξRange
          hU.measurableSet (subset_closure.trans hξU)).trans ?_
        gcongr
        exact hξB s hs
      apply (liminf_le_liminf hPt).trans_eq
      rw [ENNReal.liminf_const_mul_of_ne_top hP, liminf_add_const _ _ _
        (by isBoundedDefault) (by isBoundedDefault)]
    have hFinite : P * (B + (ENNReal.ofReal r) ^ p * M) ≠ ∞ :=
      ENNReal.mul_ne_top hP (ENNReal.add_ne_top.mpr ⟨hB, ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.ofReal_ne_top) hM⟩)
    obtain ⟨g, hg, hgE⟩ := hRecover (w.continuous.memLp_of_hasCompactSupport w.compactSupport)
      (hW.trans_lt hFinite.lt_top)
    have heq : g = w.domainElement := Subtype.ext (Lp.ext (hg.trans w.ae_eq.symm))
    have hwS : EqOn w.toFun (sawtooth r ∘ f.toFun) S := by
      intro x hx
      rw [hwVal, hξOne hx, one_mul]
      rfl
    rw [← f.coreEnergyMeasure_eq_of_eqOn_sawtooth w hS.isClosed.measurableSet hr hwS]
    calc
      w.coreEnergyMeasure S ≤ w.coreEnergyMeasure univ := measure_mono (subset_univ _)
      _ = (E.energy g : ℝ≥0∞) := by rw [w.coreEnergyMeasure_univ, heq]
      _ ≤ K * liminf (besovEnergy m p β univ w.toFun) (𝓝[>] 0) := hgE
      _ ≤ C * (B + (ENNReal.ofReal r) ^ p * M) := by
        dsimp only [C]
        rw [mul_assoc]
        exact (mul_le_mul_of_nonneg_left hW bot_le).trans (mul_le_mul_of_nonneg_right
          le_self_add bot_le)
  have ht : Tendsto (fun r : ℝ ↦ (ENNReal.ofReal r) ^ p * M) (𝓝 0) (𝓝 0) := by
    have h := (ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hM hp).comp
      (show Tendsto ENNReal.ofReal (𝓝 (0 : ℝ)) (𝓝 0) by
        simpa only [ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.tendsto 0)
    change Tendsto (fun r : ℝ ↦ M * (ENNReal.ofReal r) ^ p) (𝓝 0) (𝓝 0) at h
    simpa only [mul_comm M] using h
  have hLim : Tendsto (fun r : ℝ ↦ C * (B + (ENNReal.ofReal r) ^ p * M))
      (𝓝[>] 0) (𝓝 (C * B)) := by
    have h := (ht.const_add B).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    rw [add_zero] at h
    exact ENNReal.Tendsto.const_mul h (Or.inr hC)
  exact ge_of_tendsto hLim (eventually_mem_nhdsWithin.mono fun r hr ↦ hBound r hr)

end WalkDimensions.PEnergy
