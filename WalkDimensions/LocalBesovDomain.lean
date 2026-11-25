import WalkDimensions.LocalBesovRecovery
import WalkDimensions.BesovStability
import WalkDimensions.EnergyMeasureClarkson

/-!
# Local reverse Besov estimates on the whole energy domain
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SecondCountableTopology X] {m : Measure X}
  [m.Regular] [m.IsOpenPosMeasure] [SFinite m] {p : ℝ} (E : PEnergy m p)

theorem exists_local_besov_reverse {β : ℝ} (hβ : 0 < β)
    (hvol : VolumeDoubling m) (hPI : E.Poincare E.energyMeasure β)
    (hcap : E.CapacityUpperBound β) :
    ∃ C : ℝ≥0∞, 0 < C ∧ C ≠ ∞ ∧ ∀ (f : E.domain) (U : Set X), IsOpen U →
      E.energyMeasure f U ≤ C * liminf (besovEnergy m p β U (f : RealLp m p)) (𝓝[>] 0) := by
  obtain ⟨K, hK, hKT, hCore⟩ := E.exists_local_besov_reverse_core hβ hvol hPI hcap
  obtain ⟨L, _, hLT, hGlobal⟩ := E.global_besov_bound hvol hPI E.energyMeasure_univ
  have hp := zero_lt_one.trans E.one_lt
  let P := (2 : ℝ≥0∞) ^ p
  let C := K * P
  have hPT : P ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hp.le (by norm_num)
  have hP : 0 < P := ENNReal.rpow_pos (by norm_num) (by norm_num)
  have hCT : C ≠ ∞ := ENNReal.mul_ne_top hKT hPT
  have hC : 0 < C := pos_iff_ne_zero.mpr (mul_ne_zero hK.ne' hP.ne')
  refine ⟨C, hC, hCT, fun f U hU ↦ ?_⟩
  let B := liminf (besovEnergy m p β U (f : RealLp m p)) (𝓝[>] (0 : ℝ))
  change E.energyMeasure f U ≤ C * B
  by_cases hBT : B = ∞
  · rw [hBT, ENNReal.mul_top hC.ne']
    exact le_top
  obtain ⟨g, hg⟩ := E.exists_core_graph_approximation f
  have hroot : Tendsto (fun n ↦ E.rootSeminorm ((g n).domainElement - f)) atTop (𝓝 0) :=
    squeeze_zero (fun _ ↦ apply_nonneg _ _) (fun _ ↦ E.rootSeminorm_le_graphSeminorm _) hg
  let M (n : ℕ) := L * (E.energy (f - (g n).domainElement) : ℝ≥0∞)
  have hMeas : AEMeasurable (f : RealLp m p) m :=
    (Lp.aestronglyMeasurable _).aemeasurable
  let a := hMeas.mk (f : RealLp m p)
  have ha : Measurable a := hMeas.measurable_mk
  have hae : (f : RealLp m p) =ᵐ[m] a := hMeas.ae_eq_mk
  have hscale (n : ℕ) (r : ℝ) (hr : 0 < r) :
      besovEnergy m p β U (g n).toFun r ≤ P * (besovEnergy m p β U (f : RealLp m p) r + M n) := by
    let v := f - (g n).domainElement
    have hG : ((g n).domainElement : RealLp m p) =ᵐ[m] a - (v : RealLp m p) := by
      have he : (g n).domainElement = f - v := by
        change (g n).domainElement = f - (f - (g n).domainElement)
        abel
      rw [he]
      change (f.val - v.val : RealLp m p) =ᵐ[m] _
      filter_upwards [Lp.coeFn_sub (f : RealLp m p) (v : RealLp m p), hae] with x hx hxa
      rw [hx, Pi.sub_apply, hxa]
      rfl
    have hM' : besovEnergy m p β U (v : RealLp m p) r ≤ M n := by
      have hsub : besovEnergy m p β U (v : RealLp m p) r ≤
          besovEnergy m p β univ (v : RealLp m p) r :=
        mul_le_mul_of_nonneg_left (lintegral_mono_set (subset_univ _)) bot_le
      exact hsub.trans ((le_iSup (fun s : Ioi (0 : ℝ) ↦ besovEnergy m p β univ (v : RealLp m p) s)
        ⟨r, hr⟩).trans (hGlobal v))
    rw [besovEnergy_congr_ae ((g n).ae_eq.symm.trans hG)]
    apply (besovEnergy_sub_le_local hp.le ha U).trans
    rw [← besovEnergy_congr_ae hae]
    exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hM') bot_le
  have hBound (n : ℕ) : E.energyMeasure (g n).domainElement U ≤ C * (B + M n) := by
    have he : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r := eventually_mem_nhdsWithin
    have h := liminf_le_liminf (he.mono (fun r hr ↦ hscale n r hr))
    rw [ENNReal.liminf_const_mul_of_ne_top hPT,
      liminf_add_const _ _ _ (by isBoundedDefault) (by isBoundedDefault)] at h
    calc
      _ ≤ K * liminf (besovEnergy m p β U (g n).toFun) (𝓝[>] 0) := hCore (g n) U hU
      _ ≤ C * (B + M n) := by
        dsimp only [C, B]
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left h bot_le
  have hMlim : Tendsto M atTop (𝓝 0) := by
    have h := hroot.rpow_const (Or.inr hp.le : (0 : ℝ) ≠ 0 ∨ 0 ≤ p)
    rw [Real.zero_rpow hp.ne'] at h
    have hE : Tendsto (fun n ↦ (E.energy (f - (g n).domainElement) : ℝ)) atTop (𝓝 0) := by
      convert h using 1
      funext n
      rw [E.energy_eq_root_rpow, ← neg_sub, ← show -(f - (g n).domainElement) =
        (g n).domainElement - f by abel, map_neg_eq_map]
    have h' := ENNReal.tendsto_ofReal hE
    simp only [ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_zero] at h'
    simpa only [M, mul_zero] using ENNReal.Tendsto.const_mul h' (Or.inr hLT)
  have hR := E.tendsto_energyMeasure_real_of_root_sub hroot hU.measurableSet
  have hR' := ENNReal.tendsto_ofReal hR
  simp_rw [ENNReal.ofReal_toReal (measure_ne_top _ _)] at hR'
  have hlim := hMlim.const_add B
  rw [add_zero] at hlim
  exact le_of_tendsto_of_tendsto hR' (ENNReal.Tendsto.const_mul hlim (Or.inr hCT))
    (Eventually.of_forall hBound)

end WalkDimensions.PEnergy
