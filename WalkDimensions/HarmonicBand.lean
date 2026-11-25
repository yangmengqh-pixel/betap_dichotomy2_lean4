import WalkDimensions.ClippedHarmonicEstimate
import WalkDimensions.CoreProductRoot
import WalkDimensions.CoreCutoffs
import WalkDimensions.VariationStability
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Indicator

/-!
# Energy in the bounded values of a harmonic domain element
-/

open Filter Function MeasureTheory Set
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [LocallyCompactSpace X] {m : Measure X} [IsFiniteMeasureOnCompacts m]
  {p : ℝ} (E : PEnergy m p)

omit [LocallyCompactSpace X] in
theorem exists_core_graph_ae_approximation (f : E.domain) {w : X → ℝ}
    (hf : (f : RealLp m p) =ᵐ[m] w) :
    ∃ g : ℕ → E.CompactCore,
      Tendsto (fun n ↦ E.rootSeminorm ((g n).domainElement - f)) atTop (𝓝 0) ∧
      ∀ᵐ x ∂m, Tendsto (fun n ↦ (g n).toFun x) atTop (𝓝 (w x)) := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt.le⟩
  obtain ⟨g, hg⟩ := E.exists_core_graph_approximation f
  have hG : Tendsto (fun n ↦ ((g n).domainElement : RealLp m p)) atTop (𝓝 (f : RealLp m p)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hg.eventually_lt_const hε] with n hn
    rw [dist_eq_norm]
    exact (E.norm_le_graphSeminorm ((g n).domainElement - f)).trans_lt hn
  obtain ⟨k, hk, hkAE⟩ := (tendstoInMeasure_of_tendsto_Lp hG).exists_seq_tendsto_ae
  have hroot : Tendsto (fun n ↦ E.rootSeminorm ((g n).domainElement - f)) atTop (𝓝 0) :=
    squeeze_zero (fun _ ↦ apply_nonneg _ _) (fun _ ↦ E.rootSeminorm_le_graphSeminorm _) hg
  refine ⟨g ∘ k, hroot.comp hk.tendsto_atTop, ?_⟩
  have hAE : ∀ᵐ x ∂m, ∀ n, ((g (k n)).domainElement : RealLp m p) x = (g (k n)).toFun x :=
    ae_all_iff.mpr fun n ↦ (g (k n)).ae_eq
  filter_upwards [hkAE, hAE, hf] with x hx hRep hxw
  change _ = _ at hxw
  simp only [hRep, hxw] at hx
  exact hx

/-- Testing harmonicity against a clipped deviation controls the mass of
its unclipped values for every absolutely continuous part of the energy measure. -/
theorem ac_mass_in_band_le_of_harmonic {f : E.domain} {w : X → ℝ}
    (hw : Measurable w) (hf : (f : RealLp m p) =ᵐ[m] w)
    (χ : E.CompactCore) {B U : Set X} (hB : IsCompact B) (hU : MeasurableSet U) (hUB : U ⊆ B)
    (hχ : ∀ x, χ.toFun x ∈ Icc (0 : ℝ) 1) (hχ₁ : EqOn χ.toFun (fun _ ↦ 1) U)
    (hSupp : support χ.toFun ⊆ B)
    (hHarmonic : ∀ v : E.CompactCore, support v.toFun ⊆ B →
      E.energyDerivativeMeasure f v.domainElement univ = 0)
    (κ : Measure X) [IsFiniteMeasure κ] (hκ : κ ≤ E.energyMeasure f) (hκm : κ ≪ m)
    (c : ℝ) {a : ℝ} (ha : 0 < a) :
    (κ (U ∩ {x | |w x - c| < a})).toReal ≤
      2 * a * (E.energyMeasure f B).toReal ^ ((p - 1) / p) * E.rootSeminorm χ.domainElement := by
  have hBm := hB.isClosed.measurableSet
  obtain ⟨ψ, v, hv, hvC, hψ, _, hψ₁, _⟩ :=
    E.exists_core_cutoff_of_isCompact_subset_isOpen hB isOpen_univ (subset_univ _)
  let V : E.CompactCore := ⟨ψ, v, hψ, hv, hvC⟩
  obtain ⟨g, hg, hgAE⟩ := E.exists_core_graph_ae_approximation f hf
  let vₙ (n : ℕ) := (g n).sub (V.smul c)
  let d (n : ℕ) := (vₙ n).clip ha.le
  let u (n : ℕ) := χ.mul (d n)
  have hvₙ (n : ℕ) : EqOn (vₙ n).toFun (fun x ↦ (g n).toFun x - c) B := by
    intro x hx
    change (g n).toFun x - c * v x = (g n).toFun x - c
    rw [hψ₁ hx, mul_one]
  have hSupport (n : ℕ) : support (u n).toFun ⊆ B := by
    intro x hx
    by_contra h
    exact hx (by rw [CompactCore.mul_apply, notMem_support.mp (fun hh ↦ h (hSupp hh)), zero_mul])
  have hd (n : ℕ) (x : X) : |(d n).toFun x| ≤ a := abs_symmetricClip_le ha.le _
  have hBoundRoot (n : ℕ) : E.rootSeminorm (u n).domainElement ≤ E.rootSeminorm (g n).domainElement +
      |c| * E.rootSeminorm V.domainElement + a * E.rootSeminorm χ.domainElement := by
    have h := χ.root_mul_le_of_bound (d n) zero_le_one ha.le
      (fun x ↦ by rw [abs_of_nonneg (hχ x).1]; exact (hχ x).2) (hd n)
    rw [one_mul] at h
    apply h.trans
    apply add_le_add_left
    apply ((vₙ n).root_mapLipschitz_le (symmetricClip a) (symmetricClip_lipschitz a)
      (symmetricClip_zero ha.le)).trans
    change E.rootSeminorm ((g n).domainElement + -(c • V.domainElement)) ≤ _
    apply (map_add_le_add _ _ _).trans_eq
    rw [map_neg_eq_map, map_smul_eq_mul, Real.norm_eq_abs]
  obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto _ hg).bddAbove
  have hRoot (n : ℕ) : E.rootSeminorm (g n).domainElement ≤ C + E.rootSeminorm f := by
    rw [← sub_add_cancel (g n).domainElement f]
    exact (map_add_le_add _ _ _).trans (add_le_add_left (hC (mem_range_self n)) _)
  let D := C + E.rootSeminorm f + |c| * E.rootSeminorm V.domainElement + a * E.rootSeminorm χ.domainElement
  have hD (n : ℕ) : E.rootSeminorm (u n).domainElement ≤ D := by
    exact (hBoundRoot n).trans (add_le_add_left (add_le_add_left (hRoot n) _) _)
  have hD₀ : 0 ≤ D := (apply_nonneg _ _).trans (hD 0)
  have htD := E.tendsto_energyDerivativeMeasure_sub_of_bounded hD₀ hD hg
  have hzero (n : ℕ) : E.energyDerivativeMeasure f (u n).domainElement univ = 0 :=
    hHarmonic (u n) (hSupport n)
  simp only [hzero, sub_zero] at htD
  let S := U ∩ {x | |w x - c| < a}
  let Sₙ (n : ℕ) := S ∩ {x | |(g n).toFun x - c| ≤ a}
  have hS : MeasurableSet S := hU.inter
    (measurableSet_lt (continuous_abs.measurable.comp (hw.sub measurable_const)) measurable_const)
  have hSₙ (n : ℕ) : MeasurableSet (Sₙ n) := hS.inter
    (isClosed_le ((g n).continuous.sub continuous_const).abs continuous_const).measurableSet
  have hLim : Tendsto (fun n ↦ κ (Sₙ n)) atTop (𝓝 (κ S)) := by
    apply tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure _ hS hSₙ
    filter_upwards [hκm.ae_le hgAE] with x hx
    by_cases hxS : x ∈ S
    · have hAbs : Tendsto (fun n ↦ |(g n).toFun x - c|) atTop (𝓝 |w x - c|) := (hx.sub_const c).abs
      filter_upwards [hAbs.eventually_lt_const hxS.2] with n hn
      exact iff_of_true ⟨hxS, hn.le⟩ hxS
    · exact Eventually.of_forall fun _ ↦ iff_of_false (fun h ↦ hxS h.1) hxS
  have hMass (n : ℕ) : ((E.energyMeasure (g n).domainElement) (Sₙ n)).toReal ≤
      |E.energyDerivativeMeasure (g n).domainElement (u n).domainElement univ| +
      a * (2 * (E.energyMeasure (g n).domainElement B).toReal ^ ((p - 1) / p) *
        E.rootSeminorm χ.domainElement) := by
    have hSub : Sₙ n ⊆ U ∩ {x | |(g n).toFun x - c| ≤ a} :=
      inter_subset_inter inter_subset_left (subset_refl _)
    have h := (g n).measure_band_le_of_clipped_variation (vₙ n) χ hBm hU hUB
      (fun x ↦ (hχ x).1) hχ₁ hSupp ha.le (hvₙ n)
    refine (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hSub)).trans (h.trans ?_)
    exact add_le_add_right (mul_le_mul_of_nonneg_left
      ((g n).energyDerivativeMeasure_variation_le_global_root χ hBm) ha.le) _
  let A n := |E.energyDerivativeMeasure (g n).domainElement (u n).domainElement univ| +
      a * (2 * (E.energyMeasure (g n).domainElement B).toReal ^ ((p - 1) / p) *
        E.rootSeminorm χ.domainElement)
  let M := 2 * a * (E.energyMeasure f B).toReal ^ ((p - 1) / p) * E.rootSeminorm χ.domainElement
  have hp := zero_lt_one.trans E.one_lt
  have hAlim : Tendsto A atTop (𝓝 M) := by
    have h := (E.tendsto_energyMeasure_real_of_root_sub hg hBm).rpow_const
      (Or.inr (div_nonneg (sub_nonneg.mpr E.one_lt.le) hp.le))
    have h' := htD.abs.add (((h.const_mul 2).mul_const (E.rootSeminorm χ.domainElement)).const_mul a)
    simpa only [A, M, abs_zero, zero_add, mul_left_comm a 2, mul_assoc] using h'
  have hRootMass (n : ℕ) : (κ (Sₙ n)).toReal ^ p⁻¹ ≤ A n ^ p⁻¹ +
      E.rootSeminorm ((g n).domainElement - f) := by
    let N := E.energyMeasureRoot (Sₙ n) (hSₙ n)
    have hLe := ENNReal.toReal_mono (measure_ne_top _ _) (hκ (Sₙ n))
    have h₁ := Real.rpow_le_rpow ENNReal.toReal_nonneg hLe (inv_nonneg.mpr hp.le)
    have h₂ := Real.rpow_le_rpow ENNReal.toReal_nonneg (hMass n) (inv_nonneg.mpr hp.le)
    rw [E.energyMeasure_real_eq f (hSₙ n), ← Real.rpow_mul (apply_nonneg _ _),
      mul_inv_cancel₀ hp.ne', Real.rpow_one] at h₁
    rw [E.energyMeasure_real_eq (g n).domainElement (hSₙ n), ← Real.rpow_mul (apply_nonneg _ _),
      mul_inv_cancel₀ hp.ne', Real.rpow_one] at h₂
    have hN := E.abs_energyMeasureRoot_sub_le (hSₙ n) (g n).domainElement f
    have hDiff := (abs_le.mp hN).1
    change -E.rootSeminorm ((g n).domainElement - f) ≤ N (g n).domainElement - N f at hDiff
    change _ ≤ N f at h₁
    change N (g n).domainElement ≤ A n ^ p⁻¹ at h₂
    linarith only [h₁, h₂, hDiff]
  have hReal := (ENNReal.continuousAt_toReal (measure_ne_top κ S)).tendsto.comp hLim
  change Tendsto (fun n ↦ (κ (Sₙ n)).toReal) atTop (𝓝 (κ S).toReal) at hReal
  have h₁ := hReal.rpow_const (Or.inr (inv_nonneg.mpr hp.le))
  have h₂ := (hAlim.rpow_const (Or.inr (inv_nonneg.mpr hp.le))).add hg
  rw [add_zero] at h₂
  have hLe := le_of_tendsto_of_tendsto h₁ h₂ (Eventually.of_forall hRootMass)
  have hM₀ : 0 ≤ M := by dsimp only [M]; positivity
  exact (Real.rpow_le_rpow_iff ENNReal.toReal_nonneg hM₀ (inv_pos.mpr hp)).mp hLe

end WalkDimensions.PEnergy
