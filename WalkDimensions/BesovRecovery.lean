import WalkDimensions.BesovConvolution
import WalkDimensions.BesovStability
import WalkDimensions.EnergyClosedness
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Global recovery from the small-scale Besov liminf

The compact input in the discrete convolution may vary with the radius.
At each chosen radius, density in the ambient space controls the discarded
part of the increments at that fixed scale.
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SecondCountableTopology X] {m : Measure X} [SFinite m]
  [m.IsOpenPosMeasure] [m.Regular] {p : ℝ} (E : PEnergy m p)

theorem exists_energy_of_besov_liminf {β : ℝ} (hβ : 0 < β)
    (hvol : VolumeDoubling m) (hcap : E.CapacityUpperBound β) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ {u : X → ℝ}, MemLp u (ENNReal.ofReal p) m →
      liminf (besovEnergy m p β univ u) (𝓝[>] 0) < ∞ →
      ∃ f : E.domain, (f : RealLp m p) =ᵐ[m] u ∧
        (E.energy f : ℝ≥0∞) ≤ K * liminf (besovEnergy m p β univ u) (𝓝[>] 0) := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt.le⟩
  have hp : 0 < p := zero_lt_one.trans E.one_lt
  obtain ⟨K, J, hK, hJ, happ⟩ := E.exists_energy_approximation_at_scale hvol hcap
  obtain ⟨D, _, hD⟩ := hvol
  let C : ℝ≥0∞ := (2 : ℝ≥0∞) ^ p * 2
  have hC : C ≠ ∞ := ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg hp.le (by norm_num)) (by norm_num)
  let K' := K * C
  have hK' : K' ≠ ∞ := ENNReal.mul_ne_top hK hC
  refine ⟨K', hK', fun {u} hu hlim ↦ ?_⟩
  let w := hu.aestronglyMeasurable.mk u
  have hw₀ : u =ᵐ[m] w := hu.aestronglyMeasurable.ae_eq_mk
  have hw : Measurable w := hu.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hwLp : MemLp w (ENNReal.ofReal p) m := hu.ae_eq hw₀
  have hcongr : besovEnergy m p β univ u = besovEnergy m p β univ w :=
    funext (besovEnergy_congr_ae hw₀ p β univ)
  rw [hcongr] at hlim ⊢
  let L := liminf (besovEnergy m p β univ w) (𝓝[>] 0)
  have hL : L ≠ ∞ := hlim.ne
  let wLp := hwLp.toLp w
  have hwAE : wLp =ᵐ[m] w := MemLp.coeFn_toLp hwLp
  have hnear (b : ℝ) (hb : L.toReal < b) (ε : ℝ) (hε : 0 < ε) :
      ∃ f : E.domain, ‖(f : RealLp m p) - wLp‖ < ε ∧
        (E.energy f : ℝ≥0∞) ≤ K' * ENNReal.ofReal b := by
    have hb₀ : 0 < b := ENNReal.toReal_nonneg.trans_lt hb
    have hb' : L < ENNReal.ofReal b := by
      rw [← ENNReal.ofReal_toReal hL]
      exact ENNReal.ofReal_lt_ofReal_iff'.mpr ⟨hb, hb₀⟩
    have hgood : ∃ᶠ s in 𝓝[>] (0 : ℝ), besovEnergy m p β univ w s < ENNReal.ofReal b :=
      frequently_lt_of_liminf_lt (by isBoundedDefault) hb'
    let M := J * (C * ENNReal.ofReal b)
    have hM : M ≠ ∞ := ENNReal.mul_ne_top hJ (ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top)
    have hsmall : Tendsto (fun s : ℝ ↦ M * (ENNReal.ofReal s) ^ β) (𝓝 0) (𝓝 0) := by
      apply (ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hM hβ).comp
      simpa only [ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.tendsto 0
    have hεp : 0 < ENNReal.ofReal (ε / 2) ^ p :=
      ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr (half_pos hε)) ENNReal.ofReal_ne_top
    have hevent : ∀ᶠ s in 𝓝[>] (0 : ℝ), M * (ENNReal.ofReal s) ^ β <
        ENNReal.ofReal (ε / 2) ^ p :=
      ((tendsto_order.1 hsmall).2 _ hεp).filter_mono nhdsWithin_le_nhds
    obtain ⟨s, hsE, hs, hsSmall⟩ :=
      (hgood.and_eventually ((show ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Ioo (0 : ℝ) 1 from Ioo_mem_nhdsGT zero_lt_one).and hevent)).exists
    let F := (ENNReal.ofReal s) ^ (-β) * ((2 : ℝ≥0∞) ^ p * (1 + ENNReal.ofReal D))
    have hF : F ≠ ∞ := ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr hs.1) ENNReal.ofReal_ne_top)
      (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hp.le (by norm_num))
        (ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, ENNReal.ofReal_ne_top⟩))
    have htailSmall : Tendsto (fun δ : ℝ ↦ F * (ENNReal.ofReal δ) ^ p) (𝓝 0) (𝓝 0) := by
      apply (ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hF hp).comp
      simpa only [ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.tendsto 0
    have hδgood : ∀ᶠ δ in 𝓝[>] (0 : ℝ), F * (ENNReal.ofReal δ) ^ p < ENNReal.ofReal b :=
      ((tendsto_order.1 htailSmall).2 _ (ENNReal.ofReal_pos.mpr hb₀)).filter_mono nhdsWithin_le_nhds
    obtain ⟨δ, hδ, hδsmall⟩ :=
      ((show ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ∈ Ioo (0 : ℝ) (ε / 2) from Ioo_mem_nhdsGT (half_pos hε)).and hδgood).exists
    obtain ⟨v, hvSupp, htail, hv, hvLp⟩ := hwLp.exists_hasCompactSupport_eLpNorm_sub_le
      ENNReal.ofReal_ne_top (ENNReal.ofReal_ne_zero_iff.mpr hδ.1)
    have hvE : besovEnergy m p β univ v s ≤ C * ENNReal.ofReal b := by
      have htailE : besovEnergy m p β univ (w - v) s ≤ ENNReal.ofReal b := by
        have h := besovEnergy_le_eLpNorm_of_doubling (β := β) hp hs.1 hD (hw.sub hv.measurable)
        exact (h.trans (mul_le_mul_of_nonneg_left (ENNReal.rpow_le_rpow htail hp.le) bot_le))
          |>.trans hδsmall.le
      have hvEq : v = w - (w - v) := by ext x; simp
      nth_rw 1 [hvEq]
      calc
        _ ≤ (2 : ℝ≥0∞) ^ p * (besovEnergy m p β univ w s +
            besovEnergy m p β univ (w - v) s) :=
          besovEnergy_sub_le hp.le hw
        _ ≤ C * ENNReal.ofReal b := by
          dsimp only [C]
          rw [mul_assoc, two_mul]
          exact mul_le_mul_of_nonneg_left (add_le_add hsE.le htailE) bot_le
    obtain ⟨f, hfE, hfError⟩ := happ hv.measurable hvSupp hvLp hs
    refine ⟨f, ?_, hfE.trans ((mul_le_mul_of_nonneg_left hvE bot_le).trans_eq (mul_assoc _ _ _).symm)⟩
    let vLp := hvLp.toLp v
    have hfNorm : ‖(f : RealLp m p) - vLp‖ < ε / 2 := by
      have he : (ENNReal.ofReal ‖(f : RealLp m p) - vLp‖) ^ p < ENNReal.ofReal (ε / 2) ^ p :=
        (hfError.trans ((mul_le_mul_of_nonneg_left hvE bot_le).trans_eq (by dsimp only [M]; ac_rfl)))
          |>.trans_lt hsSmall
      exact (ENNReal.ofReal_lt_ofReal_iff (half_pos hε)).mp
        ((ENNReal.strictMono_rpow_of_pos hp).lt_iff_lt.mp he)
    have hvlp : ‖vLp - wLp‖ < ε / 2 := by
      rw [norm_sub_rev, Lp.norm_def]
      have hAE : (wLp - vLp : RealLp m p) =ᵐ[m] (w - v) := by
        filter_upwards [Lp.coeFn_sub wLp vLp, hwAE, MemLp.coeFn_toLp hvLp] with x hx hwx hvx
        change vLp x = v x at hvx
        simp only [hx, Pi.sub_apply, hwx, hvx]
      rw [eLpNorm_congr_ae hAE]
      exact ((ENNReal.toReal_mono ENNReal.ofReal_ne_top htail).trans_eq
        (ENNReal.toReal_ofReal hδ.1.le)).trans_lt hδ.2
    calc
      _ ≤ ‖(f : RealLp m p) - vLp‖ + ‖vLp - wLp‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < ε := by linarith
  have hRecover (b : ℝ) (hb : L.toReal < b) : ∃ f : E.domain, (f : RealLp m p) = wLp ∧
      (E.energy f : ℝ≥0∞) ≤ K' * ENNReal.ofReal b := by
    let M := K' * ENNReal.ofReal b
    have hM : M ≠ ∞ := ENNReal.mul_ne_top hK' ENNReal.ofReal_ne_top
    obtain ⟨f, hf, hroot⟩ := E.exists_of_bounded_lp_approximation wLp
      (M := M.toReal ^ p⁻¹) (fun ε hε ↦ by
        obtain ⟨g, hg, hgE⟩ := hnear b hb ε hε
        refine ⟨g, hg, ?_⟩
        have hgE' := ENNReal.toReal_mono hM hgE
        rw [ENNReal.coe_toReal] at hgE'
        rw [E.rootSeminorm_apply]
        exact Real.rpow_le_rpow (NNReal.coe_nonneg _) hgE' (inv_nonneg.mpr hp.le))
    refine ⟨f, hf, (ENNReal.toReal_le_toReal ENNReal.coe_ne_top hM).mp ?_⟩
    rw [ENNReal.coe_toReal, E.energy_eq_root_rpow]
    have h := Real.rpow_le_rpow (apply_nonneg _ _) hroot hp.le
    rwa [← Real.rpow_mul ENNReal.toReal_nonneg, inv_mul_cancel₀ hp.ne', Real.rpow_one] at h
  obtain ⟨f, hf, _⟩ := hRecover (L.toReal + 1) (lt_add_one _)
  refine ⟨f, by rw [hf]; exact hwAE.trans hw₀.symm, ?_⟩
  have hBound (ε : ℝ) (hε : 0 < ε) :
      (E.energy f : ℝ≥0∞) ≤ K' * ENNReal.ofReal (L.toReal + ε) := by
    obtain ⟨g, hg, hgE⟩ := hRecover (L.toReal + ε) (lt_add_of_pos_right _ hε)
    have heq : g = f := Subtype.ext (hg.trans hf.symm)
    simpa only [heq] using hgE
  have hLimit : Tendsto (fun ε : ℝ ↦ K' * ENNReal.ofReal (L.toReal + ε))
      (𝓝[>] 0) (𝓝 (K' * L)) := by
    have hInner : Tendsto (fun ε : ℝ ↦ ENNReal.ofReal (L.toReal + ε)) (𝓝 0) (𝓝 L) := by
      simpa only [Function.comp_def, id_eq, add_zero, ENNReal.ofReal_toReal hL] using
        (ENNReal.continuous_ofReal.tendsto (L.toReal + 0)).comp
          (tendsto_const_nhds.add (@tendsto_id ℝ (𝓝 0)))
    exact ENNReal.Tendsto.const_mul (hInner.mono_left nhdsWithin_le_nhds) (Or.inr hK')
  exact ge_of_tendsto hLimit (eventually_mem_nhdsWithin.mono fun ε hε ↦ hBound ε hε)

end WalkDimensions.PEnergy
