import WalkDimensions.CompactEnergyLimit
import WalkDimensions.ContinuousConvolution
import WalkDimensions.ConvolutionEnergy
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Recovery of compactly supported continuous functions

In the supercritical range, discrete convolutions recover the ambient
(L^p) class from the small-scale Besov bound. The core energy measure controls the energy of the approximations.
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SecondCountableTopology X] {m : Measure X} [SFinite m]
  [IsFiniteMeasureOnCompacts m] [m.IsOpenPosMeasure] {p : ℝ} (E : PEnergy m p)

theorem exists_energy_of_compact_besov_liminf {d β : ℝ}
    (hvol : AhlforsRegular m d) (hβ : d < β) {Γ : E.domain → Measure X}
    (hΓ : ∀ f, Γ f univ = (E.energy f : ℝ≥0∞)) (hPI : E.Poincare Γ β) (hcap : E.CapacityUpperBound β) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ {u : X → ℝ}, Continuous u → HasCompactSupport u →
      liminf (besovEnergy m p β univ u) (𝓝[>] 0) < ∞ →
      ∃ f : E.domain, (f : RealLp m p) =ᵐ[m] u ∧
        (E.energy f : ℝ≥0∞) ≤ K * liminf (besovEnergy m p β univ u) (𝓝[>] 0) := by
  obtain ⟨C, A, hC, hA, hconv⟩ :=
    E.exists_continuous_discrete_convolution hvol hβ hPI hΓ hcap
  obtain ⟨K, hK, hEconv⟩ := E.exists_discrete_convolution_energy_le hvol.volumeDoubling
    (β := β) hA hC
  let η := 2 * A + 3
  have hη : 0 < η := by dsimp [η]; linarith
  let K' := K * ENNReal.ofReal (η ^ β)
  have hK' : K' ≠ ∞ := ENNReal.mul_ne_top hK ENNReal.ofReal_ne_top
  refine ⟨K', hK', fun {u} hu hc hfin ↦ ?_⟩
  let L := liminf (besovEnergy m p β univ u) (𝓝[>] 0)
  have hL : L ≠ ∞ := hfin.ne
  have hU := hu.memLp_of_hasCompactSupport (p := ENNReal.ofReal p) hc (μ := m)
  let S := cthickening 1 (tsupport u)
  have hS : IsCompact S := hc.isCompact.cthickening
  have huS : tsupport u ⊆ S := self_subset_cthickening _
  have hp : 0 < p := zero_lt_one.trans E.one_lt
  let uLp := continuousLp (m := m) p u hu hc
  have hULp : uLp =ᵐ[m] u := MemLp.coeFn_toLp hU
  have hnear (b : ℝ) (hb : L.toReal < b) (ε : ℝ) (hε : 0 < ε) :
      ∃ (f : E.domain) (v : X → ℝ), (f : RealLp m p) =ᵐ[m] v ∧
        (∀ x, |v x - u x| ≤ S.indicator (fun _ ↦ ε) x) ∧
        (E.energy f : ℝ≥0∞) ≤ K' * ENNReal.ofReal b := by
    obtain ⟨δ, hδ, hδconv⟩ := hconv hu hc ε hε
    have hb' : L < ENNReal.ofReal b := by
      rw [← ENNReal.ofReal_toReal hL]
      exact ENNReal.ofReal_lt_ofReal_iff'.mpr ⟨hb, ENNReal.toReal_nonneg.trans_lt hb⟩
    have hgood : ∃ᶠ s in 𝓝[>] (0 : ℝ), besovEnergy m p β univ u s < ENNReal.ofReal b :=
      frequently_lt_of_liminf_lt (by isBoundedDefault) hb'
    obtain ⟨s, hsE, hs⟩ := (hgood.and_eventually (Ioo_mem_nhdsGT (mul_pos hη hδ))).exists
    let r := s / η
    have hr : 0 < r := div_pos hs.1 hη
    have hrδ : r ∈ Ioo (0 : ℝ) δ := ⟨hr, (div_lt_iff₀ hη).2 (by simpa only [mul_comm] using hs.2)⟩
    obtain ⟨t, g, w, V, hsep, hgw, hw, hV, hpu, hroot, hvAE, _, hvE, hvS, hvV⟩ := hδconv r hrδ
    let a (z : X) := ⨍ y in ball z r, u y ∂m
    let f := ∑ z ∈ t, a z • g z
    let v (x : X) := ∑ z ∈ t, a z * w z x
    have he := hEconv t r hr hsep g w hgw (fun z ↦ (hw z).2) hroot V hV hpu u hu.measurable hU hvV
    have hscale : ENNReal.ofReal (r ^ (-β)) =
        ENNReal.ofReal (η ^ β) * (ENNReal.ofReal (η * r)) ^ (-β) := by
      rw [ENNReal.ofReal_rpow_of_pos (mul_pos hη hr), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [Real.mul_rpow hη.le hr.le, ← mul_assoc, ← Real.rpow_add hη,
        add_neg_cancel, Real.rpow_zero, one_mul]
    have hrs : η * r = s := by dsimp [r]; field_simp
    have hE : (E.energy f : ℝ≥0∞) ≤ K' * ENNReal.ofReal b := by
      calc
        _ ≤ _ := he
        _ = K' * besovEnergy m p β univ u s := by
          change K * ENNReal.ofReal (r ^ (-β)) * (∫⁻ x, ballMoment m p u (η * r) x ∂m) = _
          rw [hscale, hrs, besovEnergy, Measure.restrict_univ]
          dsimp only [K']
          simp only [mul_assoc]
        _ ≤ _ := mul_le_mul_of_nonneg_left hsE.le bot_le
    refine ⟨f, v, hvAE, fun x ↦ ?_, hE⟩
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx]
      exact hvE x
    · rw [indicator_of_notMem hx]
      have hv₀ : v x = 0 := notMem_support.mp fun h ↦ hx (hvS (subset_closure h))
      have hu₀ : u x = 0 := notMem_support.mp fun h ↦ hx (huS (subset_closure h))
      rw [hv₀, hu₀, sub_self, abs_zero]
  have hRecover (b : ℝ) (hb : L.toReal < b) :
      ∃ f : E.domain, (f : RealLp m p) = uLp ∧
        (E.energy f : ℝ≥0∞) ≤ K' * ENNReal.ofReal b := by
    let M := K' * ENNReal.ofReal b
    have hM : M ≠ ∞ := ENNReal.mul_ne_top hK' ENNReal.ofReal_ne_top
    obtain ⟨f, hf, hroot⟩ := E.exists_of_uniform_approximation uLp u hULp
      hS.isClosed.measurableSet (hS.measure_lt_top (μ := m)).ne (M := M.toReal ^ p⁻¹)
      (fun ε hε ↦ by
        obtain ⟨g, v, hgv, hv, hg⟩ := hnear b hb ε hε
        refine ⟨g, v, hgv, hv, ?_⟩
        have h := ENNReal.toReal_mono hM hg
        rw [ENNReal.coe_toReal] at h
        rw [E.rootSeminorm_apply]
        exact Real.rpow_le_rpow (NNReal.coe_nonneg _) h (inv_nonneg.mpr hp.le))
    refine ⟨f, hf, ?_⟩
    apply (ENNReal.toReal_le_toReal ENNReal.coe_ne_top hM).mp
    rw [ENNReal.coe_toReal, E.energy_eq_root_rpow]
    have h := Real.rpow_le_rpow (apply_nonneg _ _) hroot hp.le
    rwa [← Real.rpow_mul ENNReal.toReal_nonneg, inv_mul_cancel₀ hp.ne', Real.rpow_one] at h
  obtain ⟨f, hf, _⟩ := hRecover (L.toReal + 1) (lt_add_one _)
  refine ⟨f, ?_, ?_⟩
  · rw [hf]
    exact hULp
  · have hBound (ε : ℝ) (hε : 0 < ε) :
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
