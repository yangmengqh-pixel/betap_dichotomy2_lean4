import WalkDimensions.BesovExponentAntitone
import WalkDimensions.BesovRecovery
import WalkDimensions.EnergyNondegeneracy
import WalkDimensions.CriticalBesov
import WalkDimensions.EnergyTestFunctions
import WalkDimensions.Interpolation

/-!
# Identification and basic comparisons of walk exponents
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [Nonempty X] [ProperSpace X] [SecondCountableTopology X] {m : Measure X}
  [SFinite m] [m.Regular] [m.IsOpenPosMeasure]

theorem not_tendsto_besov_zero {p β : ℝ} (E : PEnergy m p) (hβ : 0 < β)
    (hvol : VolumeDoubling m) {Γ : E.domain → Measure X} (hPI : E.Poincare Γ β)
    (hΓ : ∀ f, Γ f univ = (E.energy f : ℝ≥0∞)) (hcap : E.CapacityUpperBound β)
    {u : X → ℝ} (hu : MemLp u (ENNReal.ofReal p) m)
    (hnc : ¬ ∃ c : ℝ, u =ᵐ[m] fun _ ↦ c) :
    ¬ Tendsto (besovEnergy m p β univ u) (𝓝[>] 0) (𝓝 0) := by
  intro h
  obtain ⟨K, _, hrecover⟩ := E.exists_energy_of_besov_liminf hβ hvol hcap
  obtain ⟨f, hf, hE⟩ := hrecover hu (h.liminf_eq ▸ ENNReal.zero_lt_top)
  simp only [h.liminf_eq, mul_zero, nonpos_iff_eq_zero, ENNReal.coe_eq_zero] at hE
  obtain ⟨c, hc⟩ := E.ae_constant_of_energy_eq_zero hPI hΓ hE
  exact hnc ⟨c, hf.symm.trans hc⟩

theorem criticalBesovExponent_eq_walkExponent_div {p β : ℝ}
    (E : PEnergy m p) (hvol : VolumeDoubling m) (hβ : 0 < β)
    {Γ : E.domain → Measure X} (hΓ : ∀ f, Γ f univ = (E.energy f : ℝ≥0∞))
    (hPI : E.Poincare Γ β) (hcap : E.CapacityUpperBound β)
    (hunbounded : ¬ Bornology.IsBounded (univ : Set X)) :
    criticalBesovExponent m p = ENNReal.ofReal (β / p) := by
  have hp := zero_lt_one.trans E.one_lt
  apply le_antisymm _ (E.scale_le_criticalBesovExponent hunbounded hβ hvol hPI hΓ)
  refine iSup_le fun α ↦ iSup_le fun ⟨u, hu, hnc⟩ ↦ ?_
  apply ENNReal.ofReal_le_ofReal
  by_contra! h
  have hscale : β < p * (α : ℝ) := by
    simpa only [mul_comm] using (div_lt_iff₀ hp).mp h
  have hbound : ∀ᶠ r in 𝓝[>] (0 : ℝ), besovEnergy m p (p * (α : ℝ)) univ u r ≤
      ⨆ s : Ioi (0 : ℝ), besovEnergy m p (p * (α : ℝ)) univ u s :=
    eventually_mem_nhdsWithin.mono fun r hr ↦ le_iSup
      (fun s : Ioi (0 : ℝ) ↦ besovEnergy m p (p * (α : ℝ)) univ u s) ⟨r, hr⟩
  exact E.not_tendsto_besov_zero hβ hvol hPI hΓ hcap hu.1 hnc
    (tendsto_besovEnergy_zero_of_higher_scale hscale hu.2.ne hbound)

theorem exponent_le_walkExponent {p β : ℝ}
    (E : PEnergy m p) (hvol : VolumeDoubling m) (hβ : 0 < β)
    {Γ : E.domain → Measure X} (hΓ : ∀ f, Γ f univ = (E.energy f : ℝ≥0∞))
    (hPI : E.Poincare Γ β) (hcap : E.CapacityUpperBound β)
    (hunbounded : ¬ Bornology.IsBounded (univ : Set X)) : p ≤ β := by
  have hp := zero_lt_one.trans E.one_lt
  have h := one_le_criticalBesovExponent hp hvol hunbounded
  rw [E.criticalBesovExponent_eq_walkExponent_div hvol hβ hΓ hPI hcap hunbounded,
    ← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff (div_nonneg hβ.le hp.le)] at h
  simpa only [one_mul] using (le_div_iff₀ hp).mp h

theorem walkExponent_comparisons {p q βp βq : ℝ}
    (Ep : PEnergy m p) (Eq : PEnergy m q) (hpq : p < q)
    (hvol : VolumeDoubling m) (hβp : 0 < βp) (hβq : 0 < βq)
    {Γp : Ep.domain → Measure X} {Γq : Eq.domain → Measure X}
    (hΓp : ∀ f, Γp f univ = (Ep.energy f : ℝ≥0∞))
    (hΓq : ∀ f, Γq f univ = (Eq.energy f : ℝ≥0∞))
    (hPIp : Ep.Poincare Γp βp) (hPIq : Eq.Poincare Γq βq)
    (hcapP : Ep.CapacityUpperBound βp) (hcapQ : Eq.CapacityUpperBound βq)
    (hunbounded : ¬ Bornology.IsBounded (univ : Set X)) :
    βp < βq ∧ βq / q ≤ βp / p := by
  have hp := zero_lt_one.trans Ep.one_lt
  have hq := hp.trans hpq
  have hP := Ep.criticalBesovExponent_eq_walkExponent_div hvol hβp hΓp hPIp hcapP hunbounded
  have hQ := Eq.criticalBesovExponent_eq_walkExponent_div hvol hβq hΓq hPIq hcapQ hunbounded
  have hmono := criticalBesovExponent_mul_mono (m := m) hp hpq.le
  rw [hP, hQ, ← ENNReal.ofReal_mul hp.le, ← ENNReal.ofReal_mul hq.le,
    mul_div_cancel₀ _ hp.ne', mul_div_cancel₀ _ hq.ne',
    ENNReal.ofReal_le_ofReal_iff hβq.le] at hmono
  have hanti := criticalBesovExponent_antitone (m := m) hvol hp hpq.le
  rw [hP, hQ, ENNReal.ofReal_le_ofReal_iff (div_nonneg hβp.le hp.le)] at hanti
  refine ⟨hmono.lt_of_ne ?_, hanti⟩
  intro heq
  obtain ⟨f, u, hu, hc, hfu, hnc⟩ := Ep.exists_continuous_compact_nonconstant hunbounded
  obtain ⟨K, _, hK, hbound⟩ := Ep.global_besov_bound hvol hPIp hΓp
  have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), besovEnergy m p βp univ u r ≤
      K * (Ep.energy f : ℝ≥0∞) := by
    refine eventually_mem_nhdsWithin.mono fun r hr ↦ ?_
    rw [← besovEnergy_congr_ae hfu]
    exact (le_iSup (fun s : Ioi (0 : ℝ) ↦ besovEnergy m p βp univ (f : RealLp m p) s)
      ⟨r, hr⟩).trans (hbound f)
  apply Eq.not_tendsto_besov_zero hβq hvol hPIq hΓq hcapQ
    (hu.memLp_of_hasCompactSupport hc) hnc
  rw [← heq]
  exact tendsto_besovEnergy_zero_of_bounded_same_scale hp.le hpq hu hc
    (ENNReal.mul_ne_top hK ENNReal.coe_ne_top) hsmall

end WalkDimensions.PEnergy
