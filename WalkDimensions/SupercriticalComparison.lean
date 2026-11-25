import WalkDimensions.BallPotential
import WalkDimensions.ConvolutionRecovery
import WalkDimensions.EnergyNondegeneracy

/-!
# Exponent comparison in the positive Morrey range

The sharp Hölder test and compact-function Besov recovery establish the
non-strict comparison in Theorem 2.5(1) when both walk exponents exceed
the volume exponent.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace WalkDimensions

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [Nonempty X] [ProperSpace X] [SecondCountableTopology X] {m : Measure X} [SFinite m]
  [IsFiniteMeasureOnCompacts m] [m.IsOpenPosMeasure]

namespace PEnergy

theorem not_tendsto_compact_besov_zero_of_poincare {p d β : ℝ}
    (E : PEnergy m p) (hvol : AhlforsRegular m d) (hβ : d < β)
    {Γ : E.domain → Measure X} (hΓ : ∀ f, Γ f univ = (E.energy f : ℝ≥0∞)) (hPI : E.Poincare Γ β)
    (hcap : E.CapacityUpperBound β) {u : X → ℝ} (hu : Continuous u)
    (hc : HasCompactSupport u) (hconst : ¬ ∃ c : ℝ, u =ᵐ[m] fun _ ↦ c) :
    ¬ Tendsto (besovEnergy m p β univ u) (𝓝[>] 0) (𝓝 0) := by
  intro hzero
  have hlim := hzero.liminf_eq
  obtain ⟨K, _, hrecover⟩ := E.exists_energy_of_compact_besov_liminf hvol hβ hΓ hPI hcap
  obtain ⟨f, hf, hE⟩ := hrecover hu hc (hlim ▸ ENNReal.zero_lt_top)
  simp only [hlim, mul_zero, nonpos_iff_eq_zero, ENNReal.coe_eq_zero] at hE
  have hEq := E.continuous_constant_of_energy_eq_zero hPI hΓ hE hu hf
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  exact hconst ⟨u x, Eventually.of_forall fun y ↦ hEq y x⟩

end PEnergy

theorem gamma_le_gamma_of_supercritical {d p q βp βq : ℝ}
    (hvol : AhlforsRegular m d) (hpq : p < q)
    (hβp : d < βp) (hβq : d < βq) (Ep : PEnergy m p) (Eq : PEnergy m q)
    {Γp : Ep.domain → Measure X} {Γq : Eq.domain → Measure X}
    (hΓp : ∀ f, Γp f univ = (Ep.energy f : ℝ≥0∞)) (hΓq : ∀ f, Γq f univ = (Eq.energy f : ℝ≥0∞))
    (hPIp : Ep.Poincare Γp βp) (hPIq : Eq.Poincare Γq βq)
    (hcapP : Ep.CapacityUpperBound βp) (hcapQ : Eq.CapacityUpperBound βq)
    (hunbounded : ¬ Bornology.IsBounded (univ : Set X)) :
    (βp - d) / (p - 1) ≤ (βq - d) / (q - 1) := by
  by_contra! h
  let b := (q - 1) * ((βp - d) / (p - 1)) + d
  have hq : 0 < q := zero_lt_one.trans Eq.one_lt
  have hqb : βq < b := by
    have h' := (div_lt_iff₀ (sub_pos.mpr Eq.one_lt)).mp h
    dsimp [b]
    linarith only [h', mul_comm ((βp - d) / (p - 1)) (q - 1)]
  have hb : 0 < b := hvol.1.trans (hβq.trans hqb)
  obtain ⟨u, hu, hc, hnc, htest⟩ :=
    Ep.exists_besov_interpolation_test hvol hβp hPIp hΓp hcapP hunbounded
  have hB := (htest q hpq b hb le_rfl).2
  have hscale : q * (b / q) = b := by rw [mul_comm, div_mul_cancel₀ _ hq.ne']
  rw [hscale] at hB
  let M := ⨆ r : Ioi (0 : ℝ), besovEnergy m q b univ u r
  have hbound : ∀ᶠ r in 𝓝[>] (0 : ℝ), besovEnergy m q b univ u r ≤ M :=
    eventually_mem_nhdsWithin.mono fun r hr ↦
      le_iSup (fun s : Ioi (0 : ℝ) ↦ besovEnergy m q b univ u s) ⟨r, hr⟩
  exact Eq.not_tendsto_compact_besov_zero_of_poincare hvol hβq hΓq hPIq hcapQ hu hc hnc
    (tendsto_besovEnergy_zero_of_higher_scale hqb hB.ne hbound)

end WalkDimensions
