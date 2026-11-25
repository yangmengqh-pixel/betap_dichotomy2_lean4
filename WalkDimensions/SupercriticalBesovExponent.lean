import WalkDimensions.CompactBesovTest
import WalkDimensions.EnergyTestFunctions
import WalkDimensions.SupercriticalComparison

/-!
# The critical Besov exponent in the positive Morrey range
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [Nonempty X] [ProperSpace X] [SecondCountableTopology X] {m : Measure X}
  [SFinite m] [IsFiniteMeasureOnCompacts m] [m.IsOpenPosMeasure]

theorem criticalBesovExponent_eq_of_supercritical {d p β : ℝ}
    (E : PEnergy m p) (hvol : AhlforsRegular m d) (hβ : d < β)
    {Γ : E.domain → Measure X} (hΓ : ∀ f, Γ f univ = (E.energy f : ℝ≥0∞))
    (hPI : E.Poincare Γ β) (hcap : E.CapacityUpperBound β)
    (hunbounded : ¬ Bornology.IsBounded (univ : Set X)) :
    criticalBesovExponent m p = ENNReal.ofReal (β / p) := by
  have hp := zero_lt_one.trans E.one_lt
  have hβ' := hvol.1.trans hβ
  apply le_antisymm _ (E.scale_le_criticalBesovExponent hunbounded hβ' hvol.volumeDoubling hPI hΓ)
  refine iSup_le fun α ↦ iSup_le fun ⟨u, hu, hnc⟩ ↦ ?_
  apply ENNReal.ofReal_le_ofReal
  by_contra! h
  have hscale : β < p * (α : ℝ) := by
    simpa only [mul_comm] using (div_lt_iff₀ hp).mp h
  obtain ⟨v, hv, hc, hB, hvnc⟩ :=
    exists_compact_besov_test_of_supercritical E.one_lt.le hvol (hβ.trans hscale) hu hnc
  let M := ⨆ r : Ioi (0 : ℝ), besovEnergy m p (p * (α : ℝ)) univ v r
  have hbound : ∀ᶠ r in 𝓝[>] (0 : ℝ), besovEnergy m p (p * (α : ℝ)) univ v r ≤ M :=
    eventually_mem_nhdsWithin.mono fun r hr ↦
      le_iSup (fun s : Ioi (0 : ℝ) ↦ besovEnergy m p (p * (α : ℝ)) univ v s) ⟨r, hr⟩
  exact E.not_tendsto_compact_besov_zero_of_poincare hvol hβ hΓ hPI hcap hv hc hvnc
    (tendsto_besovEnergy_zero_of_higher_scale hscale hB.2.ne hbound)

end WalkDimensions.PEnergy
