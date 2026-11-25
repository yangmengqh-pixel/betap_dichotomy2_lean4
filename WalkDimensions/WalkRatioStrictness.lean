import WalkDimensions.EnergyMeasureConstruction
import WalkDimensions.SingularComparison
import WalkDimensions.WalkExponent

/-!
# Strict ratio comparison from a singular energy measure

This is the local Besov comparison in Section 4 after the singularity
input for a nonconstant higher-exponent test function.
-/

open MeasureTheory Set
open scoped ENNReal

namespace WalkDimensions

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [Nonempty X] [ProperSpace X] [SecondCountableTopology X] {m : Measure X}
  [SFinite m] [m.Regular] [m.IsOpenPosMeasure]

theorem walkExponent_ratio_lt_of_singular_domain {p q βp βq : ℝ}
    (Ep : PEnergy m p) (Eq : PEnergy m q) (hpq : p < q)
    (hvol : VolumeDoubling m) (hβp : 0 < βp) (hβq : 0 < βq)
    (hPIp : Ep.Poincare Ep.energyMeasure βp) (hPIq : Eq.Poincare Eq.energyMeasure βq)
    (hcapP : Ep.CapacityUpperBound βp) (hcapQ : Eq.CapacityUpperBound βq)
    (hunbounded : ¬ Bornology.IsBounded (univ : Set X))
    (f : Eq.domain) {u : X → ℝ} (hfu : (f : RealLp m q) =ᵐ[m] u)
    (hu : Measurable u) (huc : HasCompactSupport u) (huLp : MemLp u (ENNReal.ofReal p) m)
    (hnc : ¬ ∃ c : ℝ, u =ᵐ[m] fun _ ↦ c)
    (hsing : (Eq.energyMeasure f).MutuallySingular m) : βq / q < βp / p := by
  have hanti := (Ep.walkExponent_comparisons Eq hpq hvol hβp hβq Ep.energyMeasure_univ
    Eq.energyMeasure_univ hPIp hPIq hcapP hcapQ hunbounded).2
  apply hanti.lt_of_ne
  intro hEq
  obtain ⟨_, A, C, _, hA, _, hC, _, hbound⟩ :=
    Eq.local_besov_bound hvol hPIq Eq.energyMeasure_univ
  have hdom (U : Set X) (_ : IsOpen U) (r : ℝ) (hr : 0 < r) :
      besovEnergy m q βq U u r ≤ C * Eq.energyMeasure f
        (Metric.thickening ((2 * A) * r) U) := by
    rw [← besovEnergy_congr_ae hfu]
    exact hbound U f r hr
  have hzero := tendsto_besovEnergy_zero_of_singular (zero_lt_one.trans Ep.one_lt) hpq
    (mul_pos (by norm_num) (zero_lt_one.trans_le hA)) hEq.symm hu
    huc hsing.symm hC hdom
  exact Ep.not_tendsto_besov_zero hβp hvol hPIp Ep.energyMeasure_univ hcapP
    huLp hnc hzero

theorem walkExponent_ratio_lt_of_singular_core {p q βp βq : ℝ}
    (Ep : PEnergy m p) (Eq : PEnergy m q) (hpq : p < q)
    (hvol : VolumeDoubling m) (hβp : 0 < βp) (hβq : 0 < βq)
    (hPIp : Ep.Poincare Ep.energyMeasure βp) (hPIq : Eq.Poincare Eq.energyMeasure βq)
    (hcapP : Ep.CapacityUpperBound βp) (hcapQ : Eq.CapacityUpperBound βq)
    (hunbounded : ¬ Bornology.IsBounded (univ : Set X))
    (u : Eq.CompactCore) (hnc : ¬ ∃ c : ℝ, u.toFun =ᵐ[m] fun _ ↦ c)
    (hsing : (Eq.energyMeasure u.domainElement).MutuallySingular m) : βq / q < βp / p := by
  exact walkExponent_ratio_lt_of_singular_domain Ep Eq hpq hvol hβp hβq hPIp hPIq hcapP hcapQ
    hunbounded u.domainElement u.ae_eq u.continuous.measurable u.compactSupport
    (u.continuous.memLp_of_hasCompactSupport u.compactSupport) hnc hsing

end WalkDimensions
