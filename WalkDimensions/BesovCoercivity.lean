import WalkDimensions.EnergyNondegeneracy
import WalkDimensions.Interpolation
import WalkDimensions.SingularComparison
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Contradictions from vanishing Besov energy

The last step of Section 4 and the strict comparison in Lemma 5.1
of arXiv:2611.02422v1. The displayed domain and energy estimates are
the two parts of the Besov characterization in Lemma 3.4.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X} [IsFiniteMeasureOnCompacts m] [m.IsOpenPosMeasure]

/-- Under the domain characterization and the lower energy bound, a
nonconstant continuous compactly supported test function cannot have
vanishing Besov energy. -/
theorem not_tendsto_besovEnergy_zero {p β : ℝ} (E : PEnergy m p)
    {Γ : E.domain → Measure X} (hPI : E.Poincare Γ β)
    (hΓ : ∀ f, Γ f univ = (E.energy f : ℝ≥0∞))
    {u : X → ℝ} (hu : Continuous u) (hc : HasCompactSupport u)
    (hnonconst : ∃ x y, u x ≠ u y)
    (hdom : liminf (besovEnergy m p β univ u) (𝓝[>] 0) < ∞ →
      continuousLp (m := m) p u hu hc ∈ E.domain)
    {C : ℝ≥0∞} (hC : C ≠ 0)
    (hlower : ∀ (hm : continuousLp (m := m) p u hu hc ∈ E.domain),
      C * (E.energy ⟨continuousLp (m := m) p u hu hc, hm⟩ : ℝ≥0∞) ≤
        liminf (besovEnergy m p β univ u) (𝓝[>] 0)) :
    ¬ Tendsto (besovEnergy m p β univ u) (𝓝[>] 0) (𝓝 0) := by
  intro h
  have hlim := h.liminf_eq
  have hm := hdom (hlim ▸ ENNReal.zero_lt_top)
  let f : E.domain := ⟨continuousLp (m := m) p u hu hc, hm⟩
  have hz : E.energy f = 0 := by
    have hl := hlower hm
    rw [hlim, nonpos_iff_eq_zero, mul_eq_zero] at hl
    exact ENNReal.coe_eq_zero.mp (hl.resolve_left hC)
  obtain ⟨x, y, hxy⟩ := hnonconst
  exact hxy (E.continuous_constant_of_energy_eq_zero hPI hΓ hz hu
    (continuousLp_ae_eq u hu hc) x y)

end WalkDimensions.PEnergy
