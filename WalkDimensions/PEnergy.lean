import WalkDimensions.Geometry
import Mathlib.Analysis.Normed.Module.Seminorm.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.Average

/-!
# The p-energy, Poincaré inequality, and capacity bound

Definitions from Section 2 of arXiv:2611.02422v1.
-/

open Filter MeasureTheory Metric Set
open scoped ENNReal NNReal

namespace WalkDimensions

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The real (L^p) carrier of the energy domain. -/
abbrev RealLp (m : Measure X) (p : ℝ) := Lp ℝ (ENNReal.ofReal p) m

/-- The compactly supported continuous representatives used in regularity. -/
noncomputable def continuousLp {m : Measure X} [IsFiniteMeasureOnCompacts m] (p : ℝ)
    (u : X → ℝ) (hu : Continuous u) (hc : HasCompactSupport u) : RealLp m p :=
  (hu.memLp_of_hasCompactSupport hc).toLp u

/-- The graph norm of a (p)-energy. -/
noncomputable def energyGraphNorm {m : Measure X} {p : ℝ} {F : Submodule ℝ (RealLp m p)}
    (E : F → ℝ≥0) (f : F) : ℝ :=
  ((E f : ℝ) + ‖(f : RealLp m p)‖ ^ p) ^ p⁻¹

/-- A (p)-energy with the algebra condition (Alg).
The seminorm witnesses specify precisely the two norm formulas in the source. -/
structure PEnergy (m : Measure X) [IsFiniteMeasureOnCompacts m] (p : ℝ) where
  one_lt : 1 < p
  domain : Submodule ℝ (RealLp m p)
  dense :
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr one_lt.le⟩
    Dense (domain : Set (RealLp m p))
  energy : domain → ℝ≥0
  rootSeminorm : Seminorm ℝ domain
  rootSeminorm_apply : ∀ f, rootSeminorm f = (energy f : ℝ) ^ p⁻¹
  graphSeminorm : Seminorm ℝ domain
  graphSeminorm_apply : ∀ f, graphSeminorm f = energyGraphNorm energy f
  graph_complete :
    letI := graphSeminorm.toAddGroupSeminorm.toSeminormedAddCommGroup
    CompleteSpace domain
  markov : ∀ (φ : ℝ → ℝ), LipschitzWith 1 φ → φ 0 = 0 → ∀ f : domain,
    ∃ g : domain, (g : RealLp m p) =ᵐ[m] (fun x ↦ φ ((f : RealLp m p) x)) ∧
      energy g ≤ energy f
  regular_uniform : ∀ (u : X → ℝ), Continuous u → HasCompactSupport u →
    ∀ ε > (0 : ℝ), ∃ (v : X → ℝ) (hv : Continuous v) (hc : HasCompactSupport v),
      continuousLp (m := m) p v hv hc ∈ domain ∧
      ∃ δ < ε, ∀ x, |v x - u x| ≤ δ
  regular_graph : ∀ (f : domain) (ε : ℝ), 0 < ε →
    ∃ (u : X → ℝ) (hu : Continuous u) (hc : HasCompactSupport u)
      (hm : continuousLp (m := m) p u hu hc ∈ domain),
        graphSeminorm (⟨continuousLp (m := m) p u hu hc, hm⟩ - f) < ε
  stronglyLocal : ∀ (f g : domain) (u v : X → ℝ),
    (f : RealLp m p) =ᵐ[m] u → (g : RealLp m p) =ᵐ[m] v →
    HasCompactSupport u → HasCompactSupport v →
    (∃ U : Set X, IsOpen U ∧ tsupport u ⊆ U ∧ ∃ c : ℝ, EqOn v (fun _ ↦ c) U) →
    energy (f + g) = energy f + energy g
  clarkson_le_two : p ≤ 2 → ∀ f g : domain,
    2 * ((energy f : ℝ) ^ (p - 1)⁻¹ + (energy g : ℝ) ^ (p - 1)⁻¹) ^ (p - 1) ≤
      (energy (f + g) : ℝ) + (energy (f - g) : ℝ)
  clarkson_two_le : 2 ≤ p → ∀ f g : domain,
    (energy (f + g) : ℝ) + (energy (f - g) : ℝ) ≤
      2 * ((energy f : ℝ) ^ (p - 1)⁻¹ + (energy g : ℝ) ^ (p - 1)⁻¹) ^ (p - 1)
  algebra : ∀ f g : domain,
    eLpNorm (f : RealLp m p) ∞ m < ∞ → eLpNorm (g : RealLp m p) ∞ m < ∞ →
    ∃ h : domain,
      (h : RealLp m p) =ᵐ[m] (fun x ↦ (f : RealLp m p) x * (g : RealLp m p) x) ∧
      rootSeminorm h ≤ (eLpNorm (f : RealLp m p) ∞ m).toReal * rootSeminorm g +
        (eLpNorm (g : RealLp m p) ∞ m).toReal * rootSeminorm f

namespace PEnergy

variable {m : Measure X} [IsFiniteMeasureOnCompacts m] {p : ℝ} (E : PEnergy m p)

/-- Admissibility for the condenser capacity. The representative has the
required constant values throughout open neighbourhoods of the two plates. -/
def CapacityAdmissible (A₁ A₂ : Set X) (f : E.domain) : Prop :=
  ∃ u : X → ℝ, (f : RealLp m p) =ᵐ[m] u ∧ ∃ U₁ U₂ : Set X,
    IsOpen U₁ ∧ IsOpen U₂ ∧ A₁ ⊆ U₁ ∧ A₂ ⊆ U₂ ∧
    EqOn u (fun _ ↦ 1) U₁ ∧ EqOn u (fun _ ↦ 0) U₂

/-- The infimum of admissible energies, with value infinity for an empty class. -/
noncomputable def capacity (A₁ A₂ : Set X) : ℝ≥0∞ :=
  ⨅ f : E.domain, ⨅ (_ : E.CapacityAdmissible A₁ A₂ f), (E.energy f : ℝ≥0∞)

/-- A strict upper bound on capacity gives an admissible representative
whose energy obeys the same strict bound. -/
theorem exists_admissible_lt_of_capacity_lt {A₁ A₂ : Set X} {b : ℝ≥0∞}
    (h : E.capacity A₁ A₂ < b) :
    ∃ f : E.domain, E.CapacityAdmissible A₁ A₂ f ∧ (E.energy f : ℝ≥0∞) < b := by
  rw [capacity, iInf_lt_iff] at h
  obtain ⟨f, hf⟩ := h
  obtain ⟨hadm, hlt⟩ := iInf_lt_iff.mp hf
  exact ⟨f, hadm, hlt⟩

/-- The capacity upper bound from Section 2. -/
def CapacityUpperBound (β : ℝ) : Prop :=
  ∃ C A : ℝ, 0 < C ∧ 1 < A ∧ ∀ (x : X) (r : ℝ), 0 < r →
    E.capacity (ball x r) (ball x (A * r))ᶜ ≤
      ENNReal.ofReal (C * r ^ (-β)) * m (ball x r)

/-- The ball Poincaré inequality relative to a given energy measure.
The construction of the canonical measure is a separate assertion. -/
def Poincare (Γ : E.domain → Measure X) (β : ℝ) : Prop :=
  ∃ C A : ℝ, 0 < C ∧ 1 ≤ A ∧ ∀ (x : X) (r : ℝ), 0 < r → ∀ f : E.domain,
    (∫⁻ y in ball x r, ENNReal.ofReal
      |(f : RealLp m p) y - ⨍ z in ball x r, (f : RealLp m p) z ∂m| ^ p ∂m) ≤
      ENNReal.ofReal (C * r ^ β) * Γ f (ball x (A * r))

end PEnergy

end WalkDimensions
