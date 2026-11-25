import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Metric measure space hypotheses

The standing geometry and volume conditions of Section 2 of
Meng Yang, *On the dichotomy of p-walk dimensions on metric measure spaces II*,
arXiv:2611.02422v1.
-/

open Metric MeasureTheory Set
open scoped ENNReal

namespace WalkDimensions

variable {X : Type*} [MetricSpace X]

/-- The chain condition (CC), with a uniform bound on each link. -/
def ChainCondition (X : Type*) [MetricSpace X] : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (x y : X) (n : ℕ), 1 ≤ n →
    ∃ z : ℕ → X, z 0 = x ∧ z n = y ∧
      ∀ k < n, dist (z (k + 1)) (z k) ≤ C * dist x y / n

/-- The standing metric hypotheses in Section 2. Properness gives the stated
relative compactness of balls, as well as completeness and local compactness. -/
structure MetricHypotheses (X : Type*) [MetricSpace X] : Prop where
  proper : ProperSpace X
  separable : TopologicalSpace.SeparableSpace X
  unbounded : ¬ Bornology.IsBounded (univ : Set X)
  chain : ChainCondition X

variable [MeasurableSpace X]

/-- The reference measure is Radon and has full support. -/
structure MeasureHypotheses (m : Measure X) : Prop where
  regular : m.Regular
  fullSupport : m.IsOpenPosMeasure

/-- Volume doubling (VD). -/
def VolumeDoubling (m : Measure X) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (x : X) (r : ℝ), 0 < r →
    m (ball x (2 * r)) ≤ ENNReal.ofReal C * m (ball x r)

/-- Ahlfors regularity V(d), on all positive radii. -/
def AhlforsRegular (m : Measure X) (d : ℝ) : Prop :=
  0 < d ∧ ∃ C : ℝ, 0 < C ∧ ∀ (x : X) (r : ℝ), 0 < r →
    ENNReal.ofReal (r ^ d / C) ≤ m (ball x r) ∧
      m (ball x r) ≤ ENNReal.ofReal (C * r ^ d)

theorem AhlforsRegular.volumeDoubling {m : Measure X} {d : ℝ}
    (h : AhlforsRegular m d) : VolumeDoubling m := by
  obtain ⟨_, C, hC, hvolume⟩ := h
  refine ⟨C * C * (2 : ℝ) ^ d, by positivity, fun x r hr ↦ ?_⟩
  calc
    m (ball x (2 * r)) ≤ ENNReal.ofReal (C * (2 * r) ^ d) :=
      (hvolume x (2 * r) (by positivity)).2
    _ = ENNReal.ofReal (C * C * (2 : ℝ) ^ d) * ENNReal.ofReal (r ^ d / C) := by
      rw [← ENNReal.ofReal_mul (by positivity), Real.mul_rpow (by norm_num) hr.le]
      congr 1
      field_simp
    _ ≤ ENNReal.ofReal (C * C * (2 : ℝ) ^ d) * m (ball x r) :=
      mul_le_mul_of_nonneg_left (hvolume x r hr).1 bot_le

end WalkDimensions
