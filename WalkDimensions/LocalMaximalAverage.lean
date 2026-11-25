import WalkDimensions.Doubling
import WalkDimensions.Besov

/-!
# Local uncentered maximal averages
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal

namespace WalkDimensions

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  {m : Measure X}

/-- Supremum of the normalized averages over balls containing the point. -/
noncomputable def localMaximalAverage (m : Measure X) (g : X → ℝ≥0∞) (R : ℝ) (x : X) : ℝ≥0∞ :=
  ⨆ (z : X) (s : ℝ) (_ : s ∈ Ioc (0 : ℝ) R) (_ : x ∈ ball z s),
    ∫⁻ y, g y ∂normalizedBall m z s

theorem average_le_localMaximalAverage (g : X → ℝ≥0∞) {R s : ℝ} {z x : X}
    (hs : 0 < s) (hsR : s ≤ R) (hx : x ∈ ball z s) :
    (∫⁻ y, g y ∂normalizedBall m z s) ≤ localMaximalAverage m g R x :=
  le_iSup_of_le z (le_iSup_of_le s (le_iSup_of_le ⟨hs, hsR⟩ (le_iSup (fun _ : x ∈ ball z s ↦ ∫⁻ y, g y ∂normalizedBall m z s) hx)))

theorem localMaximalAverage_mono {g h : X → ℝ≥0∞} {R S : ℝ} (hg : g ≤ h) (hR : R ≤ S) (x : X) :
    localMaximalAverage m g R x ≤ localMaximalAverage m h S x := by
  apply iSup_le
  intro z
  apply iSup_le
  intro s
  apply iSup_le
  intro hs
  apply iSup_le
  intro hx
  exact (lintegral_mono hg).trans (average_le_localMaximalAverage h hs.1 (hs.2.trans hR) hx)

theorem isOpen_localMaximalAverage_superlevel (g : X → ℝ≥0∞) (R : ℝ) (a : ℝ≥0∞) :
    IsOpen {x | a < localMaximalAverage m g R x} := by
  rw [Metric.isOpen_iff]
  intro x hx
  obtain ⟨z, s, hs, hxs, hg⟩ : ∃ (z : X) (s : ℝ), s ∈ Ioc (0 : ℝ) R ∧
      x ∈ ball z s ∧ a < ∫⁻ y, g y ∂normalizedBall m z s := by
    change a < localMaximalAverage m g R x at hx
    simpa only [localMaximalAverage, lt_iSup_iff, exists_prop] using hx
  obtain ⟨ε, hε, hIncl⟩ := Metric.isOpen_iff.mp isOpen_ball x hxs
  exact ⟨ε, hε, fun y hy ↦ hg.trans_le (average_le_localMaximalAverage g hs.1 hs.2 (hIncl hy))⟩

variable [BorelSpace X] [ProperSpace X] [IsFiniteMeasureOnCompacts m] [m.IsOpenPosMeasure]

theorem localMaximalAverage_le_const {g : X → ℝ≥0∞} {a : ℝ≥0∞}
    (hg : ∀ x, g x ≤ a) (R : ℝ) (x : X) : localMaximalAverage m g R x ≤ a := by
  apply iSup_le
  intro z
  apply iSup_le
  intro s
  apply iSup_le
  intro hs
  apply iSup_le
  intro _
  apply (lintegral_mono hg).trans_eq
  rw [lintegral_const, normalizedBall_univ z hs.1, mul_one]

theorem lintegral_ball_le_localMaximalAverage (g : X → ℝ≥0∞)
    {R s : ℝ} {z x : X} (hs : 0 < s) (hsR : s ≤ R) (hx : x ∈ ball z s) :
    (∫⁻ y in ball z s, g y ∂m) ≤ localMaximalAverage m g R x * m (ball z s) := by
  have h := average_le_localMaximalAverage (m := m) g hs hsR hx
  rw [normalizedBall, lintegral_smul_measure, smul_eq_mul, mul_comm] at h
  exact (ENNReal.div_le_iff (measure_ball_pos m z hs).ne' measure_ball_ne_top).mp h

end WalkDimensions
