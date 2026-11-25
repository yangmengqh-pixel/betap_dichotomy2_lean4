import WalkDimensions.ContinuousConnectivity
import WalkDimensions.TimedPathLimits
import Mathlib.Topology.Semicontinuity.Basic

/-!
# Increasing continuous approximations of bounded lower semicontinuous weights
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal NNReal

namespace WalkDimensions

variable {X : Type*} [MetricSpace X]

private noncomputable def weightRegularization (g : X → ℝ≥0∞) (n : ℕ) (x : X) : ℝ≥0∞ :=
  ⨅ y : X, g y + ENNReal.ofReal ((n : ℝ) * dist x y)

private theorem weightRegularization_le (g : X → ℝ≥0∞) (n : ℕ) (x : X) :
    weightRegularization g n x ≤ g x :=
  (iInf_le _ x).trans_eq (by simp)

theorem exists_monotone_continuous_weight_approx {g : X → ℝ≥0∞}
    (hg : LowerSemicontinuous g) {M : ℝ≥0∞} (hM : M ≠ ∞) (hgM : ∀ x, g x ≤ M) :
    ∃ w : ℕ → X → ℝ≥0∞, Monotone w ∧ (∀ n, Continuous (w n)) ∧
      (∀ n x, w n x ≤ g x) ∧ ∀ x, (⨆ n, w n x) = g x := by
  let w := weightRegularization g
  have hle (n : ℕ) (x : X) : w n x ≤ g x := weightRegularization_le g n x
  have hfinite (n : ℕ) (x : X) : w n x ≠ ∞ := ne_top_of_le_ne_top hM ((hle n x).trans (hgM x))
  refine ⟨w, ?_, ?_, hle, ?_⟩
  · intro n k h x
    apply iInf_mono
    intro z
    apply add_le_add_right
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by exact_mod_cast h) dist_nonneg)
  · intro n
    have hUpper (x y : X) : w n x ≤ w n y + ENNReal.ofReal ((n : ℝ) * dist x y) := by
      have : Nonempty X := ⟨x⟩
      change w n x ≤ (⨅ z, g z + ENNReal.ofReal ((n : ℝ) * dist y z)) + _
      rw [ENNReal.iInf_add]
      apply le_iInf
      intro z
      refine (iInf_le (fun z ↦ g z + ENNReal.ofReal ((n : ℝ) * dist x z)) z).trans ?_
      rw [add_assoc, ← ENNReal.ofReal_add (by positivity) (by positivity)]
      apply add_le_add_right
      apply ENNReal.ofReal_le_ofReal
      rw [← mul_add]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      rw [add_comm]
      exact dist_triangle _ _ _
    have hUpper' (x y : X) : (w n x).toReal ≤ (w n y).toReal + (n : ℝ) * dist x y := by
      have hh := ENNReal.toReal_mono
        (ENNReal.add_ne_top.mpr ⟨hfinite n y, ENNReal.ofReal_ne_top⟩) (hUpper x y)
      rwa [ENNReal.toReal_add (hfinite n y) ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (by positivity)] at hh
    have hLip : LipschitzWith (n : ℝ≥0) (fun x ↦ (w n x).toReal) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      rw [Real.dist_eq, abs_le]
      have hx := hUpper' x y
      have hy := hUpper' y x
      rw [dist_comm y x] at hy
      change -((n : ℝ) * dist x y) ≤ _ ∧ _ ≤ (n : ℝ) * dist x y
      constructor <;> linarith only [hx, hy]
    have hEq : w n = fun x ↦ ENNReal.ofReal ((w n x).toReal) :=
      funext fun x ↦ (ENNReal.ofReal_toReal (hfinite n x)).symm
    rw [hEq]
    exact ENNReal.continuous_ofReal.comp hLip.continuous
  · intro x
    apply le_antisymm (iSup_le fun n ↦ hle n x)
    by_contra! hh
    let a := ⨆ n, w n x
    obtain ⟨b, hab, hbg⟩ := exists_between hh
    have hbT : b ≠ ∞ := ne_top_of_lt hbg
    obtain ⟨δ, hδ, hnb⟩ := Metric.isOpen_iff.mp (hg.isOpen_preimage b) x hbg
    obtain ⟨n, hn⟩ := exists_nat_gt (b.toReal / δ)
    have hδn : b ≤ ENNReal.ofReal ((n : ℝ) * δ) := by
      rw [← ENNReal.ofReal_toReal hbT]
      apply ENNReal.ofReal_le_ofReal
      exact ((div_lt_iff₀ hδ).mp hn).le
    have hBn : b ≤ w n x := by
      apply le_iInf
      intro y
      by_cases hy : y ∈ ball x δ
      · exact (show b < g y from hnb hy).le.trans (le_add_right le_rfl)
      · have hy' : δ ≤ dist x y := by rw [dist_comm]; exact le_of_not_gt hy
        exact (hδn.trans (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_left hy' (Nat.cast_nonneg _)))).trans (le_add_left le_rfl)
    exact hab.not_ge (hBn.trans (le_iSup (fun k ↦ w k x) n))

variable [MeasurableSpace X] [BorelSpace X] [ProperSpace X] [SecondCountableTopology X]
  {m : Measure X} [m.Regular] [m.IsOpenPosMeasure] [SFinite m]

/-- Weighted connections with controlled duration and cost for bounded
lower semicontinuous weights. -/
def LowerSemicontinuousConnectivity (m : Measure X) (p C A : ℝ) : Prop :=
  ∀ (x y : X) (g : X → ℝ≥0∞), LowerSemicontinuous g → (∃ M ≠ ∞, ∀ z, g z ≤ M) →
    ∀ τ > (0 : ℝ),
      localMaximalAverage m (fun z ↦ g z ^ p) (A * dist x y) x ≤ ENNReal.ofReal (τ ^ p) →
      localMaximalAverage m (fun z ↦ g z ^ p) (A * dist x y) y ≤ ENNReal.ofReal (τ ^ p) →
      ∃ γ : TimedPath x y, γ.duration ≤ C * dist x y ∧
        γ.cost g ≤ ENNReal.ofReal (C * τ * dist x y)

theorem ContinuousConnectivity.lowerSemicontinuousConnectivity {p C A : ℝ} (hp : 0 ≤ p)
    (h : ContinuousConnectivity m p C A) : LowerSemicontinuousConnectivity m p C A := by
  intro x y g hg ⟨M, hM, hgM⟩ τ hτ hx hy
  obtain ⟨u, hMono, hu, hLe, hEq⟩ := exists_monotone_continuous_weight_approx hg hM hgM
  have hPath (n : ℕ) : ∃ γ : TimedPath x y, γ.duration ≤ C * dist x y ∧
      γ.cost (u n) ≤ ENNReal.ofReal (C * τ * dist x y) := by
    have hMax (z : X) := localMaximalAverage_mono (m := m)
      (R := A * dist x y) (S := A * dist x y)
      (show (fun v ↦ u n v ^ p) ≤ (fun v ↦ g v ^ p) from fun v ↦ ENNReal.rpow_le_rpow (hLe n v) hp)
      le_rfl z
    exact h x y (u n) (hu n) ⟨M, hM, fun v ↦ (hLe n v).trans (hgM v)⟩ τ hτ
      ((hMax x).trans hx) ((hMax y).trans hy)
  obtain ⟨γ, hγ, hCost⟩ := TimedPath.exists_cost_le_of_monotone_approx hMono hu hPath
  exact ⟨γ, hγ, by simpa only [hEq] using hCost⟩

end WalkDimensions
