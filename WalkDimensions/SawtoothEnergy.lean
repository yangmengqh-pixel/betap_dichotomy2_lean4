import WalkDimensions.EnergyFold
import WalkDimensions.OscillatoryTruncation

/-!
# Energy of the sawtooth

A grid wider than the range of the function gives its absolute value.
Each halving of the grid reflects one half of every tooth and preserves
energy.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {m : Measure X} [IsFiniteMeasureOnCompacts m] {p : ℝ} (E : PEnergy m p)

theorem exists_sawtooth_energy_eq (f : E.domain) {u : X → ℝ}
    (hfu : (f : RealLp m p) =ᵐ[m] u) (hu : Continuous u) (hc : HasCompactSupport u)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ g : E.domain, (g : RealLp m p) =ᵐ[m] sawtooth δ ∘ u ∧ E.energy g = E.energy f := by
  obtain ⟨B, hB⟩ := (hc.isCompact.image (continuous_abs.comp hu)).bddAbove
  let M := max B 0
  have hM (x : X) : |u x| ≤ M := by
    by_cases hx : x ∈ tsupport u
    · exact (hB (mem_image_of_mem _ hx)).trans (le_max_left _ _)
    · have h : u x = 0 := notMem_support.mp (fun h ↦ hx (subset_closure h))
      rw [h, abs_zero]
      exact le_max_right _ _
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (M / δ) (show (1 : ℝ) < 2 by norm_num)
  have hrange (x : X) : |u x| ≤ δ * (2 : ℝ) ^ N :=
    (hM x).trans (((div_lt_iff₀ hδ).mp hN).le.trans_eq (mul_comm _ _))
  have hW (n : ℕ) : Continuous (sawtooth (δ * (2 : ℝ) ^ n) ∘ u) :=
    (lipschitzWith_sawtooth _).continuous.comp hu
  have hC (n : ℕ) : HasCompactSupport (sawtooth (δ * (2 : ℝ) ^ n) ∘ u) :=
    hc.comp_left (sawtooth_zero _)
  have hstep (n : ℕ) :
      (∃ g : E.domain, (g : RealLp m p) =ᵐ[m] sawtooth (δ * (2 : ℝ) ^ (n + 1)) ∘ u ∧
        E.energy g = E.energy f) →
      ∃ g : E.domain, (g : RealLp m p) =ᵐ[m] sawtooth (δ * (2 : ℝ) ^ n) ∘ u ∧
        E.energy g = E.energy f := by
    rintro ⟨g, hg, hEg⟩
    let s := δ * (2 : ℝ) ^ (n + 1)
    have hs : 0 < s := by dsimp [s]; positivity
    have hHalf : s / 2 = δ * (2 : ℝ) ^ n := by
      dsimp [s]
      rw [pow_succ]
      ring
    obtain ⟨h, hh, hEh⟩ := E.exists_fold_energy_eq g hg (hW (n + 1)) (hC (n + 1)) hs.le
    refine ⟨h, ?_, hEh.trans hEg⟩
    have he (x : X) :
        sawtooth (δ * (2 : ℝ) ^ n) (u x) = min (sawtooth s (u x)) (s - sawtooth s (u x)) := by
      rw [← hHalf, sawtooth_half s hs]
    exact hh.mono fun x hx ↦ hx.trans (he x).symm
  have hstart : ∃ g : E.domain, (g : RealLp m p) =ᵐ[m] sawtooth (δ * (2 : ℝ) ^ N) ∘ u ∧
      E.energy g = E.energy f := by
    obtain ⟨g, hg, hE⟩ := E.exists_abs_energy_eq f hfu hu hc
    exact ⟨g, hg.mono (fun x hx ↦ hx.trans (sawtooth_eq_abs_of_abs_le (by positivity) (hrange x)).symm), hE⟩
  have hfinish (n : ℕ) :
      (∃ g : E.domain, (g : RealLp m p) =ᵐ[m] sawtooth (δ * (2 : ℝ) ^ n) ∘ u ∧
        E.energy g = E.energy f) →
      ∃ g : E.domain, (g : RealLp m p) =ᵐ[m] sawtooth δ ∘ u ∧ E.energy g = E.energy f := by
    induction n with
    | zero => intro h; simpa only [pow_zero, mul_one] using h
    | succ n ih => exact fun h ↦ ih (hstep n h)
  exact hfinish N hstart

end WalkDimensions.PEnergy
