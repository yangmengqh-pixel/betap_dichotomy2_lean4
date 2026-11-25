import WalkDimensions.EnergyClosedness

/-!
# Energy sublevels and uniform approximation on a fixed set

The ambient (L^p) norm controls uniform errors supported on a set of
finite reference measure. This allows the closedness theorem to be
used with scalar truncations.
-/

open Filter MeasureTheory Set
open scoped ENNReal

namespace WalkDimensions

variable {X : Type*} [MeasurableSpace X] {m : Measure X} {p : ℝ}

/-- A pointwise bound on a finite-measure set gives the corresponding
ambient (L^p) norm bound. -/
theorem norm_realLp_le_of_ae_abs_bound (hp : 0 < p) (f : RealLp m p)
    {S : Set X} (hS : MeasurableSet S) (hSfin : m S ≠ ∞) {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ᵐ x ∂m, |f x| ≤ S.indicator (fun _ ↦ b) x) :
    ‖f‖ ≤ b * (m.real S) ^ p⁻¹ := by
  have hnorm : eLpNorm f (ENNReal.ofReal p) m ≤
      eLpNorm (S.indicator (fun _ ↦ b)) (ENNReal.ofReal p) m := by
    apply eLpNorm_mono_ae_real (Lp.aestronglyMeasurable f)
    simpa only [Real.norm_eq_abs] using h
  rw [eLpNorm_indicator_const hS.nullMeasurableSet
    (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top,
    Real.eNorm_eq_ofReal_abs, abs_of_nonneg hb, ENNReal.toReal_ofReal hp.le, one_div] at hnorm
  have hfin : ENNReal.ofReal b * (m S) ^ p⁻¹ ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.mpr hp.le) hSfin)
  simpa only [Lp.norm_def, ENNReal.toReal_mul, ENNReal.toReal_ofReal hb, ENNReal.toReal_rpow,
    measureReal_def] using ENNReal.toReal_mono hfin hnorm

namespace PEnergy

variable [MetricSpace X] [BorelSpace X] [IsFiniteMeasureOnCompacts m] (E : PEnergy m p)

theorem exists_of_uniform_approximation (f : RealLp m p) (u : X → ℝ)
    (hfu : f =ᵐ[m] u) {S : Set X} (hS : MeasurableSet S) (hSfin : m S ≠ ∞)
    {M : ℝ}
    (happrox : ∀ ε > (0 : ℝ), ∃ (g : E.domain) (v : X → ℝ),
      (g : RealLp m p) =ᵐ[m] v ∧ (∀ x, |v x - u x| ≤ S.indicator (fun _ ↦ ε) x) ∧
      E.rootSeminorm g ≤ M) :
    ∃ g : E.domain, (g : RealLp m p) = f ∧ E.rootSeminorm g ≤ M := by
  have hp : 0 < p := zero_lt_one.trans E.one_lt
  let D := (m.real S) ^ p⁻¹
  have hD : 0 ≤ D := by dsimp [D]; positivity
  exact E.exists_of_bounded_lp_approximation f (M := M)
    (fun ε hε ↦ by
      let δ := ε / (D + 1)
      have hδ : 0 < δ := div_pos hε (by positivity)
      obtain ⟨g, v, hgv, hv, hMg⟩ := happrox δ hδ
      refine ⟨g, ?_, hMg⟩
      have hbound : ∀ᵐ x ∂m, |((g : RealLp m p) - (f : RealLp m p)) x| ≤
          S.indicator (fun _ ↦ δ) x := by
        filter_upwards [Lp.coeFn_sub (g : RealLp m p) (f : RealLp m p), hgv, hfu] with x hx hgx hfx
        rw [hx, Pi.sub_apply, hgx, hfx]
        exact hv x
      apply (norm_realLp_le_of_ae_abs_bound hp _ hS hSfin hδ.le hbound).trans_lt
      change δ * D < ε
      have he : δ * (D + 1) = ε := div_mul_cancel₀ _ (by positivity)
      linarith)

theorem rootSeminorm_le_of_uniform_approximation (f : E.domain) (u : X → ℝ)
    (hfu : (f : RealLp m p) =ᵐ[m] u) {S : Set X} (hS : MeasurableSet S) (hSfin : m S ≠ ∞)
    {M : ℝ}
    (happrox : ∀ ε > (0 : ℝ), ∃ (g : E.domain) (v : X → ℝ),
      (g : RealLp m p) =ᵐ[m] v ∧ (∀ x, |v x - u x| ≤ S.indicator (fun _ ↦ ε) x) ∧
      E.rootSeminorm g ≤ M) :
    E.rootSeminorm f ≤ M := by
  obtain ⟨g, hg, hM⟩ := E.exists_of_uniform_approximation (f : RealLp m p) u hfu hS hSfin happrox
  exact (Subtype.ext hg : g = f) ▸ hM

theorem energy_le_of_uniform_approximation (f : E.domain) (u : X → ℝ)
    (hfu : (f : RealLp m p) =ᵐ[m] u) {S : Set X} (hS : MeasurableSet S) (hSfin : m S ≠ ∞)
    {M : ℝ} (hM : 0 ≤ M)
    (happrox : ∀ ε > (0 : ℝ), ∃ (g : E.domain) (v : X → ℝ),
      (g : RealLp m p) =ᵐ[m] v ∧ (∀ x, |v x - u x| ≤ S.indicator (fun _ ↦ ε) x) ∧
      (E.energy g : ℝ) ≤ M) : (E.energy f : ℝ) ≤ M := by
  have hp : 0 < p := zero_lt_one.trans E.one_lt
  have hroot := E.rootSeminorm_le_of_uniform_approximation f u hfu hS hSfin
    (M := M ^ p⁻¹) (fun ε hε ↦ by
      obtain ⟨g, v, hgv, hv, hg⟩ := happrox ε hε
      refine ⟨g, v, hgv, hv, ?_⟩
      rw [E.rootSeminorm_apply]
      exact Real.rpow_le_rpow (NNReal.coe_nonneg _) hg (inv_nonneg.mpr hp.le))
  rw [E.energy_eq_root_rpow, ← show (M ^ p⁻¹) ^ p = M from by
    rw [← Real.rpow_mul hM, inv_mul_cancel₀ hp.ne', Real.rpow_one]]
  exact Real.rpow_le_rpow (apply_nonneg _ _) hroot hp.le

end PEnergy

end WalkDimensions
