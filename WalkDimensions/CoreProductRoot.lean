import WalkDimensions.EnergyDerivativeProduct

/-!
# Quantitative product estimate on bounded core functions
-/

open Filter Function MeasureTheory Set
open scoped ENNReal

namespace WalkDimensions.PEnergy.CompactCore

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {m : Measure X} [IsFiniteMeasureOnCompacts m] {p : ℝ} {E : PEnergy m p}

theorem root_mul_le_of_bound (u v : E.CompactCore) {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hu : ∀ x, |u.toFun x| ≤ M) (hv : ∀ x, |v.toFun x| ≤ N) :
    E.rootSeminorm (u.mul v).domainElement ≤ M * E.rootSeminorm v.domainElement +
      N * E.rootSeminorm u.domainElement := by
  have hSup (f : E.CompactCore) {C : ℝ} (hf : ∀ x, |f.toFun x| ≤ C) :
      eLpNorm (f.domainElement : RealLp m p) ∞ m ≤ ENNReal.ofReal C := by
    rw [eLpNorm_exponent_top (Lp.aestronglyMeasurable (f.domainElement : RealLp m p))]
    apply eLpNormEssSup_le_of_ae_eNorm_bound
    filter_upwards [f.ae_eq] with x hx
    rw [hx, Real.eNorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (hf x)
  have hU := hSup u hu
  have hV := hSup v hv
  obtain ⟨f, hf, hroot⟩ := E.algebra u.domainElement v.domainElement
    (hU.trans_lt ENNReal.ofReal_lt_top) (hV.trans_lt ENNReal.ofReal_lt_top)
  have he : f = (u.mul v).domainElement := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [hf, u.ae_eq, v.ae_eq, (u.mul v).ae_eq] with x hx hux hvx hy
    rw [hx, hux, hvx, hy, mul_apply]
  rw [← he]
  apply hroot.trans
  have hU' := ENNReal.toReal_mono ENNReal.ofReal_ne_top hU
  have hV' := ENNReal.toReal_mono ENNReal.ofReal_ne_top hV
  rw [ENNReal.toReal_ofReal hM] at hU'
  rw [ENNReal.toReal_ofReal hN] at hV'
  exact add_le_add (mul_le_mul_of_nonneg_right hU' (apply_nonneg _ _))
    (mul_le_mul_of_nonneg_right hV' (apply_nonneg _ _))

end WalkDimensions.PEnergy.CompactCore
