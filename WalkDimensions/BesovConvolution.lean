import WalkDimensions.ConvolutionApproximation
import WalkDimensions.ConvolutionEnergy

/-!
# Discrete convolution bounds for measurable compactly supported inputs
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SecondCountableTopology X] {m : Measure X}
  [IsFiniteMeasureOnCompacts m] [m.IsOpenPosMeasure] {p : ℝ} (E : PEnergy m p)

theorem exists_energy_approximation_at_scale {β : ℝ}
    (hvol : VolumeDoubling m) (hcap : E.CapacityUpperBound β) :
    ∃ K J : ℝ≥0∞, K ≠ ∞ ∧ J ≠ ∞ ∧
      ∀ {u : X → ℝ}, Measurable u → HasCompactSupport u →
      ∀ (hu : MemLp u (ENNReal.ofReal p) m) {s : ℝ}, s ∈ Ioo (0 : ℝ) 1 →
      ∃ f : E.domain,
        (E.energy f : ℝ≥0∞) ≤ K * besovEnergy m p β univ u s ∧
        (ENNReal.ofReal ‖(f : RealLp m p) - hu.toLp u‖) ^ p ≤
          J * (ENNReal.ofReal s) ^ β * besovEnergy m p β univ u s := by
  classical
  obtain ⟨C, A, hC, hA, hpartition⟩ := E.exists_ball_partition hvol hcap
  obtain ⟨K, hK, henergy⟩ := E.exists_discrete_convolution_energy_le hvol (β := β) hA hC
  obtain ⟨J, hJ, herror⟩ := exists_discrete_convolution_error_le hvol E.one_lt.le hA
  let B := 2 * A + 3
  have hB : 0 < B := by dsimp [B]; linarith
  let K' := K * ENNReal.ofReal (B ^ β)
  have hK' : K' ≠ ∞ := ENNReal.mul_ne_top hK ENNReal.ofReal_ne_top
  refine ⟨K', J, hK', hJ, fun {u} hu hc huLp {s} hs ↦ ?_⟩
  let r := s / B
  have hr : 0 < r := div_pos hs.1 hB
  have hrs : B * r = s := by dsimp [r]; field_simp
  have hsmall : (A + 1) * r < 1 := calc
    _ ≤ B * r := mul_le_mul_of_nonneg_right (by dsimp [B]; linarith) hr.le
    _ = s := hrs
    _ < 1 := hs.2
  let S := cthickening 1 (tsupport u)
  let U := interior S
  have hU : IsOpen U := isOpen_interior
  obtain ⟨t, _, hsep, hcover⟩ := exists_finset_separated_ball_cover
    (hc.isCompact.cthickening (r := 1)) hr
  obtain ⟨g, w, hgw, hw, _, hUnity, hroot⟩ := hpartition t r hr hsep
  have hzero (z : X) : EqOn (w z) (fun _ ↦ 0) (ball z (A * r))ᶜ := (hw z).2.2.2
  have hSupp (z : X) : tsupport (w z) ⊆ closedBall z (A * r) := by
    apply closure_minimal _ isClosed_closedBall
    intro x hx
    by_contra hh
    exact hx (hzero z (fun hm ↦ hh (ball_subset_closedBall hm)))
  have hUnity' : EqOn (fun x ↦ ∑ z ∈ t, w z x) (fun _ ↦ 1) U :=
    hUnity.mono (interior_subset.trans hcover)
  let a (z : X) := ⨍ y in ball z r, u y ∂m
  let f := ∑ z ∈ t, a z • g z
  let v (x : X) := ∑ z ∈ t, a z * w z x
  have hterm (z : X) : ((a z • g z : E.domain) : RealLp m p) =ᵐ[m] fun x ↦ a z * w z x := by
    filter_upwards [Lp.coeFn_smul (a z) (g z : RealLp m p), hgw z] with x hx hzx
    change (a z • (g z : RealLp m p)) x = _
    rw [hx, Pi.smul_apply, smul_eq_mul, hzx]
  have hf : (f : RealLp m p) =ᵐ[m] v :=
    E.coeFn_finsetSum t (fun z ↦ a z • g z) (fun z x ↦ a z * w z x) (fun z _ ↦ hterm z)
  have hthick : thickening 1 (tsupport u) ⊆ U :=
    interior_maximal (thickening_subset_cthickening _ _) isOpen_thickening
  have huU : tsupport u ⊆ U := (self_subset_thickening zero_lt_one _).trans hthick
  have hvU : tsupport v ⊆ U :=
    (tsupport_discrete_convolution_subset hzero).trans
      ((cthickening_subset_thickening' zero_lt_one hsmall _).trans hthick)
  have he := henergy t r hr hsep g w hgw hSupp hroot U hU hUnity' u hu huLp hvU
  have herr := herror t hr w (fun z _ x ↦ ((hw z).2.2.1 x).1) (fun z _ ↦ hzero z)
    U hUnity' huLp huU hvU (f : RealLp m p) (huLp.toLp u) hf (MemLp.coeFn_toLp huLp)
  have hscale : ENNReal.ofReal (r ^ (-β)) =
      ENNReal.ofReal (B ^ β) * (ENNReal.ofReal (B * r)) ^ (-β) := by
    rw [ENNReal.ofReal_rpow_of_pos (mul_pos hB hr), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [Real.mul_rpow hB.le hr.le, ← mul_assoc, ← Real.rpow_add hB,
      add_neg_cancel, Real.rpow_zero, one_mul]
  refine ⟨f, ?_, ?_⟩
  · calc
      _ ≤ _ := he
      _ = K' * besovEnergy m p β univ u s := by
        change K * ENNReal.ofReal (r ^ (-β)) * (∫⁻ x, ballMoment m p u (B * r) x ∂m) = _
        rw [hscale, hrs, besovEnergy, Measure.restrict_univ]
        dsimp only [K']
        simp only [mul_assoc]
  · calc
      _ ≤ _ := herr
      _ = _ := by
        change J * (∫⁻ x, ballMoment m p u (B * r) x ∂m) = _
        rw [hrs, besovEnergy, Measure.restrict_univ, mul_assoc J, ← mul_assoc (ENNReal.ofReal s ^ β),
          ← ENNReal.rpow_add _ _ (ENNReal.ofReal_ne_zero_iff.mpr hs.1) ENNReal.ofReal_ne_top,
          add_neg_cancel, ENNReal.rpow_zero, one_mul]

end WalkDimensions.PEnergy
