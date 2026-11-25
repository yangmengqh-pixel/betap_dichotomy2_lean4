import WalkDimensions.HarmonicPlateTest
import WalkDimensions.HarmonicSingularity
import WalkDimensions.LocalPlateauMeasure
import WalkDimensions.WalkRatioStrictness
import Mathlib.Analysis.Real.Cardinality

/-!
# A nonconstant test function with singular energy measure
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal Topology

namespace WalkDimensions

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [Nonempty X] [ProperSpace X] [SecondCountableTopology X] {m : Measure X}
  [m.Regular] [m.IsOpenPosMeasure] [SFinite m]

omit [Nonempty X] [ProperSpace X] [SecondCountableTopology X] [m.Regular] [m.IsOpenPosMeasure] in
private theorem exists_null_sphere_radius (x : X) {a b : ℝ} (hab : a < b) :
    ∃ r ∈ Ioo a b, m (sphere x r) = 0 := by
  by_contra h
  apply hab.not_ge
  apply (Cardinal.Real.Ioo_countable_iff (x := a) (y := b)).mp
  have hCount : {r : ℝ | 0 < m (sphere x r)}.Countable :=
    Measure.countable_meas_level_set_pos (continuous_id.dist continuous_const).measurable
  exact hCount.mono fun r hr ↦ pos_iff_ne_zero.mpr (fun hz ↦ h ⟨r, hr, hz⟩)

namespace PEnergy

theorem exists_nonconstant_singular_test {p β : ℝ} (E : PEnergy m p)
    (hβ : p < β) (hvol : VolumeDoubling m) (hCC : ChainCondition X)
    (hPI : E.Poincare E.energyMeasure β) (hcap : E.CapacityUpperBound β)
    (hunbounded : ¬ Bornology.IsBounded (univ : Set X)) :
    ∃ (f : E.domain) (w : X → ℝ), (f : RealLp m p) =ᵐ[m] w ∧ Measurable w ∧
      HasCompactSupport w ∧ (∀ y, w y ∈ Icc (0 : ℝ) 1) ∧ (¬ ∃ c : ℝ, w =ᵐ[m] fun _ ↦ c) ∧
      (E.energyMeasure f).MutuallySingular m := by
  let x : X := Classical.choice ‹Nonempty X›
  obtain ⟨C, A, hC, hA, hCut⟩ := E.exists_compact_core_cutoff_of_capacity hcap hvol
  obtain ⟨r, hr, hr₀⟩ := exists_null_sphere_radius (m := m) x zero_lt_one
  obtain ⟨R, hR, hR₀⟩ := exists_null_sphere_radius (m := m) x (lt_add_one A)
  let K := closedBall x r
  let S := closedBall x R
  let U := ball x R \ K
  have hrR : r < R := (hr.2.trans hA).trans hR.1
  have hS : IsCompact S := isCompact_closedBall _ _
  have hSc : Sᶜ.Nonempty := by
    by_contra h
    have he : S = univ := eq_univ_of_forall fun y ↦ by_contra fun hy ↦ h ⟨y, hy⟩
    exact hunbounded (he ▸ hS.isBounded)
  have hKm : MeasurableSet K := isClosed_closedBall.measurableSet
  have hSm : MeasurableSet S := hS.isClosed.measurableSet
  have hU : IsOpen U := isOpen_ball.sdiff isClosed_closedBall
  obtain ⟨χ, _, hχ₁, hχS, _⟩ := hCut x 1 zero_lt_one
  have hχK : EqOn χ.toFun (fun _ ↦ 1) K := fun y hy ↦ hχ₁ (closedBall_subset_ball hr.2 hy)
  have hχ₀ : EqOn χ.toFun (fun _ ↦ 0) Sᶜ := by
    intro y hy
    apply notMem_support.mp
    intro hs
    exact hy (ball_subset_closedBall (ball_subset_ball hR.1.le (by simpa only [mul_one] using hχS (subset_closure hs))))
  obtain ⟨f, hf₁, hf₀, hfI, hfH⟩ := E.exists_bounded_harmonic_plate_test hPI hKm hS hSc
    ⟨χ.domainElement, by
      filter_upwards [ae_restrict_of_ae (s := K) χ.ae_eq, ae_restrict_mem hKm] with y hy hyK
      exact hy.trans (hχK hyK),
      by
        filter_upwards [ae_restrict_of_ae (s := Sᶜ) χ.ae_eq, ae_restrict_mem hSm.compl] with y hy hyS
        exact hy.trans (hχ₀ hyS)⟩
  have hRestr := E.harmonic_energyMeasure_restrict_mutuallySingular hβ hvol hCC hPI hcap f hU
    (fun v hv ↦ hfH v (hv.trans (sdiff_subset_sdiff_left ball_subset_closedBall)))
  let ν := E.energyMeasure f
  have hβ₀ := (zero_lt_one.trans E.one_lt).trans hβ
  have hInner : ν (ball x r) = 0 := E.energyMeasure_eq_zero_of_ae_const_on_open hβ₀
    hvol hPI hcap isOpen_ball (ae_mono (Measure.restrict_mono ball_subset_closedBall le_rfl) hf₁)
  have hOuter : ν Sᶜ = 0 :=
    E.energyMeasure_eq_zero_of_ae_const_on_open hβ₀ hvol hPI hcap hS.isClosed.isOpen_compl hf₀
  have hObs : ν.MutuallySingular m := by
    obtain ⟨N, hN, hνN, hmN⟩ := hRestr
    have hνUN : ν (N ∩ U) = 0 := by rwa [Measure.restrict_apply hN] at hνN
    have hνZero : ν ((N ∩ U) ∪ (ball x r ∪ Sᶜ)) = 0 :=
      measure_union_null hνUN (measure_union_null hInner hOuter)
    have hmZero : m (Nᶜ ∪ (sphere x r ∪ sphere x R)) = 0 :=
      measure_union_null hmN (measure_union_null hr₀ hR₀)
    apply Measure.MutuallySingular.mk hνZero hmZero
    intro y _
    by_cases hN' : y ∈ N
    · by_cases hDist : dist y x < r
      · exact Or.inl (Or.inr (Or.inl hDist))
      · by_cases hir : dist y x = r
        · exact Or.inr (Or.inr (Or.inl hir))
        · by_cases hDR : dist y x < R
          · exact Or.inl (Or.inl ⟨hN', hDR, fun h ↦ hir (le_antisymm h (le_of_not_gt hDist))⟩)
          · by_cases hR' : dist y x = R
            · exact Or.inr (Or.inr (Or.inr hR'))
            · exact Or.inl (Or.inr (Or.inr (fun h ↦ hR' (le_antisymm h (le_of_not_gt hDR)))))
    · exact Or.inr (Or.inl hN')
  let hMeas := (Lp.aestronglyMeasurable (f : RealLp m p)).aemeasurable
  let v := hMeas.mk (f : RealLp m p)
  let w : X → ℝ := S.indicator (fun y ↦ min 1 (max 0 (v y)))
  have hw : Measurable w := (measurable_const.min (measurable_const.max hMeas.measurable_mk)).indicator hSm
  have hwBounds (y : X) : w y ∈ Icc (0 : ℝ) 1 := by
    by_cases hy : y ∈ S
    · rw [show w y = S.indicator (fun z ↦ min 1 (max 0 (v z))) y from rfl, indicator_of_mem hy]
      exact ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩
    · simp [w, indicator_of_notMem hy]
  have hfw : (f : RealLp m p) =ᵐ[m] w := by
    filter_upwards [hMeas.ae_eq_mk, hfI, (ae_restrict_iff' hSm.compl).mp hf₀] with y hy hi hz
    by_cases hyS : y ∈ S
    · rw [show w y = S.indicator (fun z ↦ min 1 (max 0 (v z))) y from rfl, indicator_of_mem hyS, ← show (f : RealLp m p) y = v y from hy,
        max_eq_right hi.1, min_eq_right hi.2]
    · rw [show w y = S.indicator (fun z ↦ min 1 (max 0 (v z))) y from rfl, indicator_of_notMem hyS]
      exact hz hyS
  have hwS : HasCompactSupport w := HasCompactSupport.intro hS (fun y hy ↦ indicator_of_notMem hy _)
  refine ⟨f, w, hfw, hw, hwS, hwBounds, ?_, hObs⟩
  rintro ⟨c, hc⟩
  have hz : ∀ᵐ y ∂m.restrict Sᶜ, (0 : ℝ) = c := by
    filter_upwards [ae_restrict_of_ae (s := Sᶜ) (hfw.trans hc), hf₀] with y hy hy₀
    exact hy₀.symm.trans hy
  have ho : ∀ᵐ y ∂m.restrict K, (1 : ℝ) = c := by
    filter_upwards [ae_restrict_of_ae (s := K) (hfw.trans hc), hf₁] with y hy hy₁
    exact hy₁.symm.trans hy
  have hKpos := (measure_ball_pos m x hr.1).trans_le (measure_mono (ball_subset_closedBall : ball x r ⊆ K))
  have hScpos := hS.isClosed.isOpen_compl.measure_pos m hSc
  let : NeZero (m.restrict Sᶜ) := ⟨by
    intro he
    apply hScpos.ne'
    rw [← Measure.restrict_apply_univ, he]
    simp⟩
  let : NeZero (m.restrict K) := ⟨by
    intro he
    apply hKpos.ne'
    rw [← Measure.restrict_apply_univ, he]
    simp⟩
  exact zero_ne_one ((hz.exists.choose_spec).trans (ho.exists.choose_spec).symm)

end PEnergy

theorem walkExponent_ratio_lt_of_superlinear {p q βp βq : ℝ}
    (Ep : PEnergy m p) (Eq : PEnergy m q) (hpq : p < q)
    (hvol : VolumeDoubling m) (hCC : ChainCondition X) (hβp : 0 < βp) (hβq : q < βq)
    (hPIp : Ep.Poincare Ep.energyMeasure βp) (hPIq : Eq.Poincare Eq.energyMeasure βq)
    (hcapP : Ep.CapacityUpperBound βp) (hcapQ : Eq.CapacityUpperBound βq)
    (hunbounded : ¬ Bornology.IsBounded (univ : Set X)) : βq / q < βp / p := by
  obtain ⟨f, w, hfw, hw, hwc, hb, hnc, hs⟩ :=
    Eq.exists_nonconstant_singular_test hβq hvol hCC hPIq hcapQ hunbounded
  have hwLp : MemLp w (ENNReal.ofReal p) m := by
    let S := tsupport w
    have hS : MeasurableSet S := (isClosed_closure : IsClosed S).measurableSet
    let : IsFiniteMeasure (m.restrict S) := ⟨by
      rw [Measure.restrict_apply_univ]
      exact hwc.isCompact.measure_lt_top⟩
    have hEq : S.indicator w = w :=
      indicator_eq_self.2 (subset_closure : support w ⊆ S)
    rw [← hEq, memLp_indicator_iff_restrict hS.nullMeasurableSet]
    apply MemLp.of_bound hw.aestronglyMeasurable 1
    exact Eventually.of_forall fun y ↦ by rw [Real.norm_of_nonneg (hb y).1]; exact (hb y).2
  exact walkExponent_ratio_lt_of_singular_domain Ep Eq hpq hvol hβp
    ((zero_lt_one.trans Eq.one_lt).trans hβq) hPIp hPIq hcapP hcapQ hunbounded f hfw hw hwc hwLp hnc hs

end WalkDimensions
