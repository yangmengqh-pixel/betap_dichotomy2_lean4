import WalkDimensions.CoreEnergyClarkson

/-!
# The lower Clarkson inequality for the core measure
-/

open Filter Function MeasureTheory Set TopologicalSpace
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy.CompactCore

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {p : ℝ} {E : PEnergy μ p}

theorem pairMeasure_clarkson_lower_compact (f g : E.CompactCore) (hp : p ≤ 2)
    (K : Compacts X) :
    2 * ((f.coreEnergyMeasure K).toReal ^ (p - 1)⁻¹ +
        (g.coreEnergyMeasure K).toReal ^ (p - 1)⁻¹) ^ (p - 1) ≤
      (f.pairMeasure g K).toReal := by
  obtain ⟨w, hw, _⟩ := E.exists_compactCore_sublevel_eq K.isCompact' isOpen_univ (subset_univ _)
  change {x | w.toFun x ≤ -1} = (K : Set X) at hw
  let u (n : ℕ) := f.oscillationCore w (-1) n
  let v (n : ℕ) := g.oscillationCore w (-1) n
  have hK : MeasurableSet (K : Set X) := K.isCompact'.isClosed.measurableSet
  have hEq (n : ℕ) : (u n).pairMeasure (v n) K = f.pairMeasure g K := by
    rw [← hw]
    exact f.pairMeasure_eq_of_eqOn_sawtooths g (u n) (v n)
      (isClosed_le w.continuous continuous_const).measurableSet (oscillationWidth_pos n)
      (f.oscillationCore_eq_sawtooth_on_sublevel w (-1) n)
      (g.oscillationCore_eq_sawtooth_on_sublevel w (-1) n)
  have hEval (h : E.CompactCore) : (h.coreEnergyMeasure K).toReal = h.sublevelDistribution w (-1) := by
    rw [← hw, h.coreEnergyMeasure_sublevel]
    exact ENNReal.toReal_ofReal (Real.rpow_nonneg (h.sublevelEnergyRoot_nonneg w _) _)
  have hComp (h : E.CompactCore) : Tendsto (fun n ↦
      ((h.oscillationCore w (-1) n).coreEnergyMeasure ((K : Set X)ᶜ)).toReal) atTop (𝓝 0) := by
    have hDiff (n : ℕ) :
        ((h.oscillationCore w (-1) n).coreEnergyMeasure ((K : Set X)ᶜ)).toReal =
          (E.energy (h.oscillation w (-1) n) : ℝ) - (h.coreEnergyMeasure K).toReal := by
      let z := h.oscillationCore w (-1) n
      have heq : z.coreEnergyMeasure (K : Set X) = h.coreEnergyMeasure K := by
        rw [← hw]
        exact h.coreEnergyMeasure_eq_of_eqOn_sawtooth z
          (isClosed_le w.continuous continuous_const).measurableSet (oscillationWidth_pos n)
          (h.oscillationCore_eq_sawtooth_on_sublevel w (-1) n)
      rw [show (h.oscillationCore w (-1) n) = z from rfl, measure_compl hK (measure_ne_top _ _),
        ENNReal.toReal_sub_of_le (measure_mono (subset_univ _)) (measure_ne_top _ _),
        z.coreEnergyMeasure_univ, ENNReal.coe_toReal, heq]
      rfl
    simp_rw [hDiff, hEval h]
    simpa only [sub_self] using (h.tendsto_oscillation_energy w (-1)).sub_const
      (h.sublevelDistribution w (-1))
  have hPairComp : Tendsto (fun n ↦
      ((u n).pairMeasure (v n) ((K : Set X)ᶜ)).toReal) atTop (𝓝 0) := by
    have h := ((hComp f).add (hComp g)).const_mul (2 : ℝ)
    rw [add_zero, mul_zero] at h
    exact squeeze_zero (fun _ ↦ ENNReal.toReal_nonneg)
      (fun n ↦ (u n).pairMeasure_upper_le_two_mul (v n) hp hK.compl) h
  have hTotal : Tendsto (fun n ↦ ((u n).pairMeasure (v n) univ).toReal) atTop
      (𝓝 ((f.pairMeasure g K).toReal)) := by
    have h := hPairComp.const_add ((f.pairMeasure g K).toReal)
    rw [add_zero] at h
    convert h using 1
    funext n
    let ν := (u n).pairMeasure (v n)
    change (ν univ).toReal = (f.pairMeasure g K).toReal + (ν ((K : Set X)ᶜ)).toReal
    rw [← hEq n, measure_compl hK (measure_ne_top _ _),
      ENNReal.toReal_sub_of_le (measure_mono (subset_univ _)) (measure_ne_top _ _)]
    change (ν univ).toReal = (ν K).toReal + ((ν univ).toReal - (ν K).toReal)
    ring
  have hpow (t : ℝ) (ht : 0 ≤ t) :
      Tendsto (fun n ↦ ((E.energy (u n).domainElement : ℝ) ^ t +
        (E.energy (v n).domainElement : ℝ) ^ t)) atTop
        (𝓝 ((f.coreEnergyMeasure K).toReal ^ t + (g.coreEnergyMeasure K).toReal ^ t)) := by
    rw [hEval f, hEval g]
    exact ((f.tendsto_oscillation_energy w (-1)).rpow_const (Or.inr ht)).add
      ((g.tendsto_oscillation_energy w (-1)).rpow_const (Or.inr ht))
  have hp' := sub_nonneg.mpr E.one_lt.le
  apply le_of_tendsto_of_tendsto
    (((hpow _ (inv_nonneg.mpr hp')).rpow_const (Or.inr hp')).const_mul 2) hTotal
  refine Eventually.of_forall fun n ↦ ?_
  change _ ≤ (((u n).pairMeasure (v n)) univ).toReal
  rw [(u n).pairMeasure_univ (v n), ENNReal.toReal_add ENNReal.coe_ne_top ENNReal.coe_ne_top,
    ENNReal.coe_toReal, ENNReal.coe_toReal]
  exact E.clarkson_le_two hp (u n).domainElement (v n).domainElement

theorem pairMeasure_clarkson_lower (f g : E.CompactCore) (hp : p ≤ 2)
    {A : Set X} (hA : MeasurableSet A) :
    2 * ((f.coreEnergyMeasure A).toReal ^ (p - 1)⁻¹ +
        (g.coreEnergyMeasure A).toReal ^ (p - 1)⁻¹) ^ (p - 1) ≤
      (f.pairMeasure g A).toReal := by
  let ν := f.coreEnergyMeasure + g.coreEnergyMeasure
  let ε (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp only [ε]; positivity
  choose K hKA hK hnear using fun n ↦
    hA.exists_isCompact_lt_add (μ := ν) (measure_ne_top _ _)
      (ENNReal.ofReal_ne_zero_iff.mpr (hε n))
  have hL (i : Bool) : Tendsto (fun n ↦ ((if i then f else g).coreEnergyMeasure (K n)).toReal)
      atTop (𝓝 (((if i then f else g).coreEnergyMeasure A).toReal)) := by
    let M := ((if i then f else g).coreEnergyMeasure A).toReal
    have hM (n : ℕ) : ((if i then f else g).coreEnergyMeasure (K n)).toReal ≤ M :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (hKA n))
    have hM' (n : ℕ) : M - ε n ≤ ((if i then f else g).coreEnergyMeasure (K n)).toReal := by
      have h := (ENNReal.toReal_lt_toReal (measure_ne_top ν A) (ENNReal.add_ne_top.mpr
        ⟨measure_ne_top ν (K n), ENNReal.ofReal_ne_top⟩)).mpr (hnear n)
      rw [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal (hε n).le] at h
      simp only [ν, FunLike.coe_add, Pi.add_apply, ENNReal.toReal_add (measure_ne_top _ _)
        (measure_ne_top _ _)] at h
      have hf := ENNReal.toReal_mono (measure_ne_top f.coreEnergyMeasure A)
        (measure_mono (μ := f.coreEnergyMeasure) (hKA n))
      have hg := ENNReal.toReal_mono (measure_ne_top g.coreEnergyMeasure A)
        (measure_mono (μ := g.coreEnergyMeasure) (hKA n))
      cases i <;> simp only [M, Bool.false_eq_true, ↓reduceIte] <;> linarith only [h, hf, hg]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      (by simpa only [sub_zero] using tendsto_one_div_add_atTop_nhds_zero_nat.const_sub M)
      tendsto_const_nhds hM' hM
  have hp' := sub_nonneg.mpr E.one_lt.le
  have hF := hL true
  have hG := hL false
  simp only [Bool.false_eq_true, ↓reduceIte] at hF hG
  have hLim := (((hF.rpow_const (Or.inr (inv_nonneg.mpr hp'))).add
    (hG.rpow_const (Or.inr (inv_nonneg.mpr hp')))).rpow_const (Or.inr hp')).const_mul 2
  refine le_of_tendsto_of_tendsto hLim tendsto_const_nhds (Eventually.of_forall fun n ↦ ?_)
  exact (f.pairMeasure_clarkson_lower_compact g hp ⟨K n, hK n⟩).trans
    (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (hKA n)))

end WalkDimensions.PEnergy.CompactCore
