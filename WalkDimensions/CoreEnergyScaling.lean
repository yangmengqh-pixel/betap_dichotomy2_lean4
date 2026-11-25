import WalkDimensions.CoreEnergyLocality
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-!
# Scalar homogeneity of the core energy measure
-/

open Filter Function MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal Topology Pointwise

namespace WalkDimensions

theorem sawtooth_mul_pos {a : ℝ} (ha : 0 < a) (r t : ℝ) :
    sawtooth (a * r) (a * t) = a * sawtooth r t := by
  let G := range fun j : ℤ ↦ (2 * r) * (j : ℝ)
  have hG : (range fun j : ℤ ↦ (2 * (a * r)) * (j : ℝ)) = a • G := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨(2 * r) * (j : ℝ), mem_range_self _, by change a * _ = _; ring⟩
    · rintro ⟨y, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, by change _ = a * _; ring⟩
  unfold sawtooth
  rw [hG, show a * t = a • t from rfl, infDist_smul₀, Real.norm_eq_abs, abs_of_pos ha]

namespace PEnergy.CompactCore

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {p : ℝ} {E : PEnergy μ p}

theorem coreEnergyMeasure_eq_of_eqOn_affine (f g : E.CompactCore)
    {A : Set X} (hA : MeasurableSet A) {s c : ℝ} (hs : s = 1 ∨ s = -1)
    (h : EqOn f.toFun (fun x ↦ s * g.toFun x + c) A) :
    f.coreEnergyMeasure A = g.coreEnergyMeasure A := by
  rcases hs with rfl | rfl
  · apply f.coreEnergyMeasure_eq_of_eqOn_sub_const g hA (a := c)
    intro x hx
    have hh := h hx
    change f.toFun x = 1 * g.toFun x + c at hh
    change f.toFun x - g.toFun x = c
    linarith only [hh]
  · rw [← g.coreEnergyMeasure_neg]
    apply f.coreEnergyMeasure_eq_of_eqOn_sub_const g.neg hA (a := c)
    intro x hx
    have hh := h hx
    change f.toFun x = -1 * g.toFun x + c at hh
    change f.toFun x - -g.toFun x = c
    linarith only [hh]

theorem coreEnergyMeasure_eq_of_eqOn_sawtooth (f h : E.CompactCore)
    {A : Set X} (hA : MeasurableSet A) {r : ℝ} (hr : 0 < r)
    (heq : EqOn h.toFun (sawtooth r ∘ f.toFun) A) :
    h.coreEnergyMeasure A = f.coreEnergyMeasure A := by
  let S (i : ℤ × Bool) := A ∩ f.toFun ⁻¹' sawtoothCell r i
  have hS (i : ℤ × Bool) : MeasurableSet (S i) :=
    hA.inter ((isClosed_sawtoothCell r i).measurableSet.preimage f.continuous.measurable)
  have hRestr (i : ℤ × Bool) :
      h.coreEnergyMeasure.restrict (S i) = f.coreEnergyMeasure.restrict (S i) := by
    ext B hB
    rw [Measure.restrict_apply hB, Measure.restrict_apply hB]
    apply h.coreEnergyMeasure_eq_of_eqOn_affine f (hB.inter (hS i)) (sawtoothSign_eq i)
      (c := r * (sawtoothOffsetIndex i : ℝ))
    intro x hx
    rw [heq hx.2.1]
    exact sawtooth_eq_affine_of_mem_cell hr hx.2.2
  have hUnion : (⋃ i, S i) = A := by
    apply le_antisymm (iUnion_subset fun _ ↦ inter_subset_left)
    intro x hx
    obtain ⟨i, hi⟩ := exists_mem_sawtoothCell hr (f.toFun x)
    exact mem_iUnion.mpr ⟨i, hx, hi⟩
  have hu := Measure.restrict_iUnion_congr.2 hRestr
  rw [hUnion] at hu
  simpa only [Measure.restrict_apply_univ] using congrArg (fun ν : Measure X ↦ ν univ) hu

private theorem coreEnergyMeasure_compact_smul_le (f : E.CompactCore) {a : ℝ} (ha : 0 < a)
    (K : Compacts X) :
    (f.smul a).coreEnergyMeasure K ≤ ENNReal.ofReal (a ^ p) * f.coreEnergyMeasure K := by
  obtain ⟨g, hg, _⟩ := E.exists_compactCore_sublevel_eq K.isCompact'
    isOpen_univ (subset_univ _)
  change {x | g.toFun x ≤ -1} = (K : Set X) at hg
  have hDist : f.coreEnergyMeasure K = ENNReal.ofReal (f.sublevelDistribution g (-1)) := by
    rw [← hg, f.coreEnergyMeasure_sublevel]
  have hLim : Tendsto (fun n ↦ ENNReal.ofReal (a ^ p * (E.energy (f.oscillation g (-1) n) : ℝ)))
      atTop (𝓝 (ENNReal.ofReal (a ^ p) * f.coreEnergyMeasure K)) := by
    rw [hDist, ← ENNReal.ofReal_mul (Real.rpow_nonneg ha.le p)]
    exact ENNReal.tendsto_ofReal ((f.tendsto_oscillation_energy g (-1)).const_mul (a ^ p))
  apply ge_of_tendsto hLim
  refine Eventually.of_forall fun n ↦ ?_
  let w := f.oscillationCore g (-1) n
  let F := f.smul a
  let w' := w.smul a
  have hr := oscillationWidth_pos n
  have heq : EqOn w'.toFun (sawtooth (a * oscillationWidth n) ∘ F.toFun) K := by
    intro x hx
    have hx' : g.toFun x ≤ -1 := by
      rw [← hg] at hx
      exact hx
    change a * min (sawtooth (oscillationWidth n) (f.toFun x))
      (sublevelRamp (oscillationWidth n) (-1) (g.toFun x)) =
      sawtooth (a * oscillationWidth n) (a * f.toFun x)
    rw [sublevelRamp_eq_cap hr.le hx', min_eq_left (sawtooth_le hr _), sawtooth_mul_pos ha]
  have he := F.coreEnergyMeasure_eq_of_eqOn_sawtooth (A := (K : Set X)) w'
    K.isCompact'.isClosed.measurableSet (mul_pos ha hr) heq
  change F.coreEnergyMeasure K ≤ _
  rw [← he]
  apply (measure_mono (subset_univ _)).trans
  rw [w'.coreEnergyMeasure_univ, ← ENNReal.ofReal_coe_nnreal]
  apply le_of_eq
  congr 1
  change (E.energy (a • w.domainElement) : ℝ) = _
  rw [E.energy_smul_real, abs_of_pos ha]
  rfl

theorem coreEnergyMeasure_smul_pos (f : E.CompactCore) {a : ℝ} (ha : 0 < a) :
    (f.smul a).coreEnergyMeasure = ENNReal.ofReal (a ^ p) • f.coreEnergyMeasure := by
  ext A hA
  have hLe (f : E.CompactCore) (a : ℝ) (ha : 0 < a) :
      (f.smul a).coreEnergyMeasure A ≤ ENNReal.ofReal (a ^ p) * f.coreEnergyMeasure A := by
    rw [hA.measure_eq_iSup_isCompact (f.smul a).coreEnergyMeasure]
    exact iSup_le fun K ↦ iSup_le fun hKA ↦ iSup_le fun hK ↦
      (f.coreEnergyMeasure_compact_smul_le ha ⟨K, hK⟩).trans (mul_le_mul_of_nonneg_left
        (measure_mono hKA) bot_le)
  rw [smul_apply, smul_eq_mul]
  refine le_antisymm (hLe f a ha) ?_
  have hEq : ((f.smul a).smul a⁻¹).toFun = f.toFun := by
    funext x
    change a⁻¹ * (a * f.toFun x) = _
    rw [← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul]
  have hIm := hLe (f.smul a) a⁻¹ (inv_pos.mpr ha)
  have hMass := ((f.smul a).smul a⁻¹).coreEnergyMeasure_eq_on_subset_of_eqOn f hA
    isOpen_univ (subset_univ _) (fun x _ ↦ congrFun hEq x)
  rw [hMass] at hIm
  have h := mul_le_mul_of_nonneg_left hIm (show 0 ≤ ENNReal.ofReal (a ^ p) from bot_le)
  rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg ha.le _),
    ← Real.mul_rpow ha.le (inv_nonneg.mpr ha.le), mul_inv_cancel₀ ha.ne', Real.one_rpow,
    ENNReal.ofReal_one, one_mul] at h
  exact h

theorem coreEnergyMeasure_smul (f : E.CompactCore) (a : ℝ) :
    (f.smul a).coreEnergyMeasure = ENNReal.ofReal (|a| ^ p) • f.coreEnergyMeasure := by
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · rw [abs_of_neg ha, ← f.coreEnergyMeasure_smul_pos (neg_pos.mpr ha),
      ← (f.smul (-a)).coreEnergyMeasure_neg]
    ext A hA
    apply (f.smul a).coreEnergyMeasure_eq_on_subset_of_eqOn (f.smul (-a)).neg hA
      isOpen_univ (subset_univ _)
    intro x _
    change a * f.toFun x = -((-a) * f.toFun x)
    rw [neg_mul, neg_neg]
  · have hE : (E.energy ((f.smul 0).domainElement) : ℝ) = 0 := by
      change (E.energy ((0 : ℝ) • f.domainElement) : ℝ) = 0
      rw [E.energy_smul_real, abs_zero, Real.zero_rpow (zero_lt_one.trans E.one_lt).ne', zero_mul]
    have hMass : (f.smul 0).coreEnergyMeasure univ = 0 := by
      rw [coreEnergyMeasure_univ, ← ENNReal.ofReal_coe_nnreal, hE, ENNReal.ofReal_zero]
    rw [abs_zero, Real.zero_rpow (zero_lt_one.trans E.one_lt).ne', ENNReal.ofReal_zero, zero_smul]
    ext A hA
    rw [FunLike.coe_zero, Pi.zero_apply]
    exact measure_mono_null (subset_univ _) hMass
  · rw [abs_of_pos ha, f.coreEnergyMeasure_smul_pos ha]

end PEnergy.CompactCore

end WalkDimensions
