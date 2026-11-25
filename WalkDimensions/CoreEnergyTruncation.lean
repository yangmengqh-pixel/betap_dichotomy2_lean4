import WalkDimensions.CoreEnergySublevels
import WalkDimensions.SawtoothPeriod

/-!
# Energy carried by lower value sets

At a dyadic level the localized oscillation splits into the sawtooth of
the level truncation and a thin oscillation on the other side of the level.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal Topology

namespace WalkDimensions

private theorem sawtooth_eq_zero_of_dyadic {k n : ℕ} (hkn : k < n) (j : ℤ) :
    sawtooth (oscillationWidth n) (oscillationWidth k * (j : ℝ)) = 0 := by
  simpa only [zero_add, sawtooth_zero] using sawtooth_add_dyadic hkn 0 j

private theorem localized_self_oscillation_split {a t : ℝ} {k n : ℕ} (hkn : k < n) (j : ℤ)
    (ha : a = oscillationWidth k * (j : ℝ)) :
    min (sawtooth (oscillationWidth n) t) (sublevelRamp (oscillationWidth n) a t) =
      sawtooth (oscillationWidth n) (min t a) +
        sawtooth (oscillationWidth (n + 1)) (min (max (t - a) 0) (oscillationWidth n)) := by
  let r := oscillationWidth n
  have hr : 0 < r := oscillationWidth_pos n
  by_cases ht : t ≤ a
  · rw [sublevelRamp_eq_cap hr.le ht, min_eq_left (sawtooth_le hr t), min_eq_left ht,
      max_eq_right (sub_nonpos.mpr ht), min_eq_left hr.le, sawtooth_zero, add_zero]
  have ht' : a ≤ t := le_of_not_ge ht
  have ha0 : sawtooth r a = 0 := ha ▸ sawtooth_eq_zero_of_dyadic hkn j
  rw [min_eq_right ht', ha0, zero_add, max_eq_left (sub_nonneg.mpr ht')]
  by_cases hfar : a + r ≤ t
  · rw [sublevelRamp_eq_zero hfar, min_eq_right (sawtooth_nonneg _ _),
      min_eq_right (show r ≤ t - a by linarith only [hfar]), oscillationWidth_succ,
      sawtooth_half r hr]
    have he : sawtooth r r = r := by
      rw [sawtooth_eq_abs_of_abs_le hr (by rw [abs_of_nonneg hr.le]), abs_of_nonneg hr.le]
    rw [he, sub_self, min_eq_right hr.le]
  have hnear : t - a ≤ r := by linarith only [lt_of_not_ge hfar]
  have he : sawtooth r (t - a) = t - a := by
    rw [sawtooth_eq_abs_of_abs_le hr, abs_of_nonneg (sub_nonneg.mpr ht')]
    rwa [abs_of_nonneg (sub_nonneg.mpr ht')]
  have hs : sawtooth r t = t - a := by
    have hs' := sawtooth_add_dyadic hkn (t - a) j
    rw [← ha, sub_add_cancel, he] at hs'
    exact hs'
  rw [min_eq_left hnear, oscillationWidth_succ, sawtooth_half r hr, he, hs]
  have hR : sublevelRamp r a t = r - (t - a) := by
    unfold sublevelRamp
    rw [min_eq_left (by linarith only [ht'] : a + r - t ≤ r),
      max_eq_left (by linarith only [hnear] : 0 ≤ a + r - t)]
    ring
  rw [hR]

namespace PEnergy.CompactCore

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {p : ℝ} {E : PEnergy μ p}

noncomputable def lowerClip (f : E.CompactCore) {a : ℝ} (ha : 0 ≤ a) : E.CompactCore :=
  f.mapLipschitz (fun t ↦ min t a) (LipschitzWith.id.min_const a) (min_eq_left ha)

omit [LocallyCompactSpace X] in
theorem sublevelEnergyRoot_eq_root_lowerClip_of_dyadic (f : E.CompactCore)
    {a : ℝ} (ha : 0 ≤ a) {k : ℕ} {j : ℤ}
    (hdyadic : a = oscillationWidth k * (j : ℝ)) :
    f.sublevelEnergyRoot f a = E.rootSeminorm (f.lowerClip ha).domainElement := by
  let v := f.lowerClip ha
  let r := oscillationWidth
  let H (n : ℕ) := (f.ramp (r n) a).neg.mapLipschitz (sawtooth (r (n + 1)))
    (lipschitzWith_sawtooth _) (sawtooth_zero _)
  have hH (n : ℕ) : E.rootSeminorm (H n).domainElement ≤ E.rootSeminorm (f.ramp (r n) a).domainElement := by
    let g := (f.ramp (r n) a).neg
    change E.rootSeminorm (H n).domainElement ≤ _
    have he : E.energy (H n).domainElement ≤ E.energy g.domainElement :=
      (E.exists_lipschitz_one_comp g.domainElement g.ae_eq _ (lipschitzWith_sawtooth _)
        (sawtooth_zero _)).choose_spec.2
    calc
      _ ≤ E.rootSeminorm g.domainElement := by
        rw [E.rootSeminorm_apply, E.rootSeminorm_apply]
        exact Real.rpow_le_rpow (NNReal.coe_nonneg _) (NNReal.coe_le_coe.mpr he)
          (inv_nonneg.mpr (zero_lt_one.trans E.one_lt).le)
      _ = _ := map_neg_eq_map _ _
  have hlim : Tendsto (fun n ↦ E.rootSeminorm (H n).domainElement) atTop (𝓝 0) :=
    squeeze_zero (fun _ ↦ apply_nonneg _ _) hH (f.tendsto_root_ramp a)
  have happrox : ∀ᶠ n in atTop, |E.rootSeminorm (f.oscillation f a n) -
      E.rootSeminorm v.domainElement| ≤ E.rootSeminorm (H n).domainElement := by
    filter_upwards [eventually_gt_atTop k] with n hn
    obtain ⟨l, hl, hlE⟩ :=
      E.exists_sawtooth_energy_eq v.domainElement v.ae_eq v.continuous v.compactSupport (oscillationWidth_pos n)
    let L : E.CompactCore :=
      { domainElement := l
        toFun := sawtooth (r n) ∘ v.toFun
        ae_eq := hl
        continuous := (lipschitzWith_sawtooth _).continuous.comp v.continuous
        compactSupport := v.compactSupport.comp_left (sawtooth_zero _) }
    have hadd : f.oscillation f a n = l + (H n).domainElement := by
      change (f.oscillationCore f a n).domainElement = (L.add (H n)).domainElement
      apply domainElement_eq_of_toFun_eq
      funext x
      change min (sawtooth (r n) (f.toFun x)) (sublevelRamp (r n) a (f.toFun x)) =
        sawtooth (r n) (min (f.toFun x) a) +
          sawtooth (r (n + 1)) (-(offsetRamp (r n) a (f.toFun x)))
      rw [offsetRamp_eq_neg_min (oscillationWidth_pos n).le ha, neg_neg]
      exact localized_self_oscillation_split hn j hdyadic
    have hroot : E.rootSeminorm l = E.rootSeminorm v.domainElement := by
      rw [E.rootSeminorm_apply, E.rootSeminorm_apply, hlE]
    rw [← hroot, hadd]
    have h₁ := E.rootSeminorm.add_le' l (H n).domainElement
    change E.rootSeminorm (l + (H n).domainElement) ≤
      E.rootSeminorm l + E.rootSeminorm (H n).domainElement at h₁
    have h₂ := E.rootSeminorm.add_le' (l + (H n).domainElement) (-(H n).domainElement)
    change E.rootSeminorm (l + (H n).domainElement + -(H n).domainElement) ≤
      E.rootSeminorm (l + (H n).domainElement) + E.rootSeminorm (-(H n).domainElement) at h₂
    rw [add_assoc, add_neg_cancel, add_zero, map_neg_eq_map] at h₂
    exact abs_le.mpr ⟨by linarith only [h₂], by linarith only [h₁]⟩
  have habs := ((f.tendsto_sublevelEnergyRoot f a).sub_const (E.rootSeminorm v.domainElement)).abs
  have hz : |f.sublevelEnergyRoot f a - E.rootSeminorm v.domainElement| ≤ 0 :=
    le_of_tendsto_of_tendsto habs hlim happrox
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hz (abs_nonneg _)))

theorem coreEnergyMeasure_self_sublevel_of_dyadic (f : E.CompactCore)
    {a : ℝ} (ha : 0 ≤ a) {k : ℕ} {j : ℤ}
    (hdyadic : a = oscillationWidth k * (j : ℝ)) :
    f.coreEnergyMeasure {x | f.toFun x ≤ a} = (E.energy (f.lowerClip ha).domainElement : ℝ≥0∞) := by
  rw [f.coreEnergyMeasure_sublevel f a]
  change ENNReal.ofReal (f.sublevelEnergyRoot f a ^ p) = _
  rw [f.sublevelEnergyRoot_eq_root_lowerClip_of_dyadic ha hdyadic, ← E.energy_eq_root_rpow,
    ENNReal.ofReal_coe_nnreal]

end PEnergy.CompactCore
end WalkDimensions
