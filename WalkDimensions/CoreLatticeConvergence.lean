import WalkDimensions.EnergyStrongConvergence
import WalkDimensions.EnergyLatticeIdentity
import WalkDimensions.SawtoothEnergy

/-!
# Convergence of a fixed localization in the graph norm
-/

open Filter Function MeasureTheory Set
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy.CompactCore

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {p : ℝ} {E : PEnergy μ p}

theorem norm_sub_le_of_ae_abs_sub_le (f g u v : RealLp μ p)
    (h : ∀ᵐ x ∂μ, |f x - g x| ≤ |u x - v x|) :
    ‖f - g‖ ≤ ‖u - v‖ := by
  have he : eLpNorm (f - g) (ENNReal.ofReal p) μ ≤ eLpNorm (u - v) (ENNReal.ofReal p) μ := by
    apply eLpNorm_mono_ae (Lp.aestronglyMeasurable (f - g))
    filter_upwards [h, Lp.coeFn_sub f g, Lp.coeFn_sub u v] with x hx hf hu
    simpa only [hf, hu, Pi.sub_apply, Real.norm_eq_abs] using hx
  rw [Lp.norm_def, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_lt_top (u - v)).ne he

private theorem norm_sub_le_of_pointwise_contraction (f g a b : E.CompactCore)
    (h : ∀ x, |f.toFun x - g.toFun x| ≤ |a.toFun x - b.toFun x|) :
    ‖(f.domainElement : RealLp μ p) - (g.domainElement : RealLp μ p)‖ ≤
      ‖(a.domainElement : RealLp μ p) - (b.domainElement : RealLp μ p)‖ := by
  apply norm_sub_le_of_ae_abs_sub_le
  filter_upwards [f.ae_eq, g.ae_eq, a.ae_eq, b.ae_eq] with x hf hg ha hb
  simpa only [hf, hg, ha, hb] using h x

noncomputable def saw (f : E.CompactCore) (r : ℝ) : E.CompactCore :=
  f.mapLipschitz (sawtooth r) (lipschitzWith_sawtooth r) (sawtooth_zero r)

theorem energy_saw_eq (f : E.CompactCore) {r : ℝ} (hr : 0 < r) :
    E.energy (f.saw r).domainElement = E.energy f.domainElement := by
  obtain ⟨g, hg, hE⟩ := E.exists_sawtooth_energy_eq f.domainElement f.ae_eq
    f.continuous f.compactSupport hr
  have he : (f.saw r).domainElement = g := by
    apply Subtype.ext
    exact Lp.ext ((f.saw r).ae_eq.trans hg.symm)
  rw [he, hE]

theorem eventually_lt_energy_of_norm_sub_tendsto {f : E.CompactCore} {g : ℕ → E.CompactCore}
    {L : ℝ} (hL : L < (E.energy f.domainElement : ℝ))
    (hLp : Tendsto (fun n ↦ ‖((g n).domainElement : RealLp μ p) -
      (f.domainElement : RealLp μ p)‖) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, L < (E.energy (g n).domainElement : ℝ) := by
  by_cases hL₀ : L < 0
  · exact Eventually.of_forall fun _ ↦ hL₀.trans_le (NNReal.coe_nonneg _)
  have hp := zero_lt_one.trans E.one_lt
  have hL₀' := le_of_not_gt hL₀
  obtain ⟨a, hLa, ha⟩ := exists_between hL
  have ha₀ := hL₀'.trans hLa.le
  have hroot : a ^ p⁻¹ < E.rootSeminorm f.domainElement := by
    rw [E.rootSeminorm_apply]
    exact Real.rpow_lt_rpow ha₀ ha (inv_pos.mpr hp)
  filter_upwards [E.eventually_le_rootSeminorm_of_norm_sub_tendsto hroot hLp] with n hn
  have h := Real.rpow_le_rpow (Real.rpow_nonneg ha₀ _) hn hp.le
  rw [← Real.rpow_mul ha₀, inv_mul_cancel₀ hp.ne', Real.rpow_one, ← E.energy_eq_root_rpow] at h
  exact hLa.trans_le h

variable [LocallyCompactSpace X]

theorem tendsto_energy_min_of_norm_sub_tendsto {f : E.CompactCore} {g : ℕ → E.CompactCore}
    (v : E.CompactCore)
    (hLp : Tendsto (fun n ↦ ‖((g n).domainElement : RealLp μ p) -
      (f.domainElement : RealLp μ p)‖) atTop (𝓝 0))
    (hE : Tendsto (fun n ↦ (E.energy (g n).domainElement : ℝ))
      atTop (𝓝 (E.energy f.domainElement : ℝ))) :
    Tendsto (fun n ↦ (E.energy ((g n).minAddConst v (a := 0) le_rfl).domainElement : ℝ))
      atTop (𝓝 (E.energy (f.minAddConst v (a := 0) le_rfl).domainElement : ℝ)) := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt.le⟩
  let L (w : E.CompactCore) := w.minAddConst v (a := 0) le_rfl
  let H (w : E.CompactCore) := w.sup v
  have hL (n : ℕ) : ‖((L (g n)).domainElement : RealLp μ p) - ((L f).domainElement : RealLp μ p)‖ ≤
      ‖((g n).domainElement : RealLp μ p) - (f.domainElement : RealLp μ p)‖ := by
    apply norm_sub_le_of_pointwise_contraction
    intro x
    have hh := lipschitzWith_iff_dist_le_mul.mp (LipschitzWith.id.min_const (v.toFun x))
      ((g n).toFun x) (f.toFun x)
    change |min ((g n).toFun x) (v.toFun x + 0) - min (f.toFun x) (v.toFun x + 0)| ≤ _
    simpa only [id_eq, Real.dist_eq, NNReal.coe_one, one_mul, add_zero] using hh
  have hH (n : ℕ) : ‖((H (g n)).domainElement : RealLp μ p) - ((H f).domainElement : RealLp μ p)‖ ≤
      ‖((g n).domainElement : RealLp μ p) - (f.domainElement : RealLp μ p)‖ := by
    apply norm_sub_le_of_pointwise_contraction
    intro x
    rw [show (H (g n)).toFun x = _ from (g n).sup_apply v x, show (H f).toFun x = _ from f.sup_apply v x]
    have hh := lipschitzWith_iff_dist_le_mul.mp (LipschitzWith.id.max_const (v.toFun x))
      ((g n).toFun x) (f.toFun x)
    simpa only [id_eq, Real.dist_eq, NNReal.coe_one, one_mul] using hh
  have hLt := squeeze_zero (fun n ↦ norm_nonneg
    (((L (g n)).domainElement : RealLp μ p) - ((L f).domainElement : RealLp μ p))) hL hLp
  have hHt := squeeze_zero (fun n ↦ norm_nonneg
    (((H (g n)).domainElement : RealLp μ p) - ((H f).domainElement : RealLp μ p))) hH hLp
  have hAdd (w : E.CompactCore) :
      (E.energy (L w).domainElement : ℝ) + E.energy (H w).domainElement =
        (E.energy w.domainElement : ℝ) + E.energy v.domainElement := by
    simpa only [L, H, NNReal.coe_add, add_comm] using congrArg NNReal.toReal (w.energy_sup_add_min v)
  change Tendsto (fun n ↦ (E.energy (L (g n)).domainElement : ℝ)) atTop
    (𝓝 (E.energy (L f).domainElement : ℝ))
  apply tendsto_order.2
  refine ⟨fun a ha ↦ eventually_lt_energy_of_norm_sub_tendsto ha hLt, fun b hb ↦ ?_⟩
  let ε := (b - (E.energy (L f).domainElement : ℝ)) / 2
  have hε : 0 < ε := half_pos (sub_pos.mpr hb)
  have h₁ := hE.eventually_lt_const (lt_add_of_pos_right _ hε)
  have h₂ := eventually_lt_energy_of_norm_sub_tendsto (sub_lt_self _ hε) hHt
  filter_upwards [h₁, h₂] with n hn₁ hn₂
  have hEq := hAdd (g n)
  have hEq' := hAdd f
  dsimp only [ε] at hn₁ hn₂
  linarith only [hEq, hEq', hn₁, hn₂]

theorem tendsto_oscillation_energy_of_graph_sub_tendsto {f : E.CompactCore}
    {g : ℕ → E.CompactCore} (v : E.CompactCore) (a : ℝ) (k : ℕ)
    (ha : a + oscillationWidth k ≤ 0)
    (hLp : Tendsto (fun n ↦ ‖((g n).domainElement : RealLp μ p) -
      (f.domainElement : RealLp μ p)‖) atTop (𝓝 0))
    (hRoot : Tendsto (fun n ↦ E.rootSeminorm ((g n).domainElement - f.domainElement))
      atTop (𝓝 0)) :
    Tendsto (fun n ↦ (E.energy ((g n).oscillation v a k) : ℝ)) atTop
      (𝓝 (E.energy (f.oscillation v a k) : ℝ)) := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt.le⟩
  let r := oscillationWidth k
  have hr : 0 < r := oscillationWidth_pos k
  let w := v.ramp r a
  have hz : sublevelRamp r a 0 = 0 := sublevelRamp_eq_zero ha
  have hEq (u : E.CompactCore) : u.oscillation v a k =
      ((u.saw r).minAddConst w (a := 0) le_rfl).domainElement := by
    change (u.oscillationCore v a k).domainElement = _
    apply domainElement_eq_of_toFun_eq
    funext x
    change min (sawtooth r (u.toFun x)) (sublevelRamp r a (v.toFun x)) =
      min (sawtooth r (u.toFun x)) (offsetRamp r a (v.toFun x) + 0)
    rw [offsetRamp, hz, sub_zero, add_zero]
  simp_rw [hEq]
  apply tendsto_energy_min_of_norm_sub_tendsto
  · refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ ?_) hLp
    apply norm_sub_le_of_pointwise_contraction
    intro x
    have hh := lipschitzWith_iff_dist_le_mul.mp (lipschitzWith_sawtooth r) ((g n).toFun x)
      (f.toFun x)
    simpa only [saw, mapLipschitz, Function.comp_apply, Real.dist_eq, NNReal.coe_one, one_mul] using hh
  · simp_rw [energy_saw_eq _ hr]
    have hRoot' : Tendsto (fun n ↦ E.rootSeminorm (f.domainElement - (g n).domainElement))
        atTop (𝓝 0) := by
      have hEq (n : ℕ) : E.rootSeminorm (f.domainElement - (g n).domainElement) =
          E.rootSeminorm ((g n).domainElement - f.domainElement) := by
        rw [← neg_sub ((g n).domainElement) f.domainElement, map_neg_eq_map]
      simp_rw [hEq]
      exact hRoot
    simpa only [sub_sub_cancel] using E.tendsto_energy_sub_of_root_tendsto_zero f.domainElement
      (fun n ↦ f.domainElement - (g n).domainElement) hRoot'

end WalkDimensions.PEnergy.CompactCore
