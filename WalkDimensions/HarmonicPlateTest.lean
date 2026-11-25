import WalkDimensions.BoundedSupportCoercivity
import WalkDimensions.EnergyMinimizer
import WalkDimensions.EnergyDerivativeLaws
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Bounded harmonic test functions from almost-everywhere plate constraints
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {m : Measure X} [IsFiniteMeasureOnCompacts m] [m.IsOpenPosMeasure]
  {p : ℝ} (E : PEnergy m p)

theorem exists_bounded_harmonic_plate_test {β : ℝ}
    (hPI : E.Poincare E.energyMeasure β) {K S : Set X}
    (hK : MeasurableSet K) (hS : IsCompact S) (hProper : Sᶜ.Nonempty)
    (hTest : ∃ f : E.domain, (f : RealLp m p) =ᵐ[m.restrict K] (fun _ ↦ 1) ∧
      (f : RealLp m p) =ᵐ[m.restrict Sᶜ] (fun _ ↦ 0)) :
    ∃ h : E.domain, (h : RealLp m p) =ᵐ[m.restrict K] (fun _ ↦ 1) ∧
      (h : RealLp m p) =ᵐ[m.restrict Sᶜ] (fun _ ↦ 0) ∧
      (∀ᵐ x ∂m, (h : RealLp m p) x ∈ Icc (0 : ℝ) 1) ∧
      ∀ v : E.CompactCore, support v.toFun ⊆ S \ K →
        E.energyDerivativeMeasure h v.domainElement univ = 0 := by
  let G := E.graphSeminorm.toAddGroupSeminorm.toSeminormedAddCommGroup
  let : SeminormedAddCommGroup E.domain := G
  let : PseudoMetricSpace E.domain := G.toPseudoMetricSpace
  let : TopologicalSpace E.domain := G.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let : FirstCountableTopology E.domain :=
    ⟨fun x ↦ (Metric.nhds_basis_ball_inv_nat_succ (x := x)).isCountablyGenerated⟩
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt.le⟩
  let C : Set E.domain := {f | (f : RealLp m p) =ᵐ[m.restrict K] (fun _ ↦ 1) ∧
    (f : RealLp m p) =ᵐ[m.restrict Sᶜ] (fun _ ↦ 0)}
  have ae_lin (a : ℝ) (f g : E.domain) :
      ((a • f + g : E.domain) : RealLp m p) =ᵐ[m] (fun x ↦ a * (f : RealLp m p) x + (g : RealLp m p) x) := by
    change (a • f.val + g.val : RealLp m p) =ᵐ[m] _
    filter_upwards [Lp.coeFn_add (a • f.val) g.val, Lp.coeFn_smul a f.val] with x hx hy
    rw [hx, Pi.add_apply, hy, Pi.smul_apply, smul_eq_mul]
  have hConv : Convex ℝ C := by
    intro f hf g hg a b _ _ hab
    obtain ⟨hf₁, hf₀⟩ := hf
    obtain ⟨hg₁, hg₀⟩ := hg
    have he : ((a • f + b • g : E.domain) : RealLp m p) =ᵐ[m]
        (fun x ↦ a * (f : RealLp m p) x + b * (g : RealLp m p) x) := by
      filter_upwards [ae_lin a f (b • g), Lp.coeFn_smul b g.val] with x hx hy
      rw [hx]
      change _ + (b • g.val : RealLp m p) x = _
      rw [hy, Pi.smul_apply, smul_eq_mul]
    constructor
    · filter_upwards [ae_restrict_of_ae (s := K) he, hf₁, hg₁] with x hx hfx hgx
      simp only [hx, hfx, hgx, mul_one, hab]
    · filter_upwards [ae_restrict_of_ae (s := Sᶜ) he, hf₀, hg₀] with x hx hfx hgx
      simp only [hx, hfx, hgx, mul_zero, add_zero]
  have hClosed : IsClosed C := by
    apply IsSeqClosed.isClosed
    intro f g hf hg
    have hLp : Tendsto (fun n ↦ ((f n) : RealLp m p)) atTop (𝓝 (g : RealLp m p)) := by
      apply Metric.tendsto_nhds.2
      intro ε hε
      have hmetric := (@Metric.tendsto_nhds E.domain ℕ G.toPseudoMetricSpace atTop f g).1 hg
      filter_upwards [hmetric ε hε] with n hn
      rw [@dist_eq_norm _ G] at hn
      change E.graphSeminorm (f n - g) < ε at hn
      rw [dist_eq_norm]
      exact (E.norm_le_graphSeminorm (f n - g)).trans_lt hn
    obtain ⟨n, _, hn⟩ := (tendstoInMeasure_of_tendsto_Lp hLp).exists_seq_tendsto_ae
    have hA₁ : ∀ᵐ x ∂m.restrict K, ∀ j, ((f j : E.domain) : RealLp m p) x = 1 :=
      ae_all_iff.2 fun j ↦ (hf j).1
    have hA₀ : ∀ᵐ x ∂m.restrict Sᶜ, ∀ j, ((f j : E.domain) : RealLp m p) x = 0 :=
      ae_all_iff.2 fun j ↦ (hf j).2
    constructor
    · filter_upwards [hA₁, ae_restrict_of_ae (s := K) hn] with x hx hlim
      exact isClosed_singleton.mem_of_tendsto hlim (Eventually.of_forall fun j ↦ hx (n j))
    · filter_upwards [hA₀, ae_restrict_of_ae (s := Sᶜ) hn] with x hx hlim
      exact isClosed_singleton.mem_of_tendsto hlim (Eventually.of_forall fun j ↦ hx (n j))
  obtain ⟨x, hx⟩ := hProper
  obtain ⟨r, hr, hrS⟩ := Metric.mem_nhds_iff.mp (hS.isClosed.isOpen_compl.mem_nhds hx)
  obtain ⟨R, hR, hSR⟩ := hS.isBounded.subset_ball_lt r x
  have hVS : ball x r ⊆ ball x R := ball_subset_ball hR.le
  obtain ⟨D, hD, hGraph⟩ := E.exists_graphNorm_le_root_of_zero_off_ball_and_on
    hPI x (hr.trans hR) measurableSet_ball hVS (measure_ball_pos m x hr)
  have hz (f g : E.domain) (hf : f ∈ C) (hg : g ∈ C) :
      ((f - g : E.domain) : RealLp m p) =ᵐ[m.restrict Sᶜ] (fun _ ↦ 0) := by
    filter_upwards [ae_restrict_of_ae (s := Sᶜ) (Lp.coeFn_sub f.val g.val), hf.2, hg.2] with x hx hf hg
    change (f.val - g.val : RealLp m p) x = _
    simp only [hx, Pi.sub_apply, hf, hg, sub_self]
  obtain ⟨f, hf, hMin⟩ := E.exists_root_minimizer C hTest hConv hClosed hD (fun f hf g hg ↦ by
    exact hGraph (f - g) ((hz f g hf hg).filter_mono
      (ae_mono (Measure.restrict_mono (compl_subset_compl.mpr hSR) le_rfl)))
      ((hz f g hf hg).filter_mono (ae_mono (Measure.restrict_mono hrS le_rfl))))
  let clip := fun t : ℝ ↦ min (max t 0) 1
  have hclip : LipschitzWith 1 clip := (LipschitzWith.id.max_const 0).min_const 1
  have hclip₀ : clip 0 = 0 := by norm_num [clip]
  have hclip₁ : clip 1 = 1 := by norm_num [clip]
  obtain ⟨h, hh, hRoot⟩ := E.exists_lipschitz_one_comp f (ae_eq_refl (f : RealLp m p)) clip hclip hclip₀
  have hhC : h ∈ C := by
    constructor
    · filter_upwards [ae_restrict_of_ae (s := K) hh, hf.1] with x hx hfx
      rw [hx, comp_apply, hfx, hclip₁]
    · filter_upwards [ae_restrict_of_ae (s := Sᶜ) hh, hf.2] with x hx hfx
      rw [hx, comp_apply, hfx, hclip₀]
  have hEh (g : E.domain) (hg : g ∈ C) :
      (E.energy h : ℝ) ≤ (E.energy g : ℝ) := by
    rw [E.energy_eq_root_rpow, E.energy_eq_root_rpow]
    apply Real.rpow_le_rpow (apply_nonneg _ _) _ (zero_lt_one.trans E.one_lt).le
    have he : E.rootSeminorm h ≤ E.rootSeminorm f := by
      rw [E.rootSeminorm_apply h, E.rootSeminorm_apply f]
      exact Real.rpow_le_rpow (NNReal.coe_nonneg _) (NNReal.coe_le_coe.mpr hRoot)
        (inv_nonneg.mpr (zero_lt_one.trans E.one_lt).le)
    exact he.trans (hMin g hg)
  refine ⟨h, hhC.1, hhC.2, ?_, ?_⟩
  · filter_upwards [hh] with x hx
    rw [hx]
    exact ⟨le_min (le_max_right _ _) zero_le_one, min_le_right _ _⟩
  · intro v hv
    have hG (t : ℝ) : h + t • v.domainElement ∈ C := by
      have he : ((h + t • v.domainElement : E.domain) : RealLp m p) =ᵐ[m]
          (fun x ↦ (h : RealLp m p) x + t * v.toFun x) := by
        filter_upwards [ae_lin t v.domainElement h, v.ae_eq] with x hx hvx
        rw [add_comm h]
        change _ = _
        rw [hx, hvx, add_comm]
      constructor
      · filter_upwards [ae_restrict_of_ae (s := K) he, hhC.1, ae_restrict_mem hK] with x hx hU hxK
        have h0 : v.toFun x = 0 := notMem_support.mp fun hn ↦ (hv hn).2 hxK
        simp only [hx, hU, h0, mul_zero, add_zero]
      · filter_upwards [ae_restrict_of_ae (s := Sᶜ) he, hhC.2,
          ae_restrict_mem hS.isClosed.measurableSet.compl] with x hx hU hxS
        have h0 : v.toFun x = 0 := notMem_support.mp fun hn ↦ hxS (hv hn).1
        simp only [hx, hU, h0, mul_zero, add_zero]
    have hloc : IsLocalMin (fun t : ℝ ↦ (E.energy (h + t • v.domainElement) : ℝ)) 0 := by
      apply Eventually.of_forall
      intro t
      simpa only [zero_smul, add_zero] using hEh _ (hG t)
    have hd := hloc.hasDerivAt_eq_zero (E.hasDerivAt_energy_of_energyDerivativeMeasure h v.domainElement)
    exact (mul_eq_zero.mp hd).resolve_left (zero_lt_one.trans E.one_lt).ne'

end WalkDimensions.PEnergy
