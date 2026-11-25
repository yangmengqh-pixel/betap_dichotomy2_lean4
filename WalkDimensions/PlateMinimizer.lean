import WalkDimensions.CompactEnergyLimit
import WalkDimensions.EnergyEvaluation
import WalkDimensions.EnergyMinimizer
import WalkDimensions.Morrey

/-!
# Minimization with prescribed plate values

In the supercritical range, Morrey's estimate makes point evaluation
continuous in the energy graph norm and controls differences supported
on the outer plate's complement.
-/

open Filter MeasureTheory Metric Set
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SecondCountableTopology X] {m : Measure X}
  [IsFiniteMeasureOnCompacts m] [m.IsOpenPosMeasure] {p : ℝ} (E : PEnergy m p)

/-- Admissibility with pointwise values for a compactly supported
continuous representative. -/
def UnitPlate (K S : Set X) (f : E.domain) (u : X → ℝ) : Prop :=
  Continuous u ∧ (f : RealLp m p) =ᵐ[m] u ∧ (∀ x, u x ∈ Icc (0 : ℝ) 1) ∧
    EqOn u (fun _ ↦ 1) K ∧ EqOn u (fun _ ↦ 0) Sᶜ

theorem exists_unitPlate_minimizer {d β : ℝ} (hvol : AhlforsRegular m d)
    (hβ : d < β) {Γ : E.domain → Measure X} (hPI : E.Poincare Γ β)
    (hΓ : ∀ f, Γ f univ = (E.energy f : ℝ≥0∞))
    {K S : Set X} (hS : IsCompact S) (hSproper : Sᶜ.Nonempty)
    (hne : ∃ f u, E.UnitPlate K S f u) :
    ∃ f u, E.UnitPlate K S f u ∧ ∀ g w, E.UnitPlate K S g w → E.energy f ≤ E.energy g := by
  classical
  let : SeminormedAddCommGroup E.domain :=
    E.graphSeminorm.toAddGroupSeminorm.toSeminormedAddCommGroup
  obtain ⟨H, hH, hrep⟩ := E.exists_holder_representative hvol hβ hPI hΓ
  choose v hv hfv hbound using hrep
  let a := (β - d) / p
  have hp : 0 < p := zero_lt_one.trans E.one_lt
  have ha : 0 < a := div_pos (sub_pos.mpr hβ) hp
  have hcomb (b c : ℝ) (f g : E.domain) :
      v (b • f + c • g) = fun x ↦ b * v f x + c * v g x := by
    have hAE : ((b • f + c • g : E.domain) : RealLp m p) =ᵐ[m]
        fun x ↦ b * v f x + c * v g x := by
      filter_upwards [Lp.coeFn_add (b • (f : RealLp m p)) (c • (g : RealLp m p)),
        Lp.coeFn_smul b (f : RealLp m p), Lp.coeFn_smul c (g : RealLp m p), hfv f, hfv g]
        with x hx hb hc hf hg
      change (b • (f : RealLp m p) + c • (g : RealLp m p)) x = _
      rw [hx, Pi.add_apply, hb, hc, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, hf, hg]
    exact Measure.eq_of_ae_eq ((hfv _).symm.trans hAE) (hv _)
      ((continuous_const.mul (hv f)).add (continuous_const.mul (hv g)))
  have hsub (f g : E.domain) : v (f - g) = fun x ↦ v f x - v g x := by
    simpa only [sub_eq_add_neg, one_smul, neg_one_smul, one_mul, neg_one_mul] using hcomb 1 (-1) f g
  have hEval (x : X) : Continuous (fun f : E.domain ↦ v f x) := by
    let B := ball x 1
    let M := (m.real B) ^ (-p⁻¹)
    have hM : 0 ≤ M := by dsimp [M]; positivity
    have hnorm (f : E.domain) : |v f x| ≤ (H + M) * E.graphSeminorm f :=
      E.abs_apply_le_graphSeminorm (hfv f) hH.le ha.le (hbound f) x
    apply Metric.continuous_iff.mpr
    intro f ε hε
    have hHM : 0 < H + M := add_pos_of_pos_of_nonneg hH hM
    refine ⟨ε / (H + M), div_pos hε hHM, fun g hg ↦ ?_⟩
    rw [dist_eq_norm] at hg
    change E.graphSeminorm (g - f) < _ at hg
    rw [Real.dist_eq]
    have h := hnorm (g - f)
    rw [hsub g f] at h
    exact h.trans_lt (by
      calc
        _ < (H + M) * (ε / (H + M)) := mul_lt_mul_of_pos_left hg hHM
        _ = _ := by field_simp)
  let F : Set E.domain := {f | (∀ x, v f x ∈ Icc (0 : ℝ) 1) ∧
      EqOn (v f) (fun _ ↦ 1) K ∧ EqOn (v f) (fun _ ↦ 0) Sᶜ}
  have hUnit {f : E.domain} {u : X → ℝ} (hf : E.UnitPlate K S f u) : f ∈ F := by
    obtain ⟨hu, hfu, hunit, h1, h0⟩ := hf
    have he := Measure.eq_of_ae_eq ((hfv f).symm.trans hfu) (hv f) hu
    change (∀ x, v f x ∈ Icc (0 : ℝ) 1) ∧ EqOn (v f) (fun _ ↦ 1) K ∧
      EqOn (v f) (fun _ ↦ 0) Sᶜ
    rw [he]
    exact ⟨hunit, h1, h0⟩
  have hFne : F.Nonempty := by
    obtain ⟨f, u, hf⟩ := hne
    exact ⟨f, hUnit hf⟩
  have hFconv : Convex ℝ F := by
    intro f hf g hg b c hb hc hbc
    obtain ⟨hfU, hf1, hf0⟩ := hf
    obtain ⟨hgU, hg1, hg0⟩ := hg
    change (∀ x, v (b • f + c • g) x ∈ Icc (0 : ℝ) 1) ∧ _ ∧ _
    rw [hcomb]
    refine ⟨fun x ↦ convex_Icc _ _ (hfU x) (hgU x) hb hc hbc, ?_, ?_⟩
    · intro x hx
      simp only [hf1 hx, hg1 hx, mul_one, hbc]
    · intro x hx
      simp only [hf0 hx, hg0 hx, mul_zero, add_zero]
  have hFclosed : IsClosed F := by
    apply IsSeqClosed.isClosed
    intro u f hu hlim
    have hpoint (x : X) : Tendsto (fun n ↦ v (u n) x) atTop (𝓝 (v f x)) :=
      ((hEval x).tendsto _).comp hlim
    refine ⟨fun x ↦ isClosed_Icc.mem_of_tendsto (hpoint x) (Eventually.of_forall fun n ↦ (hu n).1 x),
      ?_, ?_⟩
    · intro x hx
      exact isClosed_singleton.mem_of_tendsto (hpoint x) (Eventually.of_forall fun n ↦ (hu n).2.1 hx)
    · intro x hx
      exact isClosed_singleton.mem_of_tendsto (hpoint x) (Eventually.of_forall fun n ↦ (hu n).2.2 hx)
  obtain ⟨x₀, hx₀⟩ := hSproper
  obtain ⟨R, hR, hSR⟩ := hS.isBounded.subset_closedBall_lt 0 x₀
  let D := (m.real S) ^ p⁻¹
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hC : 0 < 1 + H * R ^ a * D := by positivity
  have hcomp (f : E.domain) (hf : f ∈ F) (g : E.domain) (hg : g ∈ F) :
      E.graphSeminorm (f - g) ≤ (1 + H * R ^ a * D) * E.rootSeminorm (f - g) := by
    let w := f - g
    have hz (x : X) (hx : x ∉ S) : v w x = 0 := by
      dsimp only [w]
      simp only [hsub, hf.2.2 hx, hg.2.2 hx, sub_zero]
    have hpoint (x : X) :
        |v w x| ≤ S.indicator (fun _ ↦ H * E.rootSeminorm w * R ^ a) x := by
      by_cases hx : x ∈ S
      · rw [indicator_of_mem hx]
        have h := hbound w x x₀
        rw [hz x₀ hx₀, sub_zero] at h
        exact h.trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow dist_nonneg (mem_closedBall.mp (hSR hx)) ha.le) (by positivity))
      · rw [indicator_of_notMem hx, hz x hx, abs_zero]
    have hlp := norm_realLp_le_of_ae_abs_bound hp (w : RealLp m p) hS.isClosed.measurableSet
      (hS.measure_lt_top (μ := m)).ne (b := H * E.rootSeminorm w * R ^ a)
      (by positivity) ((hfv w).mono fun x hx ↦ by rw [hx]; exact hpoint x)
    calc
      E.graphSeminorm w ≤ E.rootSeminorm w + ‖(w : RealLp m p)‖ := E.graphSeminorm_le_add _
      _ ≤ E.rootSeminorm w + (H * E.rootSeminorm w * R ^ a) * D := add_le_add_right hlp _
      _ = _ := by ring
  obtain ⟨f, hf, hfmin⟩ := E.exists_root_minimizer F hFne hFconv hFclosed hC hcomp
  refine ⟨f, v f, ⟨hv f, hfv f, hf.1, hf.2⟩, fun g u hu ↦ ?_⟩
  apply NNReal.coe_le_coe.mp
  rw [E.energy_eq_root_rpow, E.energy_eq_root_rpow]
  exact Real.rpow_le_rpow (apply_nonneg _ _) (hfmin g (hUnit hu)) hp.le

end WalkDimensions.PEnergy
