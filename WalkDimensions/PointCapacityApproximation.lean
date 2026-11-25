import WalkDimensions.EnergyEvaluation
import WalkDimensions.EnergyTruncation
import WalkDimensions.PointResistance

/-!
# Point values and compact capacity approximants

Scalar clipping turns exact point values into the neighbourhood conditions
in the definition of capacity. In the supercritical range, Morrey's
estimate allows the approximants to be chosen from the continuous core.
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {m : Measure X} [IsFiniteMeasureOnCompacts m] {p : ℝ} (E : PEnergy m p)

theorem singleton_capacity_le_of_point_values {f : E.domain} {u : X → ℝ}
    (hfu : (f : RealLp m p) =ᵐ[m] u) (hu : Continuous u) {x y : X}
    (hx : u x = 1) (hy : u y = 0) :
    E.capacity {x} {y} ≤ (E.energy f : ℝ≥0∞) := by
  let B (ε : ℝ) := ENNReal.ofReal ((1 - ε - ε) ^ (-p) * (E.energy f : ℝ))
  have hInner : ContinuousAt (fun ε : ℝ ↦ 1 - ε - ε) 0 := by fun_prop
  have hcont : ContinuousAt B 0 := ENNReal.continuous_ofReal.continuousAt.comp
    ((hInner.rpow_const (p := -p) (Or.inl (by norm_num))).mul continuousAt_const)
  have hB₀ : B 0 = (E.energy f : ℝ≥0∞) := by
    simp only [B, sub_zero, Real.one_rpow, one_mul, ENNReal.ofReal_coe_nnreal]
  rw [← hB₀]
  apply ge_of_tendsto (hcont.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ))))
  filter_upwards [Ioo_mem_nhdsGT (show 0 < (1 / 2 : ℝ) by norm_num)] with ε hε
  have hab : ε < 1 - ε := by linarith only [hε.2]
  obtain ⟨g, hg, hgE⟩ := E.exists_unitClip_comp f hfu hε.1.le hab
  let U := {z | 1 - ε < u z}
  let V := {z | u z < ε}
  have hadm : E.CapacityAdmissible {x} {y} g := by
    refine ⟨unitClip ε (1 - ε) ∘ u, hg, U, V,
      isOpen_lt continuous_const hu, isOpen_lt hu continuous_const, ?_, ?_, ?_, ?_⟩
    · apply singleton_subset_iff.mpr
      change 1 - ε < u x
      rw [hx]
      linarith only [hε.1]
    · apply singleton_subset_iff.mpr
      change u y < ε
      rw [hy]
      exact hε.1
    · exact fun z hz ↦ unitClip_eq_one hab (show 1 - ε < u z from hz).le
    · exact fun z hz ↦ unitClip_eq_zero hab (show u z < ε from hz).le
  have hcap : E.capacity {x} {y} ≤ (E.energy g : ℝ≥0∞) :=
    (iInf_le _ g).trans (iInf_le _ hadm)
  exact hcap.trans (by
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal hgE)

variable [ProperSpace X] [SecondCountableTopology X] [m.IsOpenPosMeasure]

theorem exists_compact_singleton_capacity_approximant {d β : ℝ}
    (hvol : AhlforsRegular m d) (hβ : d < β) {Γ : E.domain → Measure X}
    (hPI : E.Poincare Γ β) (hΓ : ∀ f, Γ f univ = (E.energy f : ℝ≥0∞))
    {x y : X} {b : ℝ} (hb : E.capacity {x} {y} < ENNReal.ofReal b) :
    ∃ (g : E.domain) (u : X → ℝ), Continuous u ∧ HasCompactSupport u ∧
      (g : RealLp m p) =ᵐ[m] u ∧ (∀ z, u z ∈ Icc (0 : ℝ) 1) ∧
      u x = 1 ∧ u y = 0 ∧ (E.energy g : ℝ) < b := by
  obtain ⟨f, hadm, hf⟩ := E.exists_admissible_lt_of_capacity_lt hb
  obtain ⟨w, hfw, U, V, hU, hV, hUx, hVy, hw1, hw0⟩ := hadm
  obtain ⟨H, hH, hrep⟩ := E.exists_holder_representative hvol hβ hPI hΓ
  obtain ⟨v, hv, hfv, _⟩ := hrep f
  have hVW := hfv.symm.trans hfw
  have hPlate (S : Set X) (hS : IsOpen S) (c : ℝ) (h : EqOn w (fun _ ↦ c) S) :
      EqOn v (fun _ ↦ c) S := by
    apply Measure.eqOn_open_of_ae_eq (μ := m) _ hS hv.continuousOn continuousOn_const
    filter_upwards [ae_restrict_of_ae (s := S) hVW, ae_restrict_mem hS.measurableSet] with z hz hzS
    exact hz.trans (h hzS)
  have hx := hPlate U hU 1 hw1 (hUx (mem_singleton x))
  have hy := hPlate V hV 0 hw0 (hVy (mem_singleton y))
  have hp : 0 < p := zero_lt_one.trans E.one_lt
  let s := (β - d) / p
  have hs : 0 < s := div_pos (sub_pos.mpr hβ) hp
  let Dx := H + (m.real (ball x 1)) ^ (-p⁻¹)
  let Dy := H + (m.real (ball y 1)) ^ (-p⁻¹)
  have hDx : 0 < Dx := by dsimp [Dx]; positivity
  have hDy : 0 < Dy := by dsimp [Dy]; positivity
  let a (ε : ℝ) := Dy * ε
  let c (ε : ℝ) := 1 - Dx * ε
  let F (ε : ℝ) := (c ε - a ε) ^ (-p) * (E.rootSeminorm f + ε) ^ p
  have hFcont : ContinuousAt F 0 := by
    have hD : ContinuousAt (fun ε ↦ c ε - a ε) 0 := by dsimp [a, c]; fun_prop
    have hS : ContinuousAt (fun ε ↦ E.rootSeminorm f + ε) 0 := continuousAt_const.add continuousAt_id
    exact (hD.rpow_const (Or.inl (by simp [a, c]))).mul (hS.rpow_const (Or.inr hp.le))
  have hF₀ : F 0 = (E.energy f : ℝ) := by
    simp only [F, a, c, mul_zero, sub_zero, Real.one_rpow, add_zero, one_mul, E.energy_eq_root_rpow]
  have hfb : (E.energy f : ℝ) < b := by
    rw [← ENNReal.ofReal_coe_nnreal] at hf
    exact (ENNReal.ofReal_lt_ofReal_iff'.mp hf).1
  have hFsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), F ε < b :=
    ((tendsto_order.1 hFcont.tendsto).2 b (hF₀ ▸ hfb)).filter_mono (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hAC : ∀ᶠ ε in 𝓝[>] (0 : ℝ), a ε < c ε := by
    have hcont : ContinuousAt (fun ε ↦ c ε - a ε) 0 := by dsimp [a, c]; fun_prop
    have h := ((tendsto_order.1 hcont.tendsto).1 0 (by simp [a, c])).filter_mono (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    exact h.mono fun ε hε ↦ sub_pos.mp hε
  obtain ⟨ε, hε, hεF, hεAC⟩ := (eventually_mem_nhdsWithin.and (hFsmall.and hAC)).exists
  obtain ⟨z, hz, hzc, hmz, happrox⟩ := E.regular_graph f ε hε
  let fz : E.domain := ⟨continuousLp p z hz hzc, hmz⟩
  have hfz : (fz : RealLp m p) =ᵐ[m] z := MemLp.coeFn_toLp (hz.memLp_of_hasCompactSupport hzc)
  obtain ⟨w', hw', hfw', hbound⟩ := hrep (fz - f)
  have hAE : ((fz - f : E.domain) : RealLp m p) =ᵐ[m] fun t ↦ z t - v t := by
    filter_upwards [Lp.coeFn_sub (fz : RealLp m p) (f : RealLp m p), hfz, hfv] with t ht htz htv
    change ((fz : RealLp m p) - (f : RealLp m p)) t = _
    rw [ht, Pi.sub_apply, htz, htv]
  have hEq := Measure.eq_of_ae_eq (hfw'.symm.trans hAE) hw' (hz.sub hv)
  have herror (t : X) :
      |z t - v t| ≤ (H + (m.real (ball t 1)) ^ (-p⁻¹)) * E.graphSeminorm (fz - f) := by
    simpa only [hEq] using E.abs_apply_le_graphSeminorm hfw' hH.le hs.le hbound t
  have hx' : c ε ≤ z x := by
    have h := (abs_le.mp ((herror x).trans
      (mul_le_mul_of_nonneg_left happrox.le hDx.le))).1
    rw [hx] at h
    dsimp only [c]
    linarith only [h]
  have hy' : z y ≤ a ε := by
    have h := (abs_le.mp ((herror y).trans
      (mul_le_mul_of_nonneg_left happrox.le hDy.le))).2
    rw [hy, sub_zero] at h
    exact h
  have ha₀ : 0 ≤ a ε := mul_nonneg hDy.le hε.le
  obtain ⟨g, hg, hgE⟩ := E.exists_unitClip_comp fz hfz ha₀ hεAC
  let u := unitClip (a ε) (c ε) ∘ z
  have hu : Continuous u := ((hz.sub continuous_const).div_const _).max continuous_const |>.min continuous_const
  have huc : HasCompactSupport u := hzc.comp_left (unitClip_eq_zero hεAC ha₀)
  refine ⟨g, u, hu, huc, hg, fun t ↦ unitClip_mem_Icc _ _ _, unitClip_eq_one hεAC hx',
    unitClip_eq_zero hεAC hy', ?_⟩
  have hnorm : E.rootSeminorm fz ≤ E.rootSeminorm f + ε := by
    have h := E.rootSeminorm.add_le' (fz - f) f
    rw [sub_add_cancel, add_comm] at h
    exact h.trans (add_le_add_right ((E.rootSeminorm_le_graphSeminorm _).trans happrox.le) _)
  apply (hgE.trans ?_).trans_lt hεF
  rw [E.energy_eq_root_rpow]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (apply_nonneg _ _) hnorm hp.le)
    (Real.rpow_nonneg (sub_nonneg.mpr hεAC.le) _)

end WalkDimensions.PEnergy
