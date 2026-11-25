import WalkDimensions.EnergyClosedness

/-!
# Strong energy convergence from ambient convergence and norm convergence

The ambient lower semicontinuity bound controls the energy of midpoints.
Uniform convexity then gives convergence of the energy of differences.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {m : Measure X} [IsFiniteMeasureOnCompacts m] {p : ℝ} (E : PEnergy m p)

theorem rootSeminorm_le_of_norm_sub_tendsto {g : ℕ → E.domain} {f : E.domain} {M : ℝ}
    (hLp : Tendsto (fun n ↦ ‖(g n : RealLp m p) - (f : RealLp m p)‖) atTop (𝓝 0))
    (hroot : ∀ᶠ n in atTop, E.rootSeminorm (g n) ≤ M) :
    E.rootSeminorm f ≤ M := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt.le⟩
  obtain ⟨h, hh, hE⟩ := E.exists_of_bounded_lp_approximation (f : RealLp m p) (M := M)
    (fun ε hε ↦ by
      obtain ⟨n, hN, hG⟩ := ((hLp.eventually_lt_const hε).and hroot).exists
      exact ⟨g n, hN, hG⟩)
  exact (Subtype.ext hh : h = f) ▸ hE

theorem eventually_le_rootSeminorm_of_norm_sub_tendsto {g : ℕ → E.domain} {f : E.domain}
    {L : ℝ} (hL : L < E.rootSeminorm f)
    (hLp : Tendsto (fun n ↦ ‖(g n : RealLp m p) - (f : RealLp m p)‖) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, L ≤ E.rootSeminorm (g n) := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt.le⟩
  have hCl := E.isClosed_root_sublevel_in_lp L
  have hf : (f : RealLp m p) ∉ {u : RealLp m p |
      ∃ h : E.domain, (h : RealLp m p) = u ∧ E.rootSeminorm h ≤ L} := by
    rintro ⟨h, he, hH⟩
    exact hL.not_ge ((Subtype.ext he : h = f) ▸ hH)
  have ht : Tendsto (fun n ↦ (g n : RealLp m p)) atTop (𝓝 (f : RealLp m p)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    simpa only [dist_eq_norm] using hLp.eventually_lt_const hε
  filter_upwards [ht (hCl.isOpen_compl.mem_nhds hf)] with n hn
  by_contra! h
  exact hn ⟨g n, rfl, h.le⟩

theorem tendsto_root_sub_of_norm_sub_tendsto_of_root_tendsto {g : ℕ → E.domain} {f : E.domain}
    (hLp : Tendsto (fun n ↦ ‖(g n : RealLp m p) - (f : RealLp m p)‖) atTop (𝓝 0))
    (hroot : Tendsto (fun n ↦ E.rootSeminorm (g n)) atTop (𝓝 (E.rootSeminorm f))) :
    Tendsto (fun n ↦ E.rootSeminorm (g n - f)) atTop (𝓝 0) := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt.le⟩
  let R := E.rootSeminorm f
  have hR : 0 ≤ R := apply_nonneg _ _
  obtain ⟨q, hq, hClarkson⟩ := E.exists_clarkson_power
  let w (n : ℕ) := (1 / 2 : ℝ) • (g n + f)
  have hw : Tendsto (fun n ↦ ‖(w n : RealLp m p) - (f : RealLp m p)‖) atTop (𝓝 0) := by
    have hw' (n : ℕ) : (w n : RealLp m p) - (f : RealLp m p) =
        (1 / 2 : ℝ) • ((g n : RealLp m p) - (f : RealLp m p)) := by
      change (1 / 2 : ℝ) • ((g n : RealLp m p) + (f : RealLp m p)) - (f : RealLp m p) = _
      module
    simp_rw [hw', norm_smul_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    simpa only [mul_zero] using hLp.const_mul (1 / 2)
  let B (η : ℝ) := (2 * (R + η)) ^ q - (2 * max 0 (R - η)) ^ q
  have hB : Tendsto B (𝓝 0) (𝓝 0) := by
    have hC : Continuous B := by
      dsimp only [B]
      exact ((continuous_const.mul (continuous_const.add continuous_id)).rpow_const
        (fun _ ↦ Or.inr hq.le)).sub
        ((continuous_const.mul (continuous_const.max (continuous_const.sub continuous_id))).rpow_const
          (fun _ ↦ Or.inr hq.le))
    simpa only [B, add_zero, sub_zero, max_eq_right hR, sub_self] using hC.tendsto 0
  apply tendsto_order.2
  refine ⟨fun a ha ↦ Eventually.of_forall (fun _ ↦ ha.trans_le (apply_nonneg _ _)),
    fun ε hε ↦ ?_⟩
  have hevent : ∀ᶠ η : ℝ in 𝓝[>] 0, B η < ε ^ q :=
    (hB.eventually_lt_const (Real.rpow_pos_of_pos hε q)).filter_mono nhdsWithin_le_nhds
  obtain ⟨η, hη, hηB⟩ := (eventually_mem_nhdsWithin.and hevent).exists
  have hηpos : 0 < η := hη
  let L := max 0 (R - η)
  let M := R + η
  have hL : 0 ≤ L := le_max_left _ _
  have hM : 0 ≤ M := add_nonneg hR hηpos.le
  have hLM : L ≤ M := max_le hM (by dsimp [M]; linarith only [hηpos])
  have hLo : ∀ᶠ n in atTop, L ≤ E.rootSeminorm (w n) := by
    by_cases h : R - η ≤ 0
    · exact Eventually.of_forall (fun n ↦ (show L = 0 from max_eq_left h).le.trans (apply_nonneg _ _))
    · have h' : L < R := by
        dsimp [L]
        rw [max_eq_right (le_of_not_ge h)]
        linarith only [hηpos]
      exact E.eventually_le_rootSeminorm_of_norm_sub_tendsto h' hw
  have hHi : ∀ᶠ n in atTop, E.rootSeminorm (g n) < M :=
    hroot.eventually_lt_const (lt_add_of_pos_right _ hηpos)
  filter_upwards [hLo, hHi] with n hLn hMn
  apply (Real.rpow_lt_rpow_iff (apply_nonneg _ _) hε.le hq).mp
  have hBound := hClarkson (g n) f M hM hMn.le (le_add_of_nonneg_right hηpos.le)
  have hMid : (2 * L) ^ q ≤ E.rootSeminorm (g n + f) ^ q := by
    change L ≤ E.rootSeminorm ((1 / 2 : ℝ) • (g n + f)) at hLn
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hLn
    exact Real.rpow_le_rpow (by positivity) (by linarith only [hLn]) hq.le
  have hle : E.rootSeminorm (g n - f) ^ q ≤ B η := by
    dsimp only [B]
    change _ ≤ (2 * M) ^ q - (2 * L) ^ q
    linarith only [hBound, hMid]
  exact hle.trans_lt hηB

end WalkDimensions.PEnergy
