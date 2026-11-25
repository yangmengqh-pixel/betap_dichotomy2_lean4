import WalkDimensions.EnergyClosedness

/-!
# Energy minimizers on closed convex sets

Clarkson's inequality makes near-minimizers Cauchy in the energy seminorm.
A comparison with the graph norm on feasible differences gives existence.
-/

open Filter MeasureTheory Metric Set
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {m : Measure X} [IsFiniteMeasureOnCompacts m] {p : ℝ} (E : PEnergy m p)

theorem exists_root_minimizer (C : Set E.domain) (hC : C.Nonempty) (hconv : Convex ℝ C)
    (hclosed : letI := E.graphSeminorm.toAddGroupSeminorm.toSeminormedAddCommGroup; IsClosed C)
    {K : ℝ} (hK : 0 < K) (hcomp : ∀ f ∈ C, ∀ g ∈ C,
      E.graphSeminorm (f - g) ≤ K * E.rootSeminorm (f - g)) :
    ∃ f ∈ C, ∀ g ∈ C, E.rootSeminorm f ≤ E.rootSeminorm g := by
  let : SeminormedAddCommGroup E.domain :=
    E.graphSeminorm.toAddGroupSeminorm.toSeminormedAddCommGroup
  let : CompleteSpace E.domain := E.graph_complete
  have hroot : Continuous E.rootSeminorm :=
    Seminorm.continuous_of_le (show Continuous E.graphSeminorm from continuous_norm)
      E.rootSeminorm_le_graphSeminorm
  obtain ⟨q, hq, hClarkson⟩ := E.exists_clarkson_power
  let a := sInf (E.rootSeminorm '' C)
  have hne : (E.rootSeminorm '' C).Nonempty := hC.image _
  have hbelow : BddBelow (E.rootSeminorm '' C) :=
    ⟨0, fun _ ⟨f, _, hf⟩ ↦ hf ▸ apply_nonneg E.rootSeminorm f⟩
  have ha : 0 ≤ a := le_csInf hne (fun _ ⟨f, _, hf⟩ ↦ hf ▸ apply_nonneg E.rootSeminorm f)
  have hle {f : E.domain} (hf : f ∈ C) : a ≤ E.rootSeminorm f :=
    csInf_le hbelow (mem_image_of_mem _ hf)
  let e : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have hepos (n : ℕ) : 0 < e n := by dsimp [e]; positivity
  have he_anti : Antitone e := by
    intro n k hnk
    apply one_div_le_one_div_of_le (by positivity)
    exact add_le_add_left (Nat.cast_le.mpr hnk) 1
  have helim : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hnear (n : ℕ) : ∃ f ∈ C, E.rootSeminorm f < a + e n := by
    obtain ⟨_, ⟨f, hf, rfl⟩, hlt⟩ :=
      exists_lt_of_csInf_lt hne (lt_add_of_pos_right a (hepos n))
    exact ⟨f, hf, hlt⟩
  choose f hf hfa using hnear
  let b : ℕ → ℝ := fun n ↦ (2 * (a + e n)) ^ q - (2 * a) ^ q
  have hb : Tendsto b atTop (𝓝 0) := by
    have hcont : Continuous (fun t : ℝ ↦ (2 * (a + t)) ^ q - (2 * a) ^ q) := by
      apply ((Real.continuous_rpow_const hq.le).comp _).sub continuous_const
      fun_prop
    simpa [Function.comp_def, b] using (hcont.tendsto 0).comp helim
  have hdiff {n k l : ℕ} (hk : n ≤ k) (hl : n ≤ l) :
      E.rootSeminorm (f k - f l) ^ q ≤ b n := by
    have hmid : (1 / 2 : ℝ) • (f k + f l) ∈ C := by
      rw [smul_add]
      exact hconv (hf k) (hf l) (by norm_num) (by norm_num) (by norm_num)
    have hm := hle hmid
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hm
    have hmid' : (2 * a) ^ q ≤ E.rootSeminorm (f k + f l) ^ q :=
      Real.rpow_le_rpow (by positivity) (by linarith only [hm]) hq.le
    have hh := hClarkson (f k) (f l) (a + e n) (by positivity)
      ((hfa k).le.trans (add_le_add_right (he_anti hk) _))
      ((hfa l).le.trans (add_le_add_right (he_anti hl) _))
    change _ ≤ (2 * (a + e n)) ^ q - (2 * a) ^ q
    linarith only [hh, hmid']
  have hCauchy : CauchySeq f := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    have hδ : 0 < ε / K := div_pos hε hK
    obtain ⟨N, hN⟩ := eventually_atTop.1
      (hb.eventually_lt_const (Real.rpow_pos_of_pos hδ q))
    refine ⟨N, fun k hk l hl ↦ ?_⟩
    have hrootlt : E.rootSeminorm (f k - f l) < ε / K :=
      (Real.rpow_lt_rpow_iff (apply_nonneg _ _) hδ.le hq).1
        ((hdiff hk hl).trans_lt (hN N le_rfl))
    rw [dist_eq_norm]
    change E.graphSeminorm (f k - f l) < ε
    exact (hcomp (f k) (hf k) (f l) (hf l)).trans_lt (by
      rwa [mul_comm, ← lt_div_iff₀ hK])
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete hCauchy
  have hgc : g ∈ C := hclosed.mem_of_tendsto hg (Eventually.of_forall hf)
  have hlim : Tendsto (fun n ↦ E.rootSeminorm (f n)) atTop (𝓝 (E.rootSeminorm g)) :=
    hroot.continuousAt.tendsto.comp hg
  have hga : E.rootSeminorm g ≤ a := by
    apply le_of_tendsto_of_tendsto hlim _ (Eventually.of_forall fun n ↦ (hfa n).le)
    simpa only [add_zero] using tendsto_const_nhds.add helim
  exact ⟨g, hgc, fun f hf ↦ hga.trans (hle hf)⟩

end WalkDimensions.PEnergy
