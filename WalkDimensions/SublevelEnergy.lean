import WalkDimensions.OscillationShift

/-!
# Sublevel distribution of energy

The distribution uses the limit of localized oscillation energies.
Its order and one-sided continuity follow from the shifted ramp estimates.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {p : ℝ} (E : PEnergy μ p)

/-- A continuous compactly supported representative of an energy-domain element. -/
structure CompactCore where
  domainElement : E.domain
  toFun : X → ℝ
  ae_eq : (domainElement : RealLp μ p) =ᵐ[μ] toFun
  continuous : Continuous toFun
  compactSupport : HasCompactSupport toFun

variable {E}

private theorem CompactCore.exists_oscillation (f g : E.CompactCore) (a : ℝ) (n : ℕ) :
    ∃ w : E.domain, (w : RealLp μ p) =ᵐ[μ] fun x ↦ min (sawtooth (oscillationWidth n) (f.toFun x))
      (sublevelRamp (oscillationWidth n) a (g.toFun x)) := by
  obtain ⟨w, hw, _, _, _⟩ :=
  E.exists_localized_oscillation f.domainElement g.domainElement f.ae_eq g.ae_eq
      f.continuous g.continuous f.compactSupport (oscillationWidth n) a
  exact ⟨w, hw⟩

noncomputable def CompactCore.oscillation (f g : E.CompactCore) (a : ℝ) (n : ℕ) :
    E.domain := (f.exists_oscillation g a n).choose

theorem CompactCore.oscillation_ae (f g : E.CompactCore) (a : ℝ) (n : ℕ) :
    (f.oscillation g a n : RealLp μ p) =ᵐ[μ] fun x ↦
      min (sawtooth (oscillationWidth n) (f.toFun x)) (sublevelRamp (oscillationWidth n) a (g.toFun x)) :=
  (f.exists_oscillation g a n).choose_spec

/-- The energy seminorm on the sublevel set indicated by the threshold. -/
noncomputable def CompactCore.sublevelEnergyRoot (f g : E.CompactCore) (a : ℝ) : ℝ :=
  ⨅ n, E.rootSeminorm (f.oscillation g a n)

theorem CompactCore.tendsto_sublevelEnergyRoot (f g : E.CompactCore) (a : ℝ) :
    Tendsto (fun n ↦ E.rootSeminorm (f.oscillation g a n)) atTop (𝓝 (f.sublevelEnergyRoot g a)) :=
  E.tendsto_root_localized_oscillation f.domainElement g.domainElement f.ae_eq g.ae_eq
    f.continuous g.continuous f.compactSupport g.compactSupport a _ (f.oscillation_ae g a)

theorem CompactCore.sublevelEnergyRoot_nonneg (f g : E.CompactCore) (a : ℝ) :
    0 ≤ f.sublevelEnergyRoot g a :=
  le_ciInf fun _ ↦ apply_nonneg _ _

theorem CompactCore.sublevelEnergyRoot_le (f g : E.CompactCore) (a : ℝ) (n : ℕ) :
    f.sublevelEnergyRoot g a ≤ E.rootSeminorm (f.oscillation g a n) :=
  ciInf_le ⟨0, forall_mem_range.mpr (fun _ ↦ apply_nonneg _ _)⟩ n

theorem CompactCore.monotone_sublevelEnergyRoot (f g : E.CompactCore) :
    Monotone (f.sublevelEnergyRoot g) := by
  intro a b hab
  obtain ⟨r, hr, hlim⟩ := E.exists_ramp_graph_tendsto_zero g.domainElement g.ae_eq g.compactSupport
    a oscillationWidth (fun n ↦ (oscillationWidth_pos n).le)
    oscillationWidth_antitone tendsto_oscillationWidth
  have hR : Tendsto (fun n ↦ E.rootSeminorm (r n)) atTop (𝓝 0) :=
    squeeze_zero (fun _ ↦ apply_nonneg _ _) (fun n ↦ E.rootSeminorm_le_graphSeminorm (r n)) hlim
  have htend : Tendsto
      (fun n ↦ E.rootSeminorm (f.oscillation g b n) + E.rootSeminorm (r n))
      atTop (𝓝 (f.sublevelEnergyRoot g b)) := by
    simpa only [add_zero] using (f.tendsto_sublevelEnergyRoot g b).add hR
  apply le_of_tendsto_of_tendsto (f.tendsto_sublevelEnergyRoot g a) htend
  refine Eventually.of_forall fun n ↦ ?_
  let ε := oscillationWidth n
  obtain ⟨w, hw, hW⟩ := E.exists_min_add_const (f.oscillation g b n) (r n)
    (f.oscillation_ae g b n) (hr n) (sublevelRamp_nonneg ε a 0)
  have he : w = f.oscillation g a n := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [hw, f.oscillation_ae g a n] with x hx hy
    rw [hx, hy]
    change min (min (sawtooth ε (f.toFun x)) (sublevelRamp ε b (g.toFun x)))
      (offsetRamp ε a (g.toFun x) + sublevelRamp ε a 0) =
        min (sawtooth ε (f.toFun x)) (sublevelRamp ε a (g.toFun x))
    rw [offsetRamp, sub_add_cancel, min_assoc]
    congr 1
    apply min_eq_right
    unfold sublevelRamp
    exact max_le_max (min_le_min (by linarith only [hab]) le_rfl) le_rfl
  simpa only [he] using hW

theorem CompactCore.tendsto_sublevelEnergyRoot_right (f g : E.CompactCore) (a : ℝ) :
    Tendsto (f.sublevelEnergyRoot g) (𝓝[≥] a) (𝓝 (f.sublevelEnergyRoot g a)) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    filter_upwards [self_mem_nhdsWithin (s := Ici a)] with t ht
    exact hb.trans_le (f.monotone_sublevelEnergyRoot g ht)
  · intro b hb
    obtain ⟨c, hac, hcb⟩ := exists_between hb
    obtain ⟨n, hn⟩ :=
      ((f.tendsto_sublevelEnergyRoot g a).eventually_lt_const hac).exists
    let w := f.oscillation g a n
    let w' (k : ℕ) := f.oscillation g (a + oscillationWidth k) n
    have hlim := E.tendsto_graph_localized_oscillation_shift g.domainElement w g.ae_eq
      g.compactSupport f.compactSupport (oscillationWidth_pos n) a w'
      (f.oscillation_ae g a n) (fun k ↦ f.oscillation_ae g (a + oscillationWidth k) n)
    obtain ⟨k, hk⟩ := (hlim.eventually_lt_const (sub_pos.mpr hcb)).exists
    have htriangle := E.rootSeminorm.add_le' (w' k - w) w
    change E.rootSeminorm (w' k - w + w) ≤ E.rootSeminorm (w' k - w) + E.rootSeminorm w
      at htriangle
    rw [sub_add_cancel] at htriangle
    have hW : E.rootSeminorm (w' k) < b := by
      linarith only [htriangle, hk, hn, E.rootSeminorm_le_graphSeminorm (w' k - w)]
    have hNear : Iio (a + oscillationWidth k) ∈ 𝓝[≥] a :=
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (lt_add_of_pos_right _ (oscillationWidth_pos k)))
    filter_upwards [hNear] with t ht
    exact ((f.monotone_sublevelEnergyRoot g (mem_Iio.mp ht).le).trans
      (f.sublevelEnergyRoot_le g (a + oscillationWidth k) n)).trans_lt hW

end WalkDimensions.PEnergy
