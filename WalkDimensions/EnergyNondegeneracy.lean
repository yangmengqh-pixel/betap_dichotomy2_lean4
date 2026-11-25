import WalkDimensions.PEnergy
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.Topology.Order.Bornology

/-!
# Nondegeneracy of continuous test functions

Regularity gives nonzero compactly supported test functions. The ball
Poincaré inequality forces every zero-energy continuous representative
to be constant. These steps are used in Sections 4 and 5.
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal NNReal

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X} [IsFiniteMeasureOnCompacts m] {p : ℝ}

theorem continuousLp_ae_eq (u : X → ℝ) (hu : Continuous u) (hc : HasCompactSupport u) :
    (continuousLp (m := m) p u hu hc : X → ℝ) =ᵐ[m] u :=
  MemLp.coeFn_toLp _

theorem exists_nonzero_core [ProperSpace X] [Nonempty X] (E : PEnergy m p) :
    ∃ (u : X → ℝ) (hu : Continuous u) (hc : HasCompactSupport u),
      continuousLp (m := m) p u hu hc ∈ E.domain ∧ ∃ x, u x ≠ 0 := by
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  let b : X → ℝ := fun y ↦ max 0 (1 - dist y x)
  have hb : Continuous b := continuous_const.max (continuous_const.sub (continuous_id.dist continuous_const))
  have hbc : HasCompactSupport b := by
    apply HasCompactSupport.intro (isCompact_closedBall x 1)
    intro y hy
    exact max_eq_left (sub_nonpos.mpr (le_of_not_ge hy))
  obtain ⟨u, hu, hc, hdom, δ, hδ, hclose⟩ := E.regular_uniform b hb hbc (1 / 2)
    (by norm_num)
  refine ⟨u, hu, hc, hdom, x, fun hz ↦ ?_⟩
  have h := hclose x
  norm_num [b, hz] at h
  linarith

omit [MeasurableSpace X] [BorelSpace X] in
/-- A continuous compactly supported function on an unbounded space has
a zero somewhere. -/
theorem exists_zero_of_hasCompactSupport (hunbounded : ¬ Bornology.IsBounded (univ : Set X))
    {u : X → ℝ} (hc : HasCompactSupport u) : ∃ x, u x = 0 := by
  by_contra! h
  apply hunbounded
  apply hc.isCompact.isBounded.subset
  intro x _
  exact subset_closure (mem_support.mpr (h x))

omit [IsFiniteMeasureOnCompacts m] in
private theorem eqOn_const_of_lintegral_eq_zero [m.IsOpenPosMeasure] {u : X → ℝ}
    (hu : Continuous u) {U : Set X} (hU : IsOpen U) {c : ℝ} (hp : 0 < p)
    (hz : (∫⁻ y in U, ENNReal.ofReal |u y - c| ^ p ∂m) = 0) :
    EqOn u (fun _ ↦ c) U := by
  have hf : Continuous (fun y ↦ |u y - c|) := (hu.sub continuous_const).abs
  have hg : Measurable (fun y ↦ ENNReal.ofReal |u y - c| ^ p) :=
    hf.measurable.ennreal_ofReal.pow_const _
  have h := (lintegral_eq_zero_iff hg).1 hz
  have heq : ∀ᵐ y ∂m.restrict U, u y = c := by
    filter_upwards [h] with y hy
    change ENNReal.ofReal |u y - c| ^ p = 0 at hy
    have hnonpos := ENNReal.ofReal_eq_zero.mp ((ENNReal.rpow_eq_zero_iff_of_pos hp).mp hy)
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hnonpos (abs_nonneg _)))
  have hclosed : IsClosed {y | u y = c} := isClosed_eq hu continuous_const
  have hset : m (U ∩ {y | u y ≠ c}) = 0 := by
    have hzero : (m.restrict U) ({y | u y = c}ᶜ) = 0 := ae_iff.mp heq
    rwa [Measure.restrict_apply hclosed.measurableSet.compl, inter_comm] at hzero
  have ho : IsOpen (U ∩ {y | u y ≠ c}) :=
    hU.inter hclosed.isOpen_compl
  have hempty := (ho.measure_eq_zero_iff (μ := m)).1 hset
  intro y hy
  by_contra hne
  have hmem : y ∈ U ∩ {y | u y ≠ c} := ⟨hy, hne⟩
  simp only [hempty, mem_empty_iff_false] at hmem

/-- The Poincaré inequality and the total-mass identity rule out
nonconstant continuous representatives of zero-energy elements. -/
theorem continuous_constant_of_energy_eq_zero [m.IsOpenPosMeasure] (E : PEnergy m p)
    {Γ : E.domain → Measure X} (hPI : E.Poincare Γ β)
    (hΓ : ∀ f, Γ f univ = (E.energy f : ℝ≥0∞))
    {f : E.domain} (hzero : E.energy f = 0) {u : X → ℝ} (hu : Continuous u)
    (hfu : (f : RealLp m p) =ᵐ[m] u) (x y : X) : u x = u y := by
  have hΓf : Γ f = 0 := by
    apply le_antisymm _ bot_le
    intro s
    change Γ f s ≤ (0 : Measure X) s
    rw [FunLike.coe_zero, Pi.zero_apply, ← show Γ f univ = 0 by simp [hΓ, hzero]]
    exact measure_mono (subset_univ s)
  obtain ⟨C, A, _, _, hbound⟩ := hPI
  let r := dist y x + 1
  have hr : 0 < r := by dsimp only [r]; positivity
  let U := ball x r
  let c := ⨍ z in U, (f : RealLp m p) z ∂m
  have hI : (∫⁻ z in U, ENNReal.ofReal |(f : RealLp m p) z - c| ^ p ∂m) = 0 := by
    have h := hbound x r hr f
    simpa only [U, c, hΓf, FunLike.coe_zero, Pi.zero_apply, mul_zero, nonpos_iff_eq_zero] using h
  have hzero' : (∫⁻ z in U, ENNReal.ofReal |u z - c| ^ p ∂m) = 0 := by
    rw [← hI]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_of_ae hfu] with z hz
    rw [hz]
  have heq := eqOn_const_of_lintegral_eq_zero hu isOpen_ball (zero_lt_one.trans E.one_lt) hzero'
  exact (heq (mem_ball_self hr)).trans (heq (mem_ball.2 (lt_add_one _))).symm

/-- With the ball Poincaré inequality, every zero-energy domain element
is almost everywhere constant, including elements without a continuous
representative. -/
theorem ae_constant_of_energy_eq_zero [Nonempty X] [m.IsOpenPosMeasure] (E : PEnergy m p)
    {Γ : E.domain → Measure X} (hPI : E.Poincare Γ β)
    (hΓ : ∀ f, Γ f univ = (E.energy f : ℝ≥0∞)) {f : E.domain} (hzero : E.energy f = 0) :
    ∃ c : ℝ, (f : RealLp m p) =ᵐ[m] fun _ ↦ c := by
  have hΓf : Γ f = 0 := by
    apply le_antisymm _ bot_le
    intro s
    change Γ f s ≤ (0 : Measure X) s
    rw [FunLike.coe_zero, Pi.zero_apply, ← show Γ f univ = 0 by simp [hΓ, hzero]]
    exact measure_mono (subset_univ s)
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨C, A, _, _, hbound⟩ := hPI
  let B := fun n : ℕ ↦ ball x ((n : ℝ) + 1)
  let c := fun n : ℕ ↦ ⨍ y in B n, (f : RealLp m p) y ∂m
  have hBmono : Monotone B := fun a b hab ↦ ball_subset_ball
    (add_le_add_left (Nat.cast_le.mpr hab) 1)
  have hp : 0 < p := zero_lt_one.trans E.one_lt
  have hzeroInt (n : ℕ) :
      (∫⁻ y in B n, ENNReal.ofReal |(f : RealLp m p) y - c n| ^ p ∂m) = 0 := by
    simpa only [B, c, hΓf, FunLike.coe_zero, Pi.zero_apply, mul_zero, nonpos_iff_eq_zero] using
      hbound x ((n : ℝ) + 1) (by positivity) f
  have hconst (n : ℕ) : (f : RealLp m p) =ᵐ[m.restrict (B n)] fun _ ↦ c n := by
    have hmeas : AEMeasurable (fun y ↦ ENNReal.ofReal |(f : RealLp m p) y - c n| ^ p)
        (m.restrict (B n)) :=
      (continuous_abs.measurable.comp_aemeasurable
        ((Lp.aestronglyMeasurable (f : RealLp m p)).aemeasurable.restrict.sub
          aemeasurable_const)).ennreal_ofReal.pow_const _
    filter_upwards [(lintegral_eq_zero_iff' hmeas).1 (hzeroInt n)] with y hy
    change ENNReal.ofReal |(f : RealLp m p) y - c n| ^ p = 0 at hy
    have hab := ENNReal.ofReal_eq_zero.mp ((ENNReal.rpow_eq_zero_iff_of_pos hp).mp hy)
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hab (abs_nonneg _)))
  have hnonzero : m.restrict (B 0) ≠ 0 := by
    intro hm
    have he : m (B 0) = 0 := by simpa only [Measure.restrict_apply_univ, FunLike.coe_zero,
      Pi.zero_apply] using congrArg (fun (μ : Measure X) ↦ μ univ) hm
    exact (measure_ball_pos m x (show 0 < (0 : ℝ) + 1 by norm_num)).ne' he
  have : NeZero (m.restrict (B 0)) := ⟨hnonzero⟩
  have hc (n : ℕ) : c n = c 0 := by
    have he : (f : RealLp m p) =ᵐ[m.restrict (B 0)] fun _ ↦ c n :=
      (hconst n).filter_mono (ae_mono (Measure.restrict_mono (hBmono (Nat.zero_le n)) le_rfl))
    obtain ⟨_, hh⟩ := (he.symm.trans (hconst 0)).exists
    exact hh
  refine ⟨c 0, ?_⟩
  have hae (n : ℕ) : ∀ᵐ y ∂m, y ∈ B n → (f : RealLp m p) y = c 0 := by
    have he := hconst n
    rw [hc n] at he
    exact (ae_restrict_iff' measurableSet_ball).1 he
  filter_upwards [ae_all_iff.2 hae] with y hy
  obtain ⟨n, hn⟩ := exists_nat_gt (dist y x)
  exact hy n (mem_ball.mpr (hn.trans_le (by linarith)))

end WalkDimensions.PEnergy
