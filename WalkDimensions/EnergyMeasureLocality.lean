import WalkDimensions.EnergyClarkson
import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.Analysis.MeanInequalities

/-!
# The mass, seminorm and locality properties of energy measures

These are properties (a)–(c) in Section 2 of the paper. They are stated
together here for lemmas which use those properties of the measures.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {m : Measure X} [IsFiniteMeasureOnCompacts m] {p : ℝ} (E : PEnergy m p)

/-- The mass, local seminorm and locality laws of an energy measure. -/
structure EnergyMeasureLaws (Γ : E.domain → Measure X) where
  total_mass : ∀ f, Γ f univ = (E.energy f : ℝ≥0∞)
  root : ∀ A : Set X, MeasurableSet A → Seminorm ℝ E.domain
  root_apply : ∀ (A : Set X) (hA : MeasurableSet A) (f : E.domain),
    root A hA f = (Γ f).real A ^ p⁻¹
  local_const : ∀ (f g : E.domain) (u v : X → ℝ),
    Continuous u → Continuous v → HasCompactSupport u → HasCompactSupport v →
    (f : RealLp m p) =ᵐ[m] u → (g : RealLp m p) =ᵐ[m] v →
    ∀ (A : Set X), MeasurableSet A →
      (∃ c : ℝ, EqOn (fun x ↦ u x - v x) (fun _ ↦ c) A) → Γ f A = Γ g A

variable {E} {Γ : E.domain → Measure X} (hΓ : E.EnergyMeasureLaws Γ)

include hΓ

theorem EnergyMeasureLaws.measure_ne_top (f : E.domain) (A : Set X) : Γ f A ≠ ∞ := by
  apply ne_top_of_le_ne_top _ (measure_mono (subset_univ A))
  rw [hΓ.total_mass f]
  exact ENNReal.coe_ne_top

theorem EnergyMeasureLaws.root_le (A : Set X) (hA : MeasurableSet A) (f : E.domain) :
    hΓ.root A hA f ≤ E.rootSeminorm f := by
  rw [hΓ.root_apply A hA f, E.rootSeminorm_apply]
  apply Real.rpow_le_rpow ENNReal.toReal_nonneg _
    (inv_nonneg.mpr (zero_lt_one.trans E.one_lt).le)
  have h := ENNReal.toReal_mono (hΓ.measure_ne_top f univ) (measure_mono (μ := Γ f) (subset_univ A))
  rw [hΓ.total_mass f, ENNReal.coe_toReal] at h
  exact h

theorem EnergyMeasureLaws.measure_eq_zero_of_eqOn_const (f : E.domain) {u : X → ℝ}
    (hu : Continuous u) (hc : HasCompactSupport u) (hfu : (f : RealLp m p) =ᵐ[m] u)
    {A : Set X} (hA : MeasurableSet A) {c : ℝ} (hconst : EqOn u (fun _ ↦ c) A) :
    Γ f A = 0 := by
  have hzero : (0 : RealLp m p) =ᵐ[m] (fun _ : X ↦ (0 : ℝ)) :=
    Lp.coeFn_zero ℝ (ENNReal.ofReal p) m
  have he := hΓ.local_const f 0 u (fun _ ↦ 0) hu continuous_const hc HasCompactSupport.zero
    hfu hzero A hA ⟨c, fun x hx ↦ by simpa only [sub_zero] using hconst hx⟩
  have hE : (E.energy 0 : ℝ) = 0 := by
    rw [E.energy_eq_root_rpow, map_zero, Real.zero_rpow (zero_lt_one.trans E.one_lt).ne']
  have hmass : Γ 0 univ = 0 := by
    rw [hΓ.total_mass 0, ENNReal.coe_eq_zero, ← NNReal.coe_eq_zero]
    exact hE
  exact he.trans (measure_mono_null (subset_univ A) hmass)

/-- Energy-measure singularity is closed under convergence in the energy
seminorm. This is the closure assertion of [42, Lemma 4.5]. -/
theorem EnergyMeasureLaws.mutuallySingular_of_tendsto_root {f : E.domain} {g : ℕ → E.domain}
    (hsing : ∀ n, (Γ (g n)).MutuallySingular m)
    (hlim : Tendsto (fun n ↦ E.rootSeminorm (f - g n)) atTop (𝓝 (0 : ℝ))) :
    (Γ f).MutuallySingular m := by
  choose N hN hmN hΓN using fun n ↦ hsing n
  let A := ⋂ n, (N n)
  have hA : MeasurableSet A := MeasurableSet.iInter hN
  have hmA : m Aᶜ = 0 := by
    rw [show Aᶜ = ⋃ n, (N n)ᶜ by simp [A, compl_iInter]]
    exact measure_iUnion_null hΓN
  have hzero (n : ℕ) : Γ (g n) A = 0 := measure_mono_null (iInter_subset N n) (hmN n)
  have hle (n : ℕ) : hΓ.root A hA f ≤ E.rootSeminorm (f - g n) := by
    have hh := (hΓ.root A hA).add_le' (f - g n) (g n)
    rw [sub_add_cancel] at hh
    have hz : hΓ.root A hA (g n) = 0 := by
      rw [hΓ.root_apply, measureReal_def, hzero, ENNReal.toReal_zero,
        Real.zero_rpow (inv_ne_zero (zero_lt_one.trans E.one_lt).ne')]
    change hΓ.root A hA f ≤ hΓ.root A hA (f - g n) + hΓ.root A hA (g n) at hh
    rw [hz, add_zero] at hh
    exact hh.trans (hΓ.root_le A hA (f - g n))
  have hroot : hΓ.root A hA f = 0 :=
    le_antisymm (ge_of_tendsto hlim (Eventually.of_forall hle)) (apply_nonneg _ _)
  refine ⟨A, hA, ?_, hmA⟩
  rw [hΓ.root_apply, measureReal_def] at hroot
  have hp : 0 < p := zero_lt_one.trans E.one_lt
  have hh : (Γ f A).toReal = 0 := by
    by_contra h
    exact (Real.rpow_pos_of_pos (lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm h)) p⁻¹).ne' hroot
  by_contra h
  exact (ENNReal.toReal_pos h (hΓ.measure_ne_top f A)).ne' hh

theorem EnergyMeasureLaws.measure_real_finset_smul_sum_le {ι : Type*} (t : Finset ι)
    (f : ι → E.domain) (a : ι → ℝ) (A : Set X) (hA : MeasurableSet A) :
    (Γ (∑ i ∈ t, a i • f i)).real A ≤
      (t.card : ℝ) ^ (p - 1) * ∑ i ∈ t, |a i| ^ p * (E.energy (f i) : ℝ) := by
  classical
  have hp : 0 < p := zero_lt_one.trans E.one_lt
  let S := hΓ.root A hA
  have hSsum : S (∑ i ∈ t, a i • f i) ≤ ∑ i ∈ t, |a i| * S (f i) := by
    induction t using Finset.induction_on with
    | empty => simp
    | insert j t hj ih =>
      simp only [Finset.sum_insert hj]
      refine (S.add_le' _ _).trans ?_
      change S (a j • f j) + S (∑ i ∈ t, a i • f i) ≤ _
      rw [map_smul_eq_mul, Real.norm_eq_abs]
      exact add_le_add_right ih _
  have hSN : (∑ i ∈ t, |a i| * S (f i)) ≤ ∑ i ∈ t, |a i| * E.rootSeminorm (f i) :=
    Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (hΓ.root_le A hA (f i)) (abs_nonneg _)
  have hroot : S (∑ i ∈ t, a i • f i) ^ p = (Γ (∑ i ∈ t, a i • f i)).real A := by
    dsimp only [S]
    rw [hΓ.root_apply, ← Real.rpow_mul (by positivity), inv_mul_cancel₀ hp.ne', Real.rpow_one]
  rw [← hroot]
  calc
    _ ≤ (∑ i ∈ t, |a i| * E.rootSeminorm (f i)) ^ p :=
      Real.rpow_le_rpow (apply_nonneg _ _) (hSsum.trans hSN) hp.le
    _ ≤ (t.card : ℝ) ^ (p - 1) * ∑ i ∈ t, (|a i| * E.rootSeminorm (f i)) ^ p :=
      Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg t E.one_lt.le (fun i _ ↦ by positivity)
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [Real.mul_rpow (abs_nonneg _) (apply_nonneg _ _), ← E.energy_eq_root_rpow]

end WalkDimensions.PEnergy
