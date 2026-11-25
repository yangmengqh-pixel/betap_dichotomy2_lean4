import WalkDimensions.EnergyLatticeIdentity
import WalkDimensions.LocalEnergyBound

/-!
# Energy bounded by local extensions

Core approximation and the localized measure bound apply on each member
of a finite open cover, even when the local representatives are measurable.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {m : Measure X} [IsFiniteMeasureOnCompacts m] {p : ℝ} (E : PEnergy m p)

theorem energy_le_sum_of_local_extensions (f : E.domain) {ι : Type*} (t : Finset ι)
    (U : ι → Set X) (k : ι → E.domain) (a : ι → ℝ)
    (hU : ∀ i ∈ t, IsOpen (U i)) (hCover : univ ⊆ ⋃ i ∈ t, U i)
    (hLocal : ∀ i ∈ t, ∀ᵐ x ∂m, x ∈ U i →
      (f : RealLp m p) x - (k i : RealLp m p) x = a i) :
    (E.energy f : ℝ) ≤ ∑ i ∈ t, (E.energy (k i) : ℝ) := by
  let ε (n : ℕ) := 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  choose v hv hc hmem hD using fun n ↦ E.regular_graph f (ε n) (hε n)
  let F (n : ℕ) : E.CompactCore :=
    ⟨⟨continuousLp p (v n) (hv n) (hc n), hmem n⟩, v n,
      MemLp.coeFn_toLp ((hv n).memLp_of_hasCompactSupport (hc n)), hv n, hc n⟩
  let e (n : ℕ) := f - (F n).domainElement
  have hE : Tendsto (fun n ↦ E.rootSeminorm (e n)) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ ↦ apply_nonneg _ _) _ tendsto_one_div_add_atTop_nhds_zero_nat
    intro n
    have h : e n = -((F n).domainElement - f) := neg_sub _ _ |>.symm
    rw [h, map_neg_eq_map]
    exact (E.rootSeminorm_le_graphSeminorm _).trans (hD n).le
  have hLhs : Tendsto (fun n ↦ (E.energy (F n).domainElement : ℝ)) atTop (𝓝 (E.energy f : ℝ)) := by
    simpa only [e, sub_sub_cancel] using E.tendsto_energy_sub_of_root_tendsto_zero f e hE
  have hRhs (s : Finset ι) : Tendsto (fun n ↦ ∑ i ∈ s, (E.energy (k i - e n) : ℝ))
      atTop (𝓝 (∑ i ∈ s, (E.energy (k i) : ℝ))) := by
    classical
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using tendsto_const_nhds
    | insert i s hi ih =>
        simp only [Finset.sum_insert hi]
        exact (E.tendsto_energy_sub_of_root_tendsto_zero (k i) e hE).add ih
  apply le_of_tendsto_of_tendsto hLhs (hRhs t)
  refine Eventually.of_forall fun n ↦ ?_
  let Γ := (F n).coreEnergyMeasure
  have hΓ (i : ι) (hi : i ∈ t) : Γ (U i) ≤ (E.energy (k i - e n) : ℝ≥0∞) := by
    let v' (x : X) := (k i : RealLp m p) x - (e n : RealLp m p) x
    have hRep : ((k i - e n : E.domain) : RealLp m p) =ᵐ[m] v' :=
      Lp.coeFn_sub (k i : RealLp m p) (e n : RealLp m p)
    apply (F n).coreEnergyMeasure_open_le_energy_of_ae_sub_const (k i - e n) hRep (hU i hi)
    filter_upwards [(F n).ae_eq, hLocal i hi,
      Lp.coeFn_sub (f : RealLp m p) ((F n).domainElement : RealLp m p)] with x hx hL he
    intro hxU
    change (e n : RealLp m p) x = (f : RealLp m p) x - ((F n).domainElement : RealLp m p) x at he
    change (F n).toFun x - ((k i : RealLp m p) x - (e n : RealLp m p) x) = a i
    linarith only [hx, hL hxU, he]
  have hMass : (E.energy (F n).domainElement : ℝ≥0∞) ≤
      ∑ i ∈ t, (E.energy (k i - e n) : ℝ≥0∞) := by
    rw [← (F n).coreEnergyMeasure_univ]
    exact (measure_mono hCover).trans ((measure_biUnion_finset_le t U).trans
      (Finset.sum_le_sum hΓ))
  have hFinite : (∑ i ∈ t, (E.energy (k i - e n) : ℝ≥0∞)) ≠ ∞ :=
    ENNReal.sum_ne_top.mpr fun _ _ ↦ ENNReal.coe_ne_top
  simpa only [ENNReal.coe_toReal, ENNReal.toReal_sum (fun _ _ ↦ ENNReal.coe_ne_top)] using
    ENNReal.toReal_mono hFinite hMass

end WalkDimensions.PEnergy
