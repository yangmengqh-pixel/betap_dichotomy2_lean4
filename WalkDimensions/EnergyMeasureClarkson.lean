import WalkDimensions.EnergyMeasureConstruction
import WalkDimensions.EnergyFirstVariation

/-!
# Clarkson inequalities on the full domain

The inequalities for the continuous compact core pass to the local
seminorms through graph approximation.
-/

open Asymptotics Filter MeasureTheory Set
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {p : ℝ} (E : PEnergy μ p)

theorem energyMeasure_real_eq (f : E.domain) {A : Set X} (hA : MeasurableSet A) :
    (E.energyMeasure f A).toReal = E.energyMeasureRoot A hA f ^ p := by
  rw [E.energyMeasure_apply f hA, ENNReal.toReal_ofReal (Real.rpow_nonneg (apply_nonneg _ _) _)]

theorem tendsto_energyMeasure_real_of_root_sub {f : E.domain} {g : ℕ → E.domain}
    (h : Tendsto (fun n ↦ E.rootSeminorm (g n - f)) atTop (𝓝 0)) {A : Set X}
    (hA : MeasurableSet A) :
    Tendsto (fun n ↦ (E.energyMeasure (g n) A).toReal) atTop (𝓝 ((E.energyMeasure f A).toReal)) := by
  let N := E.energyMeasureRoot A hA
  have hN : Tendsto (fun n ↦ N (g n)) atTop (𝓝 (N f)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [h.eventually_lt_const hε] with n hn
    rw [Real.dist_eq]
    exact (E.abs_energyMeasureRoot_sub_le hA (g n) f).trans_lt hn
  simp_rw [E.energyMeasure_real_eq _ hA]
  exact hN.rpow_const (Or.inr (zero_lt_one.trans E.one_lt).le)

private theorem exists_corePair_energyMeasure_tendsto (f g : E.domain) {A : Set X}
    (hA : MeasurableSet A) :
    ∃ u v : ℕ → E.CompactCore,
      Tendsto (fun n ↦ ((u n).coreEnergyMeasure A).toReal) atTop (𝓝 ((E.energyMeasure f A).toReal)) ∧
      Tendsto (fun n ↦ ((v n).coreEnergyMeasure A).toReal) atTop (𝓝 ((E.energyMeasure g A).toReal)) ∧
      Tendsto (fun n ↦ ((u n).pairMeasure (v n) A).toReal) atTop
        (𝓝 ((E.energyMeasure (f + g) A).toReal + (E.energyMeasure (f - g) A).toReal)) := by
  obtain ⟨u, hu⟩ := E.exists_core_graph_approximation f
  obtain ⟨v, hv⟩ := E.exists_core_graph_approximation g
  let a (n : ℕ) := (u n).domainElement - f
  let b (n : ℕ) := (v n).domainElement - g
  have ha : Tendsto (fun n ↦ E.rootSeminorm (a n)) atTop (𝓝 0) :=
    squeeze_zero (fun n ↦ apply_nonneg _ (a n)) (fun n ↦ E.rootSeminorm_le_graphSeminorm (a n)) hu
  have hb : Tendsto (fun n ↦ E.rootSeminorm (b n)) atTop (𝓝 0) :=
    squeeze_zero (fun n ↦ apply_nonneg _ (b n)) (fun n ↦ E.rootSeminorm_le_graphSeminorm (b n)) hv
  refine ⟨u, v, ?_, ?_, ?_⟩
  · simpa only [E.energyMeasure_core] using E.tendsto_energyMeasure_real_of_root_sub ha hA
  · simpa only [E.energyMeasure_core] using E.tendsto_energyMeasure_real_of_root_sub hb hA
  have hab := ha.add hb
  rw [add_zero] at hab
  have hsum : Tendsto (fun n ↦ E.rootSeminorm (((u n).add (v n)).domainElement - (f + g)))
      atTop (𝓝 0) := by
    refine squeeze_zero (fun _ ↦ apply_nonneg _ _) (fun n ↦ ?_) hab
    have he : ((u n).add (v n)).domainElement - (f + g) = a n + b n := by
      change (u n).domainElement + (v n).domainElement - (f + g) =
        ((u n).domainElement - f) + ((v n).domainElement - g)
      abel
    rw [he]
    exact E.rootSeminorm.add_le' (a n) (b n)
  have hsub : Tendsto (fun n ↦ E.rootSeminorm (((u n).sub (v n)).domainElement - (f - g)))
      atTop (𝓝 0) := by
    refine squeeze_zero (fun _ ↦ apply_nonneg _ _) (fun n ↦ ?_) hab
    have he : ((u n).sub (v n)).domainElement - (f - g) = a n - b n := by
      change (u n).domainElement + -(v n).domainElement - (f - g) =
        ((u n).domainElement - f) - ((v n).domainElement - g)
      abel
    rw [he]
    exact map_sub_le_add _ _ _
  have hplus := E.tendsto_energyMeasure_real_of_root_sub hsum hA
  have hminus := E.tendsto_energyMeasure_real_of_root_sub hsub hA
  simpa only [E.energyMeasure_core, CompactCore.pairMeasure_toReal] using hplus.add hminus

theorem energyMeasure_real_pair_upper_le_two_mul (hp : p ≤ 2) (f g : E.domain)
    {A : Set X} (hA : MeasurableSet A) :
    (E.energyMeasure (f + g) A).toReal + (E.energyMeasure (f - g) A).toReal ≤
      2 * ((E.energyMeasure f A).toReal + (E.energyMeasure g A).toReal) := by
  obtain ⟨u, v, hu, hv, huv⟩ := E.exists_corePair_energyMeasure_tendsto f g hA
  exact le_of_tendsto_of_tendsto huv ((hu.add hv).const_mul 2)
    (Eventually.of_forall fun n ↦ (u n).pairMeasure_upper_le_two_mul (v n) hp hA)

theorem energyMeasure_real_clarkson_upper (hp : 2 ≤ p) (f g : E.domain)
    {A : Set X} (hA : MeasurableSet A) :
    (E.energyMeasure (f + g) A).toReal + (E.energyMeasure (f - g) A).toReal ≤
      2 * ((E.energyMeasure f A).toReal ^ (p - 1)⁻¹ +
        (E.energyMeasure g A).toReal ^ (p - 1)⁻¹) ^ (p - 1) := by
  obtain ⟨u, v, hu, hv, huv⟩ := E.exists_corePair_energyMeasure_tendsto f g hA
  have hp' : 0 ≤ p - 1 := sub_nonneg.mpr E.one_lt.le
  have h := (((hu.rpow_const (Or.inr (inv_nonneg.mpr hp'))).add
    (hv.rpow_const (Or.inr (inv_nonneg.mpr hp')))).rpow_const (Or.inr hp')).const_mul 2
  exact le_of_tendsto_of_tendsto huv h
    (Eventually.of_forall fun n ↦ (u n).pairMeasure_clarkson_upper (v n) hp hA)

theorem energyMeasure_real_clarkson_lower (hp : p ≤ 2) (f g : E.domain)
    {A : Set X} (hA : MeasurableSet A) :
    2 * ((E.energyMeasure f A).toReal ^ (p - 1)⁻¹ +
        (E.energyMeasure g A).toReal ^ (p - 1)⁻¹) ^ (p - 1) ≤
      (E.energyMeasure (f + g) A).toReal + (E.energyMeasure (f - g) A).toReal := by
  obtain ⟨u, v, hu, hv, huv⟩ := E.exists_corePair_energyMeasure_tendsto f g hA
  have hp' : 0 ≤ p - 1 := sub_nonneg.mpr E.one_lt.le
  have h := (((hu.rpow_const (Or.inr (inv_nonneg.mpr hp'))).add
    (hv.rpow_const (Or.inr (inv_nonneg.mpr hp')))).rpow_const (Or.inr hp')).const_mul 2
  exact le_of_tendsto_of_tendsto h huv
    (Eventually.of_forall fun n ↦ (u n).pairMeasure_clarkson_lower (v n) hp hA)

theorem exists_energyMeasure_first_variation (f : E.domain) {A : Set X} (hA : MeasurableSet A) :
    ∃ L : E.domain →ₗ[ℝ] ℝ,
      (∀ g : E.domain, HasDerivAt (fun t : ℝ ↦ (E.energyMeasure (f + t • g) A).toReal)
        (p * L g) 0) ∧
      ∀ g : E.domain, |L g| ≤ (E.energyMeasureRoot A hA f) ^ (p - 1) * E.energyMeasureRoot A hA g :=
  exists_seminorm_first_variation E.one_lt (E.energyMeasureRoot A hA)
    (fun u ↦ (E.energyMeasure u A).toReal) (fun u ↦ E.energyMeasure_real_eq u hA)
    (fun hp u v ↦ E.energyMeasure_real_pair_upper_le_two_mul hp u v hA)
    (fun hp u v ↦ E.energyMeasure_real_clarkson_upper hp u v hA) f

end WalkDimensions.PEnergy
