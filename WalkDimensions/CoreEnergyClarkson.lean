import WalkDimensions.CoreEnergyPairs

/-!
# Passing the energy inequalities to local measures
-/

open Filter Function MeasureTheory Set TopologicalSpace
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy.CompactCore

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {p : ℝ} {E : PEnergy μ p}

instance (f g : E.CompactCore) : (f.pairMeasure g).InnerRegular := by
  unfold pairMeasure
  infer_instance

instance (f g : E.CompactCore) : IsFiniteMeasure (f.pairMeasure g) := by
  unfold pairMeasure
  infer_instance

private theorem pairMeasure_real_le_of_energy_pair_le (f g : E.CompactCore)
    {F : ℝ → ℝ → ℝ} (hF : Continuous (Function.uncurry F))
    (hmono : ∀ x x' y y' : ℝ, 0 ≤ x → 0 ≤ y → x ≤ x' → y ≤ y' → F x y ≤ F x' y')
    (hlaw : ∀ u v : E.domain, (E.energy (u + v) : ℝ) + E.energy (u - v) ≤
      F (E.energy u : ℝ) (E.energy v : ℝ)) {A : Set X} (hA : MeasurableSet A) :
    (f.pairMeasure g A).toReal ≤ F (f.coreEnergyMeasure A).toReal (g.coreEnergyMeasure A).toReal := by
  have hK (K : Compacts X) :
      (f.pairMeasure g K).toReal ≤ F (f.coreEnergyMeasure K).toReal (g.coreEnergyMeasure K).toReal := by
    obtain ⟨w, hw, _⟩ := E.exists_compactCore_sublevel_eq K.isCompact' isOpen_univ (subset_univ _)
    change {x | w.toFun x ≤ -1} = (K : Set X) at hw
    let u (n : ℕ) := f.oscillationCore w (-1) n
    let v (n : ℕ) := g.oscillationCore w (-1) n
    have hEval (h : E.CompactCore) : (h.coreEnergyMeasure K).toReal = h.sublevelDistribution w (-1) := by
      rw [← hw, h.coreEnergyMeasure_sublevel]
      exact ENNReal.toReal_ofReal (Real.rpow_nonneg (h.sublevelEnergyRoot_nonneg w _) _)
    have hEq (n : ℕ) : (u n).pairMeasure (v n) K = f.pairMeasure g K := by
      rw [← hw]
      exact f.pairMeasure_eq_of_eqOn_sawtooths g (u n) (v n)
        (isClosed_le w.continuous continuous_const).measurableSet (oscillationWidth_pos n)
        (f.oscillationCore_eq_sawtooth_on_sublevel w (-1) n)
        (g.oscillationCore_eq_sawtooth_on_sublevel w (-1) n)
    have hFconv : Tendsto (fun n ↦ F (E.energy (u n).domainElement : ℝ)
        (E.energy (v n).domainElement : ℝ)) atTop
        (𝓝 (F (f.coreEnergyMeasure K).toReal (g.coreEnergyMeasure K).toReal)) := by
      rw [hEval f, hEval g]
      exact (hF.tendsto _).comp ((f.tendsto_oscillation_energy w (-1)).prodMk_nhds
        (g.tendsto_oscillation_energy w (-1)))
    apply ge_of_tendsto hFconv
    refine Eventually.of_forall fun n ↦ ?_
    have hMass : f.pairMeasure g K ≤ (u n).pairMeasure (v n) univ :=
      (hEq n).symm.trans_le (measure_mono (subset_univ _))
    have ht := ENNReal.toReal_mono (measure_ne_top _ _) hMass
    rw [(u n).pairMeasure_univ (v n), ENNReal.toReal_add ENNReal.coe_ne_top ENNReal.coe_ne_top,
      ENNReal.coe_toReal, ENNReal.coe_toReal] at ht
    exact ht.trans (hlaw _ _)
  let M := F (f.coreEnergyMeasure A).toReal (g.coreEnergyMeasure A).toReal
  have hzero : (E.energy (0 : E.domain) : ℝ) = 0 := by
    rw [E.energy_eq_root_rpow, map_zero, Real.zero_rpow (zero_lt_one.trans E.one_lt).ne']
  have hF0 : 0 ≤ F 0 0 := by simpa only [add_zero, sub_zero, hzero] using hlaw 0 0
  have hM : 0 ≤ M := hF0.trans (hmono 0 _ 0 _ le_rfl le_rfl
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
  apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hM).mp
  rw [hA.measure_eq_iSup_isCompact (f.pairMeasure g)]
  refine iSup_le fun K ↦ iSup_le fun hKA ↦ iSup_le fun hCompact ↦ ?_
  apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hM).mpr
  exact (hK ⟨K, hCompact⟩).trans (hmono _ _ _ _ ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hKA))
    (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hKA)))

theorem pairMeasure_clarkson_upper (f g : E.CompactCore) (hp : 2 ≤ p)
    {A : Set X} (hA : MeasurableSet A) :
    (f.pairMeasure g A).toReal ≤ 2 * ((f.coreEnergyMeasure A).toReal ^ (p - 1)⁻¹ +
      (g.coreEnergyMeasure A).toReal ^ (p - 1)⁻¹) ^ (p - 1) := by
  have hp₁ : 0 ≤ p - 1 := by linarith
  apply f.pairMeasure_real_le_of_energy_pair_le g (F := fun x y ↦ 2 * (x ^ (p - 1)⁻¹ + y ^ (p - 1)⁻¹) ^ (p - 1))
  · change Continuous (fun z : ℝ × ℝ ↦ 2 * (z.1 ^ (p - 1)⁻¹ + z.2 ^ (p - 1)⁻¹) ^ (p - 1))
    exact (((Real.continuous_rpow_const (inv_nonneg.mpr hp₁)).comp continuous_fst |>.add
      ((Real.continuous_rpow_const (inv_nonneg.mpr hp₁)).comp continuous_snd)).rpow_const
      (fun _ ↦ Or.inr hp₁)).const_mul 2
  · intro x x' y y' hx hy hxx hyy
    gcongr <;> positivity
  · exact E.clarkson_two_le hp
  · exact hA

theorem pairMeasure_upper_le_two_mul (f g : E.CompactCore) (hp : p ≤ 2)
    {A : Set X} (hA : MeasurableSet A) :
    (f.pairMeasure g A).toReal ≤ 2 * ((f.coreEnergyMeasure A).toReal +
      (g.coreEnergyMeasure A).toReal) := by
  apply f.pairMeasure_real_le_of_energy_pair_le g (F := fun x y ↦ 2 * (x + y))
  · exact (continuous_fst.add continuous_snd).const_mul 2
  · intro x x' y y' _ _ hxx hyy
    exact mul_le_mul_of_nonneg_left (add_le_add hxx hyy) (by norm_num)
  · exact E.energy_add_add_energy_sub_le_two_mul hp
  · exact hA

end WalkDimensions.PEnergy.CompactCore
