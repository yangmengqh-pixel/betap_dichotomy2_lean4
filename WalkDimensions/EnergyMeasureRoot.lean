import WalkDimensions.CoreEnergySeminorm

/-!
# Extension of the localized root to the energy domain

The infimum formula extends the localized seminorm from the continuous
compact core, with the global energy seminorm controlling its changes.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {p : ℝ} (E : PEnergy μ p)

private noncomputable def zeroCore : E.CompactCore :=
  ⟨0, 0, Lp.coeFn_zero ℝ (ENNReal.ofReal p) μ, continuous_const, HasCompactSupport.zero⟩

private theorem coreEnergyMeasure_zeroCore : E.zeroCore.coreEnergyMeasure = 0 := by
  have h : E.zeroCore.coreEnergyMeasure univ = 0 := by
    rw [CompactCore.coreEnergyMeasure_univ, ← ENNReal.ofReal_coe_nnreal]
    change ENNReal.ofReal (E.energy 0 : ℝ) = 0
    rw [E.energy_eq_root_rpow, map_zero, Real.zero_rpow (zero_lt_one.trans E.one_lt).ne',
      ENNReal.ofReal_zero]
  ext A hA
  rw [FunLike.coe_zero, Pi.zero_apply]
  exact measure_mono_null (subset_univ _) h

private noncomputable def rootExtensionValue (A : Set X) (f : E.domain) : ℝ :=
  sInf (range fun g : E.CompactCore ↦ g.localEnergyRoot A + E.rootSeminorm (f - g.domainElement))

private theorem rootExtensionValue_bddBelow (A : Set X) (f : E.domain) :
    BddBelow (range fun g : E.CompactCore ↦ g.localEnergyRoot A + E.rootSeminorm (f - g.domainElement)) :=
  ⟨0, forall_mem_range.mpr fun g ↦ add_nonneg (g.localEnergyRoot_nonneg A) (apply_nonneg _ _)⟩

private theorem rootExtensionValue_nonneg (A : Set X) (f : E.domain) :
    0 ≤ E.rootExtensionValue A f :=
  le_csInf ⟨_, mem_range_self E.zeroCore⟩
    (forall_mem_range.mpr fun g ↦ add_nonneg (g.localEnergyRoot_nonneg A) (apply_nonneg _ _))

private theorem rootExtensionValue_le (A : Set X) (f : E.domain) (g : E.CompactCore) :
    E.rootExtensionValue A f ≤ g.localEnergyRoot A + E.rootSeminorm (f - g.domainElement) :=
  csInf_le (E.rootExtensionValue_bddBelow A f) (mem_range_self g)

private theorem rootExtensionValue_le_rootSeminorm (A : Set X) (f : E.domain) :
    E.rootExtensionValue A f ≤ E.rootSeminorm f := by
  have h := E.rootExtensionValue_le A f E.zeroCore
  rw [CompactCore.localEnergyRoot, E.coreEnergyMeasure_zeroCore,
    FunLike.coe_zero, Pi.zero_apply, ENNReal.toReal_zero,
    Real.zero_rpow (inv_ne_zero (zero_lt_one.trans E.one_lt).ne'), zero_add] at h
  simpa only [zeroCore, sub_zero] using h

private theorem rootExtensionValue_add_le {A : Set X} (hA : MeasurableSet A) (f g : E.domain) :
    E.rootExtensionValue A (f + g) ≤ E.rootExtensionValue A f + E.rootExtensionValue A g := by
  by_contra! hgt
  let ε := (E.rootExtensionValue A (f + g) -
    (E.rootExtensionValue A f + E.rootExtensionValue A g)) / 3
  have hε : 0 < ε := div_pos (sub_pos.mpr hgt) (by norm_num)
  have hnear (u : E.domain) : ∃ v : E.CompactCore,
      v.localEnergyRoot A + E.rootSeminorm (u - v.domainElement) < E.rootExtensionValue A u + ε := by
    obtain ⟨_, ⟨v, rfl⟩, hv⟩ := exists_lt_of_csInf_lt (⟨_, mem_range_self E.zeroCore⟩ :
      (range fun v : E.CompactCore ↦ v.localEnergyRoot A + E.rootSeminorm (u - v.domainElement)).Nonempty)
      (lt_add_of_pos_right (E.rootExtensionValue A u) hε)
    exact ⟨v, hv⟩
  obtain ⟨u, hu⟩ := hnear f
  obtain ⟨v, hv⟩ := hnear g
  have hB := E.rootExtensionValue_le A (f + g) (u.add v)
  have ht := u.localEnergyRoot_add_le v hA
  have he : f + g - (u.add v).domainElement =
      (f - u.domainElement) + (g - v.domainElement) := by
    change f + g - (u.domainElement + v.domainElement) = _
    abel
  rw [he] at hB
  have hsum := E.rootSeminorm.add_le' (f - u.domainElement) (g - v.domainElement)
  change E.rootSeminorm ((f - u.domainElement) + (g - v.domainElement)) ≤
    E.rootSeminorm (f - u.domainElement) + E.rootSeminorm (g - v.domainElement) at hsum
  dsimp only [ε] at hu hv
  linarith only [hB, ht, hsum, hu, hv, hgt]

private theorem rootExtensionValue_smul_le (A : Set X) (a : ℝ) (f : E.domain) :
    E.rootExtensionValue A (a • f) ≤ |a| * E.rootExtensionValue A f := by
  by_cases ha : a = 0
  · subst a
    rw [zero_smul, abs_zero, zero_mul]
    exact (E.rootExtensionValue_le_rootSeminorm A 0).trans_eq (map_zero _)
  rw [mul_comm |a|]
  apply (div_le_iff₀ (abs_pos.mpr ha)).mp
  apply le_csInf ⟨_, mem_range_self E.zeroCore⟩
  rintro _ ⟨g, rfl⟩
  apply (div_le_iff₀ (abs_pos.mpr ha)).mpr
  refine (E.rootExtensionValue_le A (a • f) (g.smul a)).trans_eq ?_
  rw [CompactCore.localEnergyRoot_smul]
  change |a| * g.localEnergyRoot A + E.rootSeminorm (a • f - a • g.domainElement) = _
  have he : a • f - a • g.domainElement = a • (f - g.domainElement) := by module
  rw [he, map_smul_eq_mul, Real.norm_eq_abs]
  change |a| * g.localEnergyRoot A + |a| * E.rootSeminorm (f - g.domainElement) =
    (g.localEnergyRoot A + E.rootSeminorm (f - g.domainElement)) * |a|
  ring

private theorem rootExtensionValue_smul (A : Set X) (a : ℝ) (f : E.domain) :
    E.rootExtensionValue A (a • f) = |a| * E.rootExtensionValue A f := by
  apply le_antisymm (E.rootExtensionValue_smul_le A a f)
  by_cases ha : a = 0
  · rw [ha, abs_zero, zero_mul]
    exact E.rootExtensionValue_nonneg A _
  have h := E.rootExtensionValue_smul_le A a⁻¹ (a • f)
  rw [smul_smul, inv_mul_cancel₀ ha, one_smul, abs_inv] at h
  exact (mul_le_mul_of_nonneg_left h (abs_nonneg a)).trans_eq
    (by rw [← mul_assoc, mul_inv_cancel₀ (abs_ne_zero.mpr ha), one_mul])

noncomputable def energyMeasureRoot (A : Set X) (hA : MeasurableSet A) : Seminorm ℝ E.domain where
  toFun := E.rootExtensionValue A
  map_zero' := le_antisymm ((E.rootExtensionValue_le_rootSeminorm A 0).trans_eq (map_zero _))
    (E.rootExtensionValue_nonneg A 0)
  add_le' := E.rootExtensionValue_add_le hA
  neg' := by
    intro f
    have h := E.rootExtensionValue_smul A (-1) f
    have hf : (-1 : ℝ) • f = -f := neg_one_smul ℝ f
    rw [hf, abs_neg, abs_one, one_mul] at h
    exact h
  smul' a f := by rw [Real.norm_eq_abs, E.rootExtensionValue_smul]

theorem energyMeasureRoot_le (A : Set X) (hA : MeasurableSet A) (f : E.domain) :
    E.energyMeasureRoot A hA f ≤ E.rootSeminorm f :=
  E.rootExtensionValue_le_rootSeminorm A f

set_option maxHeartbeats 450000 in
private theorem localEnergyRoot_le_add_root_sub (A : Set X) (hA : MeasurableSet A)
    (f g : E.CompactCore) :
    f.localEnergyRoot A ≤ g.localEnergyRoot A + E.rootSeminorm (f.domainElement - g.domainElement) := by
  let d := f.sub g
  have hEq : f.toFun = (g.add d).toFun := by
    funext x
    change f.toFun x = g.toFun x + (f.toFun x - g.toFun x)
    ring
  have hEqRoot := f.localEnergyRoot_eq_of_toFun_eq (g.add d) hEq hA
  have hd : d.domainElement = f.domainElement - g.domainElement := by
    change f.domainElement + -g.domainElement = _
    rw [sub_eq_add_neg]
  have hD := d.localEnergyRoot_le_rootSeminorm A
  have hTail := hD.trans_eq (congrArg (fun w : E.domain ↦ E.rootSeminorm w) hd)
  exact hEqRoot.le.trans ((g.localEnergyRoot_add_le d hA).trans
    (add_le_add (le_refl (g.localEnergyRoot A)) hTail))

theorem energyMeasureRoot_apply_core (A : Set X) (hA : MeasurableSet A) (f : E.CompactCore) :
    E.energyMeasureRoot A hA f.domainElement = f.localEnergyRoot A := by
  change E.rootExtensionValue A f.domainElement = _
  have hHi := E.rootExtensionValue_le A f.domainElement f
  rw [sub_self, map_zero, add_zero] at hHi
  refine le_antisymm hHi (le_csInf ⟨_, mem_range_self E.zeroCore⟩
    (forall_mem_range.mpr (E.localEnergyRoot_le_add_root_sub A hA f)))

theorem energyMeasureRoot_univ (f : E.domain) :
    E.energyMeasureRoot univ MeasurableSet.univ f = E.rootSeminorm f := by
  apply le_antisymm (E.energyMeasureRoot_le _ _ _)
  change E.rootSeminorm f ≤ E.rootExtensionValue univ f
  apply le_csInf ⟨_, mem_range_self E.zeroCore⟩
  rintro _ ⟨g, rfl⟩
  have hg : g.localEnergyRoot univ = E.rootSeminorm g.domainElement := by
    rw [CompactCore.localEnergyRoot, g.coreEnergyMeasure_univ, ENNReal.coe_toReal, E.rootSeminorm_apply]
  change E.rootSeminorm f ≤ g.localEnergyRoot univ + E.rootSeminorm (f - g.domainElement)
  rw [hg]
  have h := E.rootSeminorm.add_le' g.domainElement (f - g.domainElement)
  change E.rootSeminorm (g.domainElement + (f - g.domainElement)) ≤ _ at h
  rwa [add_comm g.domainElement, sub_add_cancel] at h

end WalkDimensions.PEnergy
