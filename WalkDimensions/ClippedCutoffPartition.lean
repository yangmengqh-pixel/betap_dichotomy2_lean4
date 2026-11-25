import WalkDimensions.CoreCutoffSums

/-!
# Local energy bounds for a finite cutoff partition

Successive truncations of partial sums give a partition subordinate to the
original cutoffs. On any support, only intersecting cutoffs contribute to
the localized energy estimate.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal

namespace WalkDimensions.PEnergy.CompactCore

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [LocallyCompactSpace X] {m : Measure X} [IsFiniteMeasureOnCompacts m] {p : ℝ} {E : PEnergy m p}

private theorem root_eq_of_eqOn {A : Set X} (hA : MeasurableSet A) (f g : E.CompactCore)
    (he : EqOn f.toFun g.toFun A) :
    E.energyMeasureRoot A hA f.domainElement = E.energyMeasureRoot A hA g.domainElement := by
  have h := f.coreEnergyMeasure_eq_of_eqOn_sub_const g hA (a := 0)
    (fun x hx ↦ sub_eq_zero.mpr (he hx))
  rw [E.energyMeasureRoot_apply_core, E.energyMeasureRoot_apply_core, localEnergyRoot, localEnergyRoot, h]

/-- Clipping cumulative sums costs at most twice the sum of neighboring local roots. -/
theorem exists_clipped_cutoff_partition {n : ℕ} (ψ : Fin n → E.CompactCore)
    (B : Fin n → Set X) (hB : ∀ i, IsClosed (B i))
    (hsupp : ∀ i, support (ψ i).toFun ⊆ B i)
    (hψ : ∀ i x, (ψ i).toFun x ∈ Icc (0 : ℝ) 1)
    (N : Fin n → Finset (Fin n))
    (hN : ∀ i j, (B i ∩ B j).Nonempty → j ∈ N i) :
    ∃ φ : Fin n → E.CompactCore,
      (∀ i x, 0 ≤ (φ i).toFun x ∧ (φ i).toFun x ≤ (ψ i).toFun x) ∧
      (∀ i, tsupport (φ i).toFun ⊆ B i) ∧
      (∀ x, (∑ i, (φ i).toFun x) = min (∑ i, (ψ i).toFun x) 1) ∧
      ∀ i (A : Set X) (hA : MeasurableSet A),
        E.energyMeasureRoot A hA (φ i).domainElement ≤
          2 * ∑ j ∈ N i, E.energyMeasureRoot A hA (ψ j).domainElement := by
  classical
  let P (k : ℕ) : Finset (Fin n) := Finset.univ.filter (fun j ↦ j.val < k)
  let G (k : ℕ) := (finsetSum (P k) ψ).minOne
  let φ (i : Fin n) := (G (i.val + 1)).sub (G i.val)
  have hP (i : Fin n) : P (i.val + 1) = insert i (P i.val) := by
    ext j
    simp only [P, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, ← Fin.val_inj]
    omega
  have hφ (i : Fin n) (x : X) : 0 ≤ (φ i).toFun x ∧ (φ i).toFun x ≤ (ψ i).toFun x := by
    let a := ∑ j ∈ P i.val, (ψ j).toFun x
    let b := (ψ i).toFun x
    have hb : 0 ≤ b := (hψ i x).1
    change 0 ≤ min (∑ j ∈ P (i.val + 1), (ψ j).toFun x) 1 - min a 1 ∧
      min (∑ j ∈ P (i.val + 1), (ψ j).toFun x) 1 - min a 1 ≤ b
    rw [hP, Finset.sum_insert (show i ∉ P i.val by simp [P])]
    change 0 ≤ min (b + a) 1 - min a 1 ∧ min (b + a) 1 - min a 1 ≤ b
    constructor
    · exact sub_nonneg.mpr (min_le_min (le_add_of_nonneg_left hb) le_rfl)
    · have h := (lipschitzWith_iff_dist_le_mul.mp (LipschitzWith.id.min_const (1 : ℝ)) (b + a) a)
      simp only [Real.dist_eq, NNReal.coe_one, one_mul, add_sub_cancel_right] at h
      exact (le_abs_self _).trans (h.trans_eq (abs_of_nonneg hb))
  have hSupport (i : Fin n) : support (φ i).toFun ⊆ B i := by
    intro x hx
    by_contra h
    have hzero := notMem_support.mp (fun hh ↦ h (hsupp i hh))
    exact hx (le_antisymm ((hφ i x).2.trans_eq hzero) (hφ i x).1)
  have hG₀ (x : X) : (G 0).toFun x = 0 := by
    change min (∑ j ∈ P 0, (ψ j).toFun x) 1 = 0
    simp [P]
  have hGₙ (x : X) : (G n).toFun x = min (∑ i, (ψ i).toFun x) 1 := by
    change min (∑ j ∈ P n, (ψ j).toFun x) 1 = _
    simp [P]
  refine ⟨φ, hφ, fun i ↦ closure_minimal (hSupport i) (hB i), ?_, ?_⟩
  · intro x
    change (∑ i : Fin n, ((G (i.val + 1)).toFun x - (G i.val).toFun x)) = _
    rw [Fin.sum_univ_eq_sum_range (fun k ↦ (G (k + 1)).toFun x - (G k).toFun x) n,
      Finset.sum_range_sub (fun k ↦ (G k).toFun x),
      hG₀, sub_zero, hGₙ]
  · intro i A hA
    let U := A ∩ B i
    have hU := hA.inter (hB i).measurableSet
    let S (k : ℕ) := (P k).filter (fun j ↦ j ∈ N i)
    let H (k : ℕ) := (finsetSum (S k) ψ).minOne
    have hEq (k : ℕ) : EqOn (G k).toFun (H k).toFun U := by
      intro x hx
      have hsum : (∑ j ∈ P k, (ψ j).toFun x) = ∑ j ∈ S k, (ψ j).toFun x := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro j hj hjS
        apply notMem_support.mp
        intro h
        exact hjS (Finset.mem_filter.mpr ⟨hj, hN i j ⟨x, hx.2, hsupp j h⟩⟩)
      change min (∑ j ∈ P k, (ψ j).toFun x) 1 = min (∑ j ∈ S k, (ψ j).toFun x) 1
      rw [hsum]
    have hpairs : E.energyMeasureRoot U hU (φ i).domainElement =
        E.energyMeasureRoot U hU ((H (i.val + 1)).sub (H i.val)).domainElement := by
      apply root_eq_of_eqOn hU
      intro x hx
      change (G (i.val + 1)).toFun x - (G i.val).toFun x =
        (H (i.val + 1)).toFun x - (H i.val).toFun x
      rw [hEq (i.val + 1) hx, hEq i.val hx]
    have hRestr : E.energyMeasureRoot A hA (φ i).domainElement =
        E.energyMeasureRoot U hU (φ i).domainElement := by
      change E.energyMeasureLaws.root A hA (φ i).domainElement =
        E.energyMeasureLaws.root U hU (φ i).domainElement
      rw [E.energyMeasureLaws.root_apply, E.energyMeasureLaws.root_apply, measureReal_def, measureReal_def,
        (φ i).energyMeasure_apply_inter_of_support (hB i).measurableSet (hSupport i)]
    have hRoot (k : ℕ) : E.energyMeasureRoot U hU (H k).domainElement ≤
        ∑ j ∈ N i, E.energyMeasureRoot A hA (ψ j).domainElement := by
      refine ((finsetSum (S k) ψ).energyMeasureRoot_minOne_le hU).trans ?_
      change E.energyMeasureRoot U hU (∑ j ∈ S k, (ψ j).domainElement) ≤ _
      refine (Finset.map_sum_le_sum (E.energyMeasureRoot U hU) _ _).trans ?_
      refine (Finset.sum_le_sum (fun j _ ↦ E.energyMeasureRoot_mono _ hU hA inter_subset_left)).trans ?_
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (fun j hj ↦ (Finset.mem_filter.mp hj).2) (fun _ _ _ ↦ apply_nonneg _ _)
    rw [hRestr, hpairs]
    change E.energyMeasureRoot U hU ((H (i.val + 1)).domainElement + -(H i.val).domainElement) ≤ _
    apply (map_add_le_add _ _ _).trans
    rw [map_neg_eq_map, two_mul]
    exact add_le_add (hRoot _) (hRoot _)

end WalkDimensions.PEnergy.CompactCore
