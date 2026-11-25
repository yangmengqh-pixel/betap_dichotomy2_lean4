import WalkDimensions.EnergyClarkson

/-!
# Local sums of compactly supported functions

Strong locality makes energy additive on a finite family of disjoint
topological supports. This applies to measurable representatives.
-/

open Filter Function MeasureTheory Set

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {m : Measure X} [IsFiniteMeasureOnCompacts m] {p : ℝ} (E : PEnergy m p)

theorem coeFn_finsetSum {ι : Type*} (t : Finset ι) (f : ι → E.domain)
    (u : ι → X → ℝ) (hfu : ∀ i ∈ t, (f i : RealLp m p) =ᵐ[m] u i) :
    ((∑ i ∈ t, f i : E.domain) : RealLp m p) =ᵐ[m] fun x ↦ ∑ i ∈ t, u i x := by
  rw [E.domain.coe_sum]
  have hall := (Filter.eventually_all_finset t).mpr hfu
  filter_upwards [Lp.coeFn_fun_finsetSum t (fun i ↦ (f i : RealLp m p)), hall] with x hx hu
  exact hx.trans (Finset.sum_congr rfl fun i hi ↦ hu i hi)

/-- Energy adds over a finite family with pairwise disjoint supports. -/
theorem energy_finsetSum_of_disjoint_tsupport {ι : Type*} (t : Finset ι)
    (f : ι → E.domain) (u : ι → X → ℝ)
    (hfu : ∀ i ∈ t, (f i : RealLp m p) =ᵐ[m] u i)
    (hu : ∀ i ∈ t, HasCompactSupport (u i))
    (hdisj : (↑t : Set ι).PairwiseDisjoint (fun i ↦ tsupport (u i))) :
    E.energy (∑ i ∈ t, f i) = ∑ i ∈ t, E.energy (f i) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    apply NNReal.eq
    simp only [E.energy_eq_root_rpow, map_zero, Real.zero_rpow
      (zero_lt_one.trans E.one_lt).ne', NNReal.coe_zero]
  | insert i t hit ih =>
    have hsub : (↑t : Set ι) ⊆ ↑(insert i t) := fun j hj ↦ Finset.mem_insert_of_mem hj
    have hfu' (j : ι) (hj : j ∈ t) := hfu j (hsub hj)
    have hu' (j : ι) (hj : j ∈ t) := hu j (hsub hj)
    let v := fun x ↦ ∑ j ∈ t, u j x
    let K := ⋃ j ∈ t, tsupport (u j)
    have hK : IsCompact K := t.isCompact_biUnion (fun j hj ↦ (hu' j hj).isCompact)
    have hts : tsupport v ⊆ K := by
      apply closure_minimal _ hK.isClosed
      intro x hx
      by_contra hxK
      apply hx
      apply Finset.sum_eq_zero
      intro j hj
      exact notMem_support.mp (fun h ↦ hxK (mem_iUnion₂.mpr ⟨j, hj, subset_closure h⟩))
    have hv : HasCompactSupport v := hK.of_isClosed_subset isClosed_closure hts
    have huv : tsupport (u i) ⊆ (tsupport v)ᶜ := by
      intro x hx hxv
      obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp (hts hxv)
      exact (disjoint_left.mp (hdisj (Finset.mem_insert_self _ _) (hsub hj)
        (fun h ↦ hit (h ▸ hj)))) hx hxj
    have hlocal := E.stronglyLocal (f i) (∑ j ∈ t, f j) (u i) v
      (hfu i (Finset.mem_insert_self _ _)) (E.coeFn_finsetSum t f u hfu')
      (hu i (Finset.mem_insert_self _ _)) hv
      ⟨(tsupport v)ᶜ, isClosed_closure.isOpen_compl, huv, 0,
        fun x hx ↦ notMem_support.mp (fun hs ↦ hx (subset_closure hs))⟩
    rw [Finset.sum_insert hit, Finset.sum_insert hit, hlocal,
      ih hfu' hu' (fun x hx y hy hxy ↦ hdisj (hsub hx) (hsub hy) hxy)]

end WalkDimensions.PEnergy
