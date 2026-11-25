import WalkDimensions.EnergyTruncation
import Mathlib.Topology.UrysohnsLemma

/-!
# Cutoffs in the continuous energy core

Regularity and a scalar clipping operation furnish cutoffs between
compact sets and open neighbourhoods.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {m : Measure X} [IsFiniteMeasureOnCompacts m] {p : ℝ} (E : PEnergy m p)

theorem exists_core_cutoff_of_isCompact_subset_isOpen {K U : Set X}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (f : E.domain) (u : X → ℝ), Continuous u ∧ HasCompactSupport u ∧
      (f : RealLp m p) =ᵐ[m] u ∧ (∀ x, u x ∈ Icc (0 : ℝ) 1) ∧
      EqOn u (fun _ ↦ 1) K ∧ tsupport u ⊆ U := by
  obtain ⟨v, hv1, hvc, hvU, _⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK hU hKU
  obtain ⟨g, hg, hgc, hgm, ε, hε, hclose⟩ :=
    E.regular_uniform v v.continuous hvc (1 / 4) (by norm_num)
  let F : E.domain := ⟨continuousLp p g hg hgc, hgm⟩
  have hF : (F : RealLp m p) =ᵐ[m] g := MemLp.coeFn_toLp (hg.memLp_of_hasCompactSupport hgc)
  obtain ⟨f, hf, _⟩ := E.exists_unitClip_comp F hF (a := 1 / 4) (b := 3 / 4)
    (by norm_num) (by norm_num)
  let u : X → ℝ := unitClip (1 / 4) (3 / 4) ∘ g
  have hu : Continuous u := ((hg.sub continuous_const).div_const _).max continuous_const |>.min continuous_const
  have huc : HasCompactSupport u := hgc.comp_left (unitClip_eq_zero (by norm_num) (by norm_num))
  refine ⟨f, u, hu, huc, hf, fun x ↦ unitClip_mem_Icc _ _ _, ?_, ?_⟩
  · intro x hx
    have h₁ := hv1 hx
    change v x = 1 at h₁
    have h₂ := (abs_le.mp (hclose x)).1
    rw [h₁] at h₂
    exact unitClip_eq_one (by norm_num) (by linarith)
  · apply Subset.trans (closure_minimal _ isClosed_closure) hvU
    intro x hx
    by_contra hxv
    have h₀ : v x = 0 := notMem_support.mp fun h ↦ hxv (subset_closure h)
    have h₂ := (abs_le.mp (hclose x)).2
    rw [h₀, sub_zero] at h₂
    exact hx (unitClip_eq_zero (by norm_num) (by linarith))

end WalkDimensions.PEnergy
