import WalkDimensions.Geometry
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Semicontinuity.Basic

/-!
# The portion of a path after it last leaves a ball
-/

open Metric Set

namespace WalkDimensions

variable {X : Type*} [MetricSpace X]

theorem exists_compact_connected_path_tail {φ : ℝ → X}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1)) {x y : X}
    (hx : φ 0 = x) (hy : φ 1 = y) {a : ℝ} (ha : 0 < a) (hay : a < dist y x) :
    ∃ K : Set X, IsCompact K ∧ IsPreconnected K ∧ K ⊆ φ '' Icc 0 1 ∧ y ∈ K ∧
      (∀ z ∈ K, a ≤ dist z x) ∧ ∃ z ∈ K, dist z x = a := by
  let I := Icc (0 : ℝ) 1
  let d (t : ℝ) := dist (φ t) x
  have hd : ContinuousOn d I := ((continuous_id.dist continuous_const : Continuous (fun z : X ↦ dist z x))).comp_continuousOn hφ
  let S := I ∩ d ⁻¹' Iic a
  have hS : IsCompact S :=
    hd.lowerSemicontinuousOn.isCompact_inter_preimage_Iic isCompact_Icc a
  have h0 : 0 ∈ S := ⟨⟨le_rfl, zero_le_one⟩, by
    change dist (φ 0) x ≤ a
    rw [hx, dist_self]
    exact ha.le⟩
  obtain ⟨t, ht, hmax⟩ := hS.exists_isMaxOn ⟨0, h0⟩ continuous_id.continuousOn
  have htI : t ∈ I := ht.1
  have hdt : d t ≤ a := ht.2
  have hd1 : a < d 1 := by dsimp [d]; rwa [hy]
  have hI : Icc t 1 ⊆ I := fun u hu ↦ ⟨htI.1.trans hu.1, hu.2⟩
  have heq : d t = a := by
    by_contra! hne
    have hlt := lt_of_le_of_ne hdt hne
    have hInter := intermediate_value_Icc htI.2 (hd.mono hI)
    obtain ⟨s, hs, hds⟩ := hInter ⟨hlt.le, hd1.le⟩
    have hsS : s ∈ S := ⟨hI hs, hds.le⟩
    have hst : s = t := le_antisymm (hmax hsS) hs.1
    exact hne (hst ▸ hds)
  let K := φ '' Icc t 1
  refine ⟨K, isCompact_Icc.image_of_continuousOn (hφ.mono hI),
    isPreconnected_Icc.image _ (hφ.mono hI), image_mono hI,
    ⟨1, ⟨htI.2, le_rfl⟩, hy⟩, ?_, ⟨φ t, mem_image_of_mem φ ⟨le_rfl, htI.2⟩, heq⟩⟩
  rintro _ ⟨s, hs, rfl⟩
  by_contra! hlt
  have hsS : s ∈ S := ⟨hI hs, hlt.le⟩
  have hs' : s = t := le_antisymm (hmax hsS) hs.1
  exact hlt.ne (hs' ▸ heq)

end WalkDimensions
