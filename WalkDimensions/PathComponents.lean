import WalkDimensions.ChainPaths
import WalkDimensions.CoreRestriction
import Mathlib.Topology.Connected.LocallyPathConnected

/-!
# Open path components and restriction of core functions
-/

open Filter Function MeasureTheory Metric Set
open scoped Topology

namespace WalkDimensions

variable {X : Type*} [MetricSpace X]

theorem ChainCondition.locallyPathConnectedSpace [ProperSpace X] (hCC : ChainCondition X) :
    LocallyPathConnectedSpace X := by
  rw [locallyPathConnectedSpace_iff_pathComponentIn_mem_nhds]
  intro x U hU hx
  obtain ⟨r, hr, hBall⟩ := Metric.isOpen_iff.mp hU x hx
  obtain ⟨C, hC, hBound⟩ := hCC.exists_intrinsicDistance_le
  apply Filter.mem_of_superset (ball_mem_nhds x (div_pos hr hC))
  intro y hy
  obtain ⟨θ, hθ⟩ := hCC.exists_lipschitz_path x y
  refine ⟨θ, fun t ↦ hBall (mem_ball.mpr ?_)⟩
  have ht := hθ t 0
  change dist (θ t) (θ 0) ≤ intrinsicDistance x y * |(t : ℝ) - 0| at ht
  rw [θ.source, sub_zero, abs_of_nonneg t.property.1] at ht
  apply ht.trans_lt
  have h := mem_ball.mp hy
  rw [dist_comm y x, lt_div_iff₀ hC, mul_comm] at h
  exact ((mul_le_of_le_one_right (dist_nonneg.trans (dist_le_intrinsicDistance hCC x y)) t.property.2).trans
    (hBound x y)).trans_lt h

theorem isOpen_sdiff_pathComponentIn [LocallyPathConnectedSpace X]
    {U : Set X} (hU : IsOpen U) (x : X) : IsOpen (U \ pathComponentIn U x) := by
  have he : U \ pathComponentIn U x =
      ⋃ y ∈ U \ pathComponentIn U x, pathComponentIn U y := by
    apply subset_antisymm
    · intro z hz
      exact mem_iUnion₂.mpr ⟨z, hz, mem_pathComponentIn_self hz.1⟩
    · intro z hz
      obtain ⟨y, hy, hzy⟩ := mem_iUnion₂.mp hz
      exact ⟨pathComponentIn_subset hzy, fun hz' ↦ hy.2 (hz'.trans hzy.symm)⟩
  rw [he]
  exact isOpen_iUnion fun y ↦ isOpen_iUnion fun _ ↦ hU.pathComponentIn y

theorem disjoint_pathComponentIn_of_not_joinedIn {U : Set X} {x y : X}
    (h : ¬ JoinedIn U x y) : Disjoint (pathComponentIn U x) (pathComponentIn U y) :=
  disjoint_left.mpr fun _ hx hy ↦ h (hx.trans hy.symm)

namespace PEnergy.CompactCore

variable [LocallyCompactSpace X] [LocallyPathConnectedSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {p : ℝ} {E : PEnergy μ p}

theorem exists_core_restrict_pathComponentIn (f : E.CompactCore)
    {U : Set X} (hU : IsOpen U) (hSupp : tsupport f.toFun ⊆ U) (x : X) :
    ∃ w : E.CompactCore, w.toFun = (pathComponentIn U x).indicator f.toFun ∧
      tsupport w.toFun ⊆ pathComponentIn U x ∧ E.energy w.domainElement ≤ E.energy f.domainElement := by
  have hS : IsCompact (tsupport f.toFun ∩ pathComponentIn U x) := by
    have he : tsupport f.toFun ∩ pathComponentIn U x =
        tsupport f.toFun ∩ (U \ pathComponentIn U x)ᶜ := by
      ext z
      exact ⟨fun h ↦ ⟨h.1, fun hn ↦ hn.2 h.2⟩, fun h ↦
        ⟨h.1, by_contra fun hn ↦ h.2 ⟨hSupp h.1, hn⟩⟩⟩
    rw [he]
    exact f.compactSupport.isCompact.inter_right (isOpen_sdiff_pathComponentIn hU x).isClosed_compl
  exact f.exists_core_restrict_of_compact_support_inter (hU.pathComponentIn x) hS

end PEnergy.CompactCore

end WalkDimensions
