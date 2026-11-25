import WalkDimensions.DoublingCovers
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Uniform chains through compact connected subsets

The intersection graph of a separated ball cover connects centres along
the compact set. Packing bounds the length of a simple path in that graph.
-/

open MeasureTheory Metric Set

namespace WalkDimensions

variable {X : Type*} [MetricSpace X]

private theorem reachable_of_ball_cover {K : Set X} (hconn : IsPreconnected K)
    {t : Finset X} (ht : (↑t : Set X) ⊆ K) {s : ℝ} (hs : 0 < s)
    (hcov : K ⊆ ⋃ z ∈ t, ball z s) :
    let G : SimpleGraph (↥t) :=
      { Adj := fun x y ↦ x ≠ y ∧ dist (x : X) (y : X) < 2 * s
        symm := ⟨fun x y h ↦ ⟨h.1.symm, by rw [dist_comm (y : X) (x : X)]; exact h.2⟩⟩
        loopless := ⟨fun _ h ↦ h.1 rfl⟩ }
    ∀ x y : ↥t, G.Reachable x y := by
  classical
  dsimp only
  intro x y
  let G : SimpleGraph (↥t) :=
    { Adj := fun x y ↦ x ≠ y ∧ dist (x : X) (y : X) < 2 * s
      symm := ⟨fun x y h ↦ ⟨h.1.symm, by rw [dist_comm (y : X) (x : X)]; exact h.2⟩⟩
      loopless := ⟨fun _ h ↦ h.1 rfl⟩ }
  change G.Reachable x y
  let U := ⋃ u : ↥t, ⋃ (_ : G.Reachable x u), ball (u : X) s
  let V := ⋃ v : ↥t, ⋃ (_ : ¬ G.Reachable x v), ball (v : X) s
  have hU : IsOpen U := isOpen_iUnion fun _ ↦ isOpen_iUnion fun _ ↦ isOpen_ball
  have hV : IsOpen V := isOpen_iUnion fun _ ↦ isOpen_iUnion fun _ ↦ isOpen_ball
  have hUV : Disjoint U V := by
    refine disjoint_left.mpr fun z hz hz' ↦ ?_
    obtain ⟨u, hu, hzu⟩ := mem_iUnion₂.mp hz
    obtain ⟨v, hv, hzv⟩ := mem_iUnion₂.mp hz'
    have huv : u ≠ v := fun h ↦ hv (h ▸ hu)
    have hed : G.Adj u v := ⟨huv, (dist_triangle (u : X) z (v : X)).trans_lt (by
      rw [dist_comm (u : X) z]
      linarith only [mem_ball.mp hzu, mem_ball.mp hzv])⟩
    exact hv (hu.trans hed.reachable)
  have hAll : K ⊆ U ∪ V := by
    intro z hz
    obtain ⟨v, hv, hzv⟩ := mem_iUnion₂.mp (hcov hz)
    let w : ↥t := ⟨v, hv⟩
    by_cases h : G.Reachable x w
    · exact Or.inl (mem_iUnion₂.mpr ⟨w, h, hzv⟩)
    · exact Or.inr (mem_iUnion₂.mpr ⟨w, h, hzv⟩)
  have hX : (x : X) ∈ U := mem_iUnion₂.mpr ⟨x, SimpleGraph.Reachable.refl _, mem_ball_self hs⟩
  have hLeft : K ⊆ U := hconn.subset_left_of_subset_union hU hV hUV hAll ⟨x, ht x.property, hX⟩
  by_contra hy
  exact disjoint_left.mp hUV (hLeft (ht y.property)) (mem_iUnion₂.mpr ⟨y, hy, mem_ball_self hs⟩)

variable [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [ProperSpace X]
  [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]

theorem VolumeDoubling.exists_short_chain_in_compact_connected_set (hvol : VolumeDoubling μ)
    {L b : ℝ} (hL : 0 ≤ L) (hb : 0 < b) :
    ∃ N : ℕ, ∀ (o : X) (r : ℝ), 0 < r →
      ∀ {K : Set X}, IsCompact K → IsPreconnected K → K ⊆ closedBall o (L * r) →
      ∀ x ∈ K, ∀ y ∈ K, ∃ (n : ℕ) (v : ℕ → X), n ≤ N ∧ v 0 = x ∧ v n = y ∧
        (∀ k ≤ n, v k ∈ K) ∧ ∀ k < n, dist (v k) (v (k + 1)) ≤ b * r := by
  classical
  obtain ⟨N, _, hpack⟩ := exists_card_le_of_separated_centres hvol
    (R := 4 * L / b) (div_nonneg (mul_nonneg (by norm_num) hL) hb.le)
  refine ⟨N + 2, fun o r hr K hK hconn hKB x hx y hy ↦ ?_⟩
  let s := b * r / 2
  have hs : 0 < s := half_pos (mul_pos hb hr)
  have hsw : s ≤ b * r := half_le_self (mul_pos hb hr).le
  obtain ⟨t, ht, hsep, hcov⟩ := exists_finset_separated_ball_cover hK hs
  have hcard : t.card ≤ N := by
    apply hpack o (s / 2) (half_pos hs)
    · intro z hz
      have hz' := mem_closedBall.mp (hKB (ht hz))
      have he : (4 * L / b) * (s / 2) = L * r := by dsimp [s]; field_simp; ring
      rwa [he]
    · intro x hx y hy hxy
      rw [show 2 * (s / 2) = s by ring]
      exact hsep hx hy hxy
  let G : SimpleGraph (↥t) :=
    { Adj := fun u v ↦ u ≠ v ∧ dist (u : X) (v : X) < 2 * s
      symm := ⟨fun x y h ↦ ⟨h.1.symm, by rw [dist_comm (y : X) (x : X)]; exact h.2⟩⟩
      loopless := ⟨fun _ h ↦ h.1 rfl⟩ }
  obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.mp (hcov hx)
  obtain ⟨v, hv, hyv⟩ := mem_iUnion₂.mp (hcov hy)
  let u' : ↥t := ⟨u, hu⟩
  let v' : ↥t := ⟨v, hv⟩
  have hR : G.Reachable u' v' := reachable_of_ball_cover hconn ht hs hcov u' v'
  obtain ⟨P, hP⟩ := hR.exists_isPath
  let n := P.length
  have hN : n ≤ N := hP.length_lt_natCard.le.trans (by simpa using hcard)
  let w (k : ℕ) : X := if k = 0 then x else if k ≤ n + 1 then (P.getVert (k - 1) : X) else y
  refine ⟨n + 2, w, by omega, by simp [w], by simp [w], ?_, ?_⟩
  · intro k hk
    unfold w
    split
    · exact hx
    split
    · exact ht (P.getVert _).property
    · exact hy
  · intro k hk
    by_cases hk0 : k = 0
    · subst k
      have hl : (1 : ℕ) ≤ n + 1 := by omega
      simpa only [w, ite_eq_left rfl, Nat.zero_add, Nat.one_ne_zero, ite_false, ite_eq_left hl, Nat.sub_self,
        SimpleGraph.Walk.getVert_zero] using
        (mem_ball.mp hxu).le.trans hsw
    by_cases hk1 : k = n + 1
    · have he : w k = v := by
        dsimp only [w]
        rw [ite_eq_right hk0, ite_eq_left (le_of_eq hk1), hk1, Nat.add_sub_cancel,
          SimpleGraph.Walk.getVert_length]
      have he' : w (k + 1) = y := by
        unfold w
        rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      rw [he, he', dist_comm]
      exact (mem_ball.mp hyv).le.trans hsw
    have hlt : k - 1 < n := by omega
    have he : w k = P.getVert (k - 1) := by
      dsimp only [w]
      rw [ite_eq_right hk0, ite_eq_left (by omega)]
    have he' : w (k + 1) = P.getVert (k - 1 + 1) := by
      dsimp only [w]
      rw [ite_eq_right (by omega), ite_eq_left (by omega), show k + 1 - 1 = k - 1 + 1 by omega]
    rw [he, he']
    have hh := (P.adj_getVert_succ hlt).2
    exact hh.le.trans_eq (by dsimp [s]; ring)

end WalkDimensions
