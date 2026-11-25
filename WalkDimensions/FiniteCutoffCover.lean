import WalkDimensions.DoublingCovers

/-!
# Packing and overlap for finite cutoff covers
-/

open Function MeasureTheory Metric Set
open scoped ENNReal

namespace WalkDimensions

variable {X : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X] [BorelSpace X]
  {m : Measure X} [IsFiniteMeasureOnCompacts m] [m.IsOpenPosMeasure]

theorem exists_uniform_cutoff_cover_overlap (hvol : VolumeDoubling m) {A : ℝ} (hA : 0 ≤ A) :
    ∃ N : ℕ, 0 < N ∧ ∀ {n : ℕ} (z : Fin n → X) {s : ℝ}, 0 < s →
      (∀ i j, i ≠ j → s ≤ dist (z i) (z j)) →
      (∀ i, (Finset.univ.filter (fun j ↦ dist (z j) (z i) ≤ 2 * A * s)).card ≤ N) ∧
      ∀ (ν : Measure X) {S : Set X}, MeasurableSet S →
        (∑ i, ν (S ∩ closedBall (z i) (A * s))) ≤ (N : ℝ≥0∞) * ν S := by
  classical
  obtain ⟨N, hN, hPack⟩ := exists_card_le_of_separated_centres hvol (R := 4 * A) (by positivity)
  refine ⟨N, hN, fun {n} z {s} hs hz ↦ ?_⟩
  have hInj : Injective z := by
    intro i j he
    by_contra hne
    have h := hz i j hne
    rw [he, dist_self] at h
    exact hs.not_ge h
  let e : Fin n ↪ X := ⟨z, hInj⟩
  have hCard (x : X) (t : Finset (Fin n))
      (h : ∀ i ∈ t, dist (z i) x ≤ 2 * A * s) : t.card ≤ N := by
    rw [← Finset.card_map e]
    apply hPack x (s / 2) (half_pos hs)
    · intro y hy
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hy
      rw [show 4 * A * (s / 2) = 2 * A * s by ring]
      exact h i hi
    · intro y hy w hw hne
      obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hy
      obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hw
      rw [show 2 * (s / 2) = s by ring]
      exact hz i j (fun he ↦ hne (congrArg z he))
  refine ⟨fun i ↦ hCard (z i) _ (fun j hj ↦ (Finset.mem_filter.mp hj).2), ?_⟩
  intro ν S _hS
  let B (i : Fin n) := closedBall (z i) (A * s)
  have hAt (x : X) : (Finset.univ.filter (fun i ↦ x ∈ B i)).card ≤ N := by
    apply hCard x
    intro i hi
    have h := mem_closedBall.mp (Finset.mem_filter.mp hi).2
    rw [dist_comm]
    exact h.trans (by nlinarith)
  have hEq (i : Fin n) : (∫⁻ x, (B i).indicator (fun _ : X ↦ (1 : ℝ≥0∞)) x ∂ν.restrict S) =
      ν (S ∩ B i) := by
    rw [lintegral_indicator measurableSet_closedBall, setLIntegral_const, one_mul,
      Measure.restrict_apply measurableSet_closedBall, inter_comm]
  calc
    _ = ∑ i, ∫⁻ x, (B i).indicator (fun _ : X ↦ (1 : ℝ≥0∞)) x ∂ν.restrict S := by
      simp_rw [hEq]
      rfl
    _ = ∫⁻ x, ∑ i, (B i).indicator (fun _ : X ↦ (1 : ℝ≥0∞)) x ∂ν.restrict S :=
      (lintegral_finsetSum _ (fun i _ ↦ measurable_const.indicator measurableSet_closedBall)).symm
    _ ≤ ∫⁻ _ : X, (N : ℝ≥0∞) ∂ν.restrict S := by
      apply lintegral_mono
      intro x
      simp only [indicator_apply, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      exact_mod_cast hAt x
    _ = _ := by simp

theorem exists_indexed_separated_ball_cover {A τ : ℝ} (hvol : VolumeDoubling m)
    (hA : 0 ≤ A) (hτ : 0 < τ) :
    ∃ N : ℕ, 0 < N ∧ ∀ (x : X) {r : ℝ}, 0 < r →
      ∃ (n : ℕ) (z : Fin n → X), n ≤ N ∧ (∀ i, z i ∈ closedBall x (A * r)) ∧
        (∀ i j, i ≠ j → τ * r ≤ dist (z i) (z j)) ∧
        closedBall x (A * r) ⊆ ⋃ i, ball (z i) (τ * r) := by
  classical
  obtain ⟨N, hN, hPack⟩ := exists_card_le_of_separated_centres hvol
    (R := 2 * A / τ) (by positivity)
  refine ⟨N, hN, fun x r hr ↦ ?_⟩
  have hs : 0 < τ * r := mul_pos hτ hr
  obtain ⟨t, ht, hsep, hcover⟩ := exists_finset_separated_ball_cover (isCompact_closedBall x (A * r)) hs
  let e : Fin t.card ≃ t := (Fintype.equivFinOfCardEq (Fintype.card_coe t)).symm
  let z (i : Fin t.card) : X := e i
  have hscale : 2 * A / τ * (τ * r / 2) = A * r := by
    field_simp
  refine ⟨t.card, z, hPack x (τ * r / 2) (half_pos hs) t ?_ ?_, fun i ↦ ht (e i).property, ?_, ?_⟩
  · intro y hy
    rw [hscale]
    exact mem_closedBall.mp (ht hy)
  · rw [show 2 * (τ * r / 2) = τ * r by ring]
    exact hsep
  · intro i j hij
    exact hsep (e i).property (e j).property (fun he ↦ hij (e.injective (Subtype.ext he)))
  · intro y hy
    obtain ⟨w, hw, hyw⟩ := mem_iUnion₂.mp (hcover hy)
    obtain ⟨i, hi⟩ := e.surjective ⟨w, hw⟩
    refine mem_iUnion.mpr ⟨i, ?_⟩
    change y ∈ ball (e i : X) (τ * r)
    rwa [hi]

end WalkDimensions
