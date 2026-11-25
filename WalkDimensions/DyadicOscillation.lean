import WalkDimensions.OscillatoryTruncation

/-!
# Identities for nested oscillations

The estimates use the reflection of the sawtooth at each dyadic refinement.
-/

namespace WalkDimensions

noncomputable def oscillationWidth (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n

theorem oscillationWidth_pos (n : ℕ) : 0 < oscillationWidth n := by
  unfold oscillationWidth
  positivity

theorem oscillationWidth_succ (n : ℕ) :
    oscillationWidth (n + 1) = oscillationWidth n / 2 := by
  simp only [oscillationWidth, pow_succ, div_eq_mul_inv, one_mul]

theorem oscillationWidth_antitone : Antitone oscillationWidth :=
  antitone_nat_of_succ_le fun n ↦ by
    rw [oscillationWidth_succ]
    linarith only [oscillationWidth_pos n]

theorem sawtooth_oscillationWidth_comp {n m : ℕ} (hnm : n ≤ m) (t : ℝ) :
    sawtooth (oscillationWidth m) (sawtooth (oscillationWidth n) t) =
      sawtooth (oscillationWidth m) t := by
  induction m, hnm using Nat.le_induction with
  | base =>
      have ht : 0 ≤ sawtooth (oscillationWidth n) t := sawtooth_nonneg _ _
      rw [sawtooth_eq_abs_of_abs_le (oscillationWidth_pos n), abs_of_nonneg ht]
      rw [abs_of_nonneg ht]
      exact sawtooth_le (oscillationWidth_pos n) t
  | succ m _ ih =>
      simp only [oscillationWidth_succ, sawtooth_half _ (oscillationWidth_pos m), ih]

theorem sawtooth_oscillationWidth_near_cap {n m : ℕ} (hnm : n < m)
    {t : ℝ} (ht : 0 ≤ t) (htm : t ≤ oscillationWidth m) :
    sawtooth (oscillationWidth m) (oscillationWidth n - t) = t := by
  induction m, hnm using Nat.le_induction with
  | base =>
      have hhalf : t ≤ oscillationWidth n / 2 := by
        rwa [← oscillationWidth_succ]
      have harg : 0 ≤ oscillationWidth n - t := by
        linarith only [hhalf, oscillationWidth_pos n]
      have hbase : sawtooth (oscillationWidth n) (oscillationWidth n - t) =
          oscillationWidth n - t := by
        rw [sawtooth_eq_abs_of_abs_le (oscillationWidth_pos n), abs_of_nonneg harg]
        rw [abs_of_nonneg harg]
        linarith only [ht]
      rw [oscillationWidth_succ, sawtooth_half _ (oscillationWidth_pos n), hbase,
        show oscillationWidth n - (oscillationWidth n - t) = t by ring,
        min_eq_right (by linarith only [hhalf])]
  | succ m _ ih =>
      rw [oscillationWidth_succ, sawtooth_half _ (oscillationWidth_pos m)]
      rw [ih (htm.trans (oscillationWidth_antitone (Nat.le_succ m)))]
      rw [min_eq_left]
      rw [oscillationWidth_succ] at htm
      linarith only [htm]

theorem localized_oscillation_refine {n m : ℕ} (hnm : n < m) (a u v : ℝ) :
    min (sawtooth (oscillationWidth m) u) (sublevelRamp (oscillationWidth m) a v) =
      min (min (sawtooth (oscillationWidth m)
        (min (sawtooth (oscillationWidth n) u) (sublevelRamp (oscillationWidth n) a v)))
        (sublevelRamp (oscillationWidth m) a v))
        (min (oscillationWidth n - sawtooth (oscillationWidth n) u) (oscillationWidth m)) := by
  let s := oscillationWidth n
  let r := oscillationWidth m
  let U := sawtooth s u
  have hrs : r ≤ s := oscillationWidth_antitone hnm.le
  have hr : 0 < r := oscillationWidth_pos m
  have hU : U ≤ s := sawtooth_le (oscillationWidth_pos n) _
  have hcap : 0 ≤ min (s - U) r := le_min (sub_nonneg.mpr hU) hr.le
  change min (sawtooth r u) (sublevelRamp r a v) =
    min (min (sawtooth r (min U (sublevelRamp s a v))) (sublevelRamp r a v))
      (min (s - U) r)
  by_cases hfar : a + r ≤ v
  · simp only [sublevelRamp_eq_zero hfar, min_eq_right (sawtooth_nonneg r _),
      min_eq_left hcap]
  have hnear : s - r ≤ sublevelRamp s a v := by
    apply le_max_of_le_left
    apply le_min <;> linarith only [lt_of_not_ge hfar, hr]
  have hnest : sawtooth r U = sawtooth r u := sawtooth_oscillationWidth_comp hnm.le _
  by_cases hUfar : U ≤ s - r
  · rw [min_eq_left (hUfar.trans hnear), hnest, min_eq_right (by linarith only [hUfar] : r ≤ s - U),
      min_eq_left ((min_le_left _ _).trans (sawtooth_le hr _))]
  have hclose (x : ℝ) (hx : s - r ≤ x) (hxs : x ≤ s) :
      sawtooth r x = s - x := by
    have he := sawtooth_oscillationWidth_near_cap hnm (sub_nonneg.mpr hxs)
      (show s - x ≤ r by linarith only [hx])
    change sawtooth r (s - (s - x)) = s - x at he
    rwa [sub_sub_cancel] at he
  have hUclose := hclose U (le_of_not_ge hUfar) hU
  rw [← hnest, hUclose, min_eq_left (by linarith only [lt_of_not_ge hUfar] : s - U ≤ r)]
  rw [hclose _ (le_min (le_of_not_ge hUfar) hnear) ((min_le_left _ _).trans hU)]
  have hle := sub_le_sub_left (min_le_left U (sublevelRamp s a v)) s
  rw [min_right_comm, min_eq_right hle, min_comm]

end WalkDimensions
