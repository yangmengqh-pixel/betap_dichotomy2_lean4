import WalkDimensions.StrongLocality

/-!
# Preservation of energy under folding values

The two sides of the folding level have additive energy. Reflecting the
upper portion changes its sign and preserves that energy.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {m : Measure X} [IsFiniteMeasureOnCompacts m] {p : ℝ} (E : PEnergy m p)

theorem exists_reflected_at_level (f : E.domain) {u : X → ℝ}
    (hfu : (f : RealLp m p) =ᵐ[m] u) (hu : Continuous u) (hc : HasCompactSupport u)
    {a : ℝ} (ha : 0 ≤ a) :
    ∃ g : E.domain, (g : RealLp m p) =ᵐ[m] (fun x ↦ min (u x) a - max (u x - a) 0) ∧
      E.energy g = E.energy f := by
  obtain ⟨l, h, hl, hh, _, hsum⟩ := E.exists_split_energy_at_level f hfu hu hc ha
  let L : X → ℝ := fun x ↦ min (u x) a
  let H : X → ℝ := fun x ↦ -max (u x - a) 0
  have hl' : (l : RealLp m p) =ᵐ[m] L := hl
  have hH : ((-h : E.domain) : RealLp m p) =ᵐ[m] H := by
    filter_upwards [Lp.coeFn_neg (h : RealLp m p), hh] with x hx hhx
    change (-(h : RealLp m p)) x = H x
    rw [hx, Pi.neg_apply, hhx]
  have hLc : HasCompactSupport L := hc.comp_left (g := fun t : ℝ ↦ min t a) (min_eq_left ha)
  have hHc : HasCompactSupport H := hc.comp_left (g := fun t : ℝ ↦ -max (t - a) 0) (by
    simp only [zero_sub, max_eq_right (neg_nonpos.mpr ha), neg_zero])
  have hHcont : Continuous H := ((hu.sub continuous_const).max continuous_const).neg
  have hconst : EqOn L (fun _ ↦ a) (support H) := by
    intro x hx
    by_contra h
    have hu₁ : a ≤ u x := by
      by_contra! hn
      exact hx (by simp only [H, max_eq_right (sub_nonpos.mpr hn.le), neg_zero])
    exact h (min_eq_right hu₁)
  have hloc := E.stronglyLocal_of_const_on_support (-h) l hH hl' hHcont hHc hLc hconst
  refine ⟨l - h, ?_, ?_⟩
  · filter_upwards [Lp.coeFn_sub (l : RealLp m p) (h : RealLp m p), hl, hh] with x hx hlx hhx
    change ((l : RealLp m p) - (h : RealLp m p)) x = _
    rw [hx, Pi.sub_apply, hlx, hhx]
  · have hneg : E.energy (-h) = E.energy h := by
      apply NNReal.eq
      rw [E.energy_eq_root_rpow, E.energy_eq_root_rpow, map_neg_eq_map]
    rw [sub_eq_add_neg, add_comm, hloc, hneg, add_comm, ← hsum]

theorem exists_abs_energy_eq (f : E.domain) {u : X → ℝ}
    (hfu : (f : RealLp m p) =ᵐ[m] u) (hu : Continuous u) (hc : HasCompactSupport u) :
    ∃ g : E.domain, (g : RealLp m p) =ᵐ[m] (fun x ↦ |u x|) ∧ E.energy g = E.energy f := by
  obtain ⟨g, hg, hgE⟩ := E.exists_reflected_at_level f hfu hu hc (a := 0) (le_refl _)
  refine ⟨-g, ?_, ?_⟩
  · filter_upwards [Lp.coeFn_neg (g : RealLp m p), hg] with x hx hgx
    change (-(g : RealLp m p)) x = _
    rw [hx, Pi.neg_apply, hgx, sub_zero]
    rcases le_total (u x) 0 with h | h
    · rw [min_eq_left h, max_eq_right h, sub_zero, abs_of_nonpos h]
    · rw [min_eq_right h, max_eq_left h, abs_of_nonneg h]
      ring
  · apply NNReal.eq
    rw [E.energy_eq_root_rpow, map_neg_eq_map, ← E.energy_eq_root_rpow, hgE]

theorem exists_fold_energy_eq (f : E.domain) {u : X → ℝ}
    (hfu : (f : RealLp m p) =ᵐ[m] u) (hu : Continuous u) (hc : HasCompactSupport u)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    ∃ g : E.domain, (g : RealLp m p) =ᵐ[m] (fun x ↦ min (u x) (δ - u x)) ∧
      E.energy g = E.energy f := by
  obtain ⟨g, hg, hgE⟩ := E.exists_reflected_at_level f hfu hu hc (a := δ / 2) (by positivity)
  refine ⟨g, hg.mono fun x hx ↦ ?_, hgE⟩
  rw [hx]
  change min (u x) (δ / 2) - max (u x - δ / 2) 0 = min (u x) (δ - u x)
  rcases le_total (u x) (δ / 2) with h | h
  · rw [min_eq_left h, max_eq_right (sub_nonpos.mpr h), sub_zero,
      min_eq_left (by linarith)]
  · rw [min_eq_right h, max_eq_left (sub_nonneg.mpr h), min_eq_right (by linarith)]
    ring

end WalkDimensions.PEnergy
