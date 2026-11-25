import WalkDimensions.CoreEnergyMeasure
import WalkDimensions.ThinTruncation

/-!
# Energy of pointwise minima and maxima

Removing a thin value interval around the crossing creates two open
sets where the lattice operations agree locally with the original
functions. The interval is removed in the graph norm.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {p : ℝ} (E : PEnergy μ p)

theorem tendsto_energy_sub_of_root_tendsto_zero (f : E.domain) (g : ℕ → E.domain)
    (h : Tendsto (fun n ↦ E.rootSeminorm (g n)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ (E.energy (f - g n) : ℝ)) atTop (𝓝 (E.energy f : ℝ)) := by
  let P := E.rootSeminorm
  have hl (n : ℕ) : P f - P (g n) ≤ P (f - g n) := by
    have hh := P.add_le' (f - g n) (g n)
    change P (f - g n + g n) ≤ P (f - g n) + P (g n) at hh
    rw [sub_add_cancel] at hh
    linarith only [hh]
  have hu (n : ℕ) : P (f - g n) ≤ P f + P (g n) := by
    have hh := P.add_le' f (-g n)
    change P (f + -g n) ≤ P f + P (-g n) at hh
    simpa only [← sub_eq_add_neg, map_neg_eq_map] using hh
  have hconv := tendsto_of_tendsto_of_tendsto_of_le_of_le
    (by simpa only [sub_zero] using h.const_sub (P f))
    (by simpa only [add_zero] using h.const_add (P f)) hl hu
  simpa only [P, Function.comp_def, ← E.energy_eq_root_rpow] using
    ((Real.continuous_rpow_const (zero_lt_one.trans E.one_lt).le).tendsto (P f)).comp hconv

namespace CompactCore

variable {E}

noncomputable def sub (f g : E.CompactCore) : E.CompactCore := f.add g.neg

private noncomputable def positivePart (f : E.CompactCore) : E.CompactCore :=
  f.mapLipschitz (fun t ↦ max t 0) (LipschitzWith.id.max_const 0) (max_self _)

private noncomputable def negativePart (f : E.CompactCore) : E.CompactCore :=
  f.mapLipschitz (fun t ↦ min t 0) (LipschitzWith.id.min_const 0) (min_self _)

private theorem root_positivePart_le (f : E.CompactCore) :
    E.rootSeminorm f.positivePart.domainElement ≤ E.rootSeminorm f.domainElement :=
  f.root_mapLipschitz_le _ _ _

private theorem root_negativePart_le (f : E.CompactCore) :
    E.rootSeminorm f.negativePart.domainElement ≤ E.rootSeminorm f.domainElement :=
  f.root_mapLipschitz_le _ _ _

private theorem min_symmetricClip_eq_min {b t : ℝ} (hb : 0 ≤ b) (ht : -b ≤ t) :
    min (symmetricClip b t) 0 = min t 0 := by
  rw [symmetricClip, max_eq_left ht, min_assoc, min_eq_right hb]

private theorem max_symmetricClip_eq_max {b t : ℝ} (hb : 0 ≤ b) (ht : t ≤ b) :
    max (symmetricClip b t) 0 = max t 0 := by
  rw [symmetricClip, min_eq_left (max_le ht (neg_nonpos.mpr hb |>.trans hb))]
  exact max_assoc _ _ _ |>.trans (by rw [max_eq_right (neg_nonpos.mpr hb)])

variable [LocallyCompactSpace X]

theorem energy_sup_add_min (f g : E.CompactCore) :
    E.energy (f.sup g).domainElement + E.energy (f.minAddConst g (a := 0) le_rfl).domainElement =
      E.energy f.domainElement + E.energy g.domainElement := by
  let h := f.sub g
  let A := g.add h.positivePart
  let B := g.add h.negativePart
  have hA : A.domainElement = (f.sup g).domainElement := by
    apply domainElement_eq_of_toFun_eq
    funext x
    rw [sup_apply]
    change g.toFun x + max (f.toFun x - g.toFun x) 0 = _
    rw [add_max, add_zero]
    congr 1
    ring
  have hB : B.domainElement = (f.minAddConst g (a := 0) le_rfl).domainElement := by
    apply domainElement_eq_of_toFun_eq
    funext x
    change g.toFun x + min (f.toFun x - g.toFun x) 0 = min (f.toFun x) (g.toFun x + 0)
    rw [add_min, add_zero]
    congr 1
    ring
  let δ (n : ℕ) := 1 / ((n : ℝ) + 1)
  have hδ (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  obtain ⟨v, hv, hlim⟩ := E.exists_thin_truncations h.domainElement h.ae_eq h.compactSupport
  let V (n : ℕ) : E.CompactCore :=
    { domainElement := v n
      toFun := symmetricClip (δ n) ∘ h.toFun
      ae_eq := hv n
      continuous := (symmetricClip_lipschitz _).continuous.comp h.continuous
      compactSupport := h.compactSupport.comp_left (symmetricClip_zero (hδ n).le) }
  let F (n : ℕ) := f.sub (V n)
  let A' (n : ℕ) := A.sub (V n).positivePart
  let B' (n : ℕ) := B.sub (V n).negativePart
  have hEq (n : ℕ) : (E.energy (A' n).domainElement : ℝ) + (E.energy (B' n).domainElement : ℝ) =
      (E.energy (F n).domainElement : ℝ) + (E.energy g.domainElement : ℝ) := by
    let U := {x | -δ n < h.toFun x}
    let W := {x | h.toFun x < δ n}
    have hU : IsOpen U := isOpen_lt continuous_const h.continuous
    have hW : IsOpen W := isOpen_lt h.continuous continuous_const
    have hUW : Uᶜ ⊆ W := by
      intro x hx
      change h.toFun x < δ n
      have hn : h.toFun x ≤ -δ n := le_of_not_gt hx
      linarith only [hn, hδ n]
    have hdecomp (x : X) :
        (A' n).toFun x + (B' n).toFun x = (F n).toFun x + g.toFun x := by
      change (g.toFun x + max (h.toFun x) 0) + -max ((V n).toFun x) 0 +
        ((g.toFun x + min (h.toFun x) 0) + -min ((V n).toFun x) 0) =
          f.toFun x + -((V n).toFun x) + g.toFun x
      have h₁ := max_add_min (h.toFun x) 0
      have h₂ := max_add_min ((V n).toFun x) 0
      have h₃ : h.toFun x = f.toFun x - g.toFun x := rfl
      linarith only [h₁, h₂, h₃]
    have hBu : EqOn (B' n).toFun g.toFun U := by
      intro x hx
      change -δ n < h.toFun x at hx
      change (g.toFun x + min (h.toFun x) 0) +
        -min (symmetricClip (δ n) (h.toFun x)) 0 = g.toFun x
      rw [min_symmetricClip_eq_min (hδ n).le hx.le]
      ring
    have hAw : EqOn (A' n).toFun g.toFun W := by
      intro x hx
      change h.toFun x < δ n at hx
      change (g.toFun x + max (h.toFun x) 0) +
        -max (symmetricClip (δ n) (h.toFun x)) 0 = g.toFun x
      rw [max_symmetricClip_eq_max (hδ n).le hx.le]
      ring
    have hAu : EqOn (A' n).toFun (F n).toFun U := by
      intro x hx
      have he := hdecomp x
      rw [hBu hx] at he
      exact add_right_cancel he
    have hBw : EqOn (B' n).toFun (F n).toFun W := by
      intro x hx
      have he := hdecomp x
      rw [hAw hx, add_comm (g.toFun x)] at he
      exact add_right_cancel he
    have hu₁ := (A' n).coreEnergyMeasure_eq_on_open (F n) hU hAu
    have hu₂ := (B' n).coreEnergyMeasure_eq_on_open g hU hBu
    have hw₁ := (A' n).coreEnergyMeasure_eq_on_subset_of_eqOn g hU.measurableSet.compl hW hUW hAw
    have hw₂ := (B' n).coreEnergyMeasure_eq_on_subset_of_eqOn (F n) hU.measurableSet.compl hW hUW hBw
    have hsum : (A' n).coreEnergyMeasure univ + (B' n).coreEnergyMeasure univ =
        (F n).coreEnergyMeasure univ + g.coreEnergyMeasure univ := by
      simp only [← measure_add_measure_compl (s := U) hU.measurableSet, hu₁, hu₂, hw₁, hw₂]
      ac_rfl
    simp only [coreEnergyMeasure_univ, ← ENNReal.coe_add] at hsum
    exact congrArg NNReal.toReal (ENNReal.coe_inj.mp hsum)
  have hzero : Tendsto (fun n ↦ E.rootSeminorm (V n).domainElement) atTop (𝓝 0) :=
    squeeze_zero (fun _ ↦ apply_nonneg _ _) (fun n ↦ E.rootSeminorm_le_graphSeminorm (v n)) hlim
  have hPos : Tendsto (fun n ↦ E.rootSeminorm (V n).positivePart.domainElement) atTop (𝓝 0) :=
    squeeze_zero (fun _ ↦ apply_nonneg _ _) (fun n ↦ (V n).root_positivePart_le) hzero
  have hNeg : Tendsto (fun n ↦ E.rootSeminorm (V n).negativePart.domainElement) atTop (𝓝 0) :=
    squeeze_zero (fun _ ↦ apply_nonneg _ _) (fun n ↦ (V n).root_negativePart_le) hzero
  have ha := E.tendsto_energy_sub_of_root_tendsto_zero A.domainElement _ hPos
  have hb := E.tendsto_energy_sub_of_root_tendsto_zero B.domainElement _ hNeg
  have hf := E.tendsto_energy_sub_of_root_tendsto_zero f.domainElement _ hzero
  have hE := tendsto_nhds_unique_of_forall (ha.add hb) (hf.add_const (E.energy g.domainElement : ℝ))
    (fun n ↦ by simpa only [A', B', F, sub, add, neg, sub_eq_add_neg] using hEq n)
  apply NNReal.eq
  rw [NNReal.coe_add, NNReal.coe_add, ← hA, ← hB]
  exact hE

end CompactCore
end WalkDimensions.PEnergy
