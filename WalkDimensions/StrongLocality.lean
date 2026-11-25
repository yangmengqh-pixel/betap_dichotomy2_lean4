import WalkDimensions.ThinTruncation

/-!
# Locality on the support of a continuous representative

Thin truncations keep the active support inside an open constant region.
This recovers the form of strong locality used by Sasaya's construction.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {m : Measure X} [IsFiniteMeasureOnCompacts m] {p : ℝ} (E : PEnergy m p)

theorem stronglyLocal_of_const_on_support (f g : E.domain) {u v : X → ℝ}
    (hfu : (f : RealLp m p) =ᵐ[m] u) (hgv : (g : RealLp m p) =ᵐ[m] v)
    (hu : Continuous u) (huc : HasCompactSupport u) (hvc : HasCompactSupport v)
    {c : ℝ} (hconst : EqOn v (fun _ ↦ c) (support u)) :
    E.energy (f + g) = E.energy f + E.energy g := by
  obtain ⟨h, hh, hsmall⟩ := E.exists_thin_truncations f hfu huc
  let ε (n : ℕ) := 1 / ((n : ℝ) + 1)
  let uₙ (n : ℕ) (x : X) := u x - symmetricClip (ε n) (u x)
  let fₙ (n : ℕ) := f - h n
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hRep (n : ℕ) : (fₙ n : RealLp m p) =ᵐ[m] uₙ n := by
    filter_upwards [Lp.coeFn_sub (f : RealLp m p) (h n : RealLp m p), hfu, hh n] with x hx hfx hnx
    change ((f : RealLp m p) - (h n : RealLp m p)) x = _
    rw [hx, Pi.sub_apply, hfx, hnx]
    rfl
  have hCompact (n : ℕ) : HasCompactSupport (uₙ n) :=
    huc.comp_left (g := fun a : ℝ ↦ a - symmetricClip (ε n) a)
      (by rw [symmetricClip_zero (hε n).le, sub_zero])
  have hSupport (n : ℕ) : tsupport (uₙ n) ⊆ {x | ε n ≤ |u x|} := by
    apply closure_minimal _ (isClosed_le continuous_const (continuous_abs.comp hu))
    intro x hx
    change ε n ≤ |u x|
    by_contra! hn
    have h := abs_lt.mp hn
    apply hx
    change u x - symmetricClip (ε n) (u x) = 0
    rw [symmetricClip, max_eq_left h.1.le, min_eq_left h.2.le, sub_self]
  have hLocal (n : ℕ) : E.energy (fₙ n + g) = E.energy (fₙ n) + E.energy g := by
    let W : Set X := {x | ε n / 2 < |u x|}
    have hW : IsOpen W := isOpen_lt continuous_const (continuous_abs.comp hu)
    have hsub : tsupport (uₙ n) ⊆ W := fun x hx ↦ (half_lt_self (hε n)).trans_le (hSupport n hx)
    have hWsub : W ⊆ support u := by
      intro x hx
      exact abs_pos.mp ((half_pos (hε n)).trans hx)
    exact E.stronglyLocal (fₙ n) g (uₙ n) v (hRep n) hgv (hCompact n) hvc
      ⟨W, hW, hsub, c, hconst.mono hWsub⟩
  let : SeminormedAddCommGroup E.domain :=
    E.graphSeminorm.toAddGroupSeminorm.toSeminormedAddCommGroup
  have hh₀ : Tendsto h atTop (𝓝 (0 : E.domain)) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact hsmall
  have hfₙ : Tendsto fₙ atTop (𝓝 f) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hh₀
  have hRoot : Continuous E.rootSeminorm := Seminorm.continuous_of_le
    (show Continuous E.graphSeminorm from continuous_norm) E.rootSeminorm_le_graphSeminorm
  have hE : Continuous (fun f : E.domain ↦ (E.energy f : ℝ)) := by
    simp_rw [E.energy_eq_root_rpow]
    exact (Real.continuous_rpow_const (zero_lt_one.trans E.one_lt).le).comp hRoot
  have hSum : Tendsto (fun n ↦ (E.energy (fₙ n + g) : ℝ)) atTop (𝓝 (E.energy (f + g) : ℝ)) :=
    (hE.tendsto (f + g)).comp (hfₙ.add tendsto_const_nhds)
  have hAdd : Tendsto (fun n ↦ (E.energy (fₙ n + g) : ℝ)) atTop
      (𝓝 ((E.energy f : ℝ) + (E.energy g : ℝ))) := by
    have h := ((hE.tendsto f).comp hfₙ).add
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (E.energy g : ℝ)) atTop (𝓝 (E.energy g : ℝ)))
    convert h using 1
    funext n
    rw [hLocal n, NNReal.coe_add]
    rfl
  apply NNReal.eq
  rw [NNReal.coe_add]
  exact tendsto_nhds_unique hSum hAdd

end WalkDimensions.PEnergy
