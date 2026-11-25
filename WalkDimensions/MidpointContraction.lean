import WalkDimensions.CompactEnergyLimit
import WalkDimensions.EnergyMidpointLimit
import WalkDimensions.EnergyTruncation

/-!
# Contractions of midpoints

These estimates combine pointwise midpoint identities with energy
closedness on a fixed support.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {m : Measure X} [IsFiniteMeasureOnCompacts m] {p : ℝ} (E : PEnergy m p)

theorem root_le_midpoint_of_lipschitz_comp (f g h : E.domain) {u v w : X → ℝ}
    (hfu : (f : RealLp m p) =ᵐ[m] u) (hgv : (g : RealLp m p) =ᵐ[m] v)
    (hhw : (h : RealLp m p) =ᵐ[m] w) {φ : ℝ → ℝ}
    (hφ : LipschitzWith 1 φ) (hφ₀ : φ 0 = 0)
    (hW : ∀ x, w x = φ ((u x + v x) / 2)) :
    E.rootSeminorm h ≤ E.rootSeminorm ((1 / 2 : ℝ) • (f + g)) := by
  let F := (f : RealLp m p)
  let G := (g : RealLp m p)
  let k := (1 / 2 : ℝ) • (f + g)
  have hk : (k : RealLp m p) =ᵐ[m] (fun x ↦ (u x + v x) / 2) := by
    filter_upwards [Lp.coeFn_smul (1 / 2 : ℝ) (F + G), Lp.coeFn_add F G, hfu, hgv]
      with x hx hsum hfx hgx
    change ((1 / 2 : ℝ) • (F + G)) x = _
    rw [hx, Pi.smul_apply, smul_eq_mul, hsum, Pi.add_apply, hfx, hgx]
    ring
  obtain ⟨v', hv', hvE⟩ := E.exists_lipschitz_one_comp k hk φ hφ hφ₀
  have he : h = v' := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [hhw, hv'] with x hx hx'
    rw [hx, hx']
    exact hW x
  rw [he, E.rootSeminorm_apply, E.rootSeminorm_apply]
  exact Real.rpow_le_rpow (NNReal.coe_nonneg _) (NNReal.coe_le_coe.mpr hvE)
    (inv_nonneg.mpr (zero_lt_one.trans E.one_lt).le)

theorem tendsto_graph_zero_of_uniform_bound_midpoint_control
    (f : ℕ → E.domain) (u : ℕ → X → ℝ)
    (hfu : ∀ n, (f n : RealLp m p) =ᵐ[m] u n)
    {S : Set X} (hS : MeasurableSet S) (hSfin : m S ≠ ∞)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (hlim : Tendsto ε atTop (𝓝 0))
    (hBound : ∀ n x, |u n x| ≤ S.indicator (fun _ ↦ ε n) x)
    (hmid : ∀ i j n : ℕ, i ≤ n → j ≤ n →
      E.rootSeminorm (f n) ≤ E.rootSeminorm ((1 / 2 : ℝ) • (f i + f j))) :
    Tendsto (fun n ↦ E.graphSeminorm (f n)) atTop (𝓝 0) := by
  let _ : Fact (1 ≤ ENNReal.ofReal p) := ⟨by simpa using E.one_lt.le⟩
  let D := (m.real S) ^ p⁻¹
  have hLpBound (n : ℕ) : ‖(f n : RealLp m p)‖ ≤ ε n * D := by
    apply norm_realLp_le_of_ae_abs_bound (zero_lt_one.trans E.one_lt) _ hS hSfin (hε n)
    filter_upwards [hfu n] with x hx
    rw [hx]
    exact hBound n x
  have hLpNorm : Tendsto (fun n ↦ ‖(f n : RealLp m p)‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ ↦ norm_nonneg _) hLpBound (by simpa only [zero_mul] using hlim.mul_const D)
  have hE := E.tendsto_root_zero_of_midpoint_control f hLpNorm hmid
  exact squeeze_zero (fun _ ↦ apply_nonneg _ _) (fun n ↦ E.graphSeminorm_le_add (f n))
    (by simpa only [zero_add] using hE.add hLpNorm)

end WalkDimensions.PEnergy
