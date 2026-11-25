import WalkDimensions.DiscreteConvolution
import WalkDimensions.Morrey

/-!
# Continuous discrete convolutions

In the positive Morrey range each weight has a continuous representative.
The pointwise bounds on the measurable weights pass to these
representatives on closed or open sets as appropriate.
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SecondCountableTopology X] {m : Measure X}
  [IsFiniteMeasureOnCompacts m] [m.IsOpenPosMeasure] {p : ℝ} (E : PEnergy m p)

theorem exists_continuous_discrete_convolution {d β : ℝ}
    (hvol : AhlforsRegular m d) (hβ : d < β) {Γ : E.domain → Measure X}
    (hPI : E.Poincare Γ β) (hΓ : ∀ f, Γ f univ = (E.energy f : ℝ≥0∞))
    (hcap : E.CapacityUpperBound β) :
    ∃ C A : ℝ, 0 < C ∧ 1 < A ∧ ∀ {u : X → ℝ}, Continuous u → HasCompactSupport u →
      ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ r ∈ Ioo (0 : ℝ) δ, ∃ (t : Finset X) (g : X → E.domain) (w : X → X → ℝ) (U : Set X),
        (↑t : Set X).Pairwise (fun y z ↦ r ≤ dist y z) ∧
        (∀ z, (g z : RealLp m p) =ᵐ[m] w z) ∧
        (∀ z, Continuous (w z) ∧ tsupport (w z) ⊆ closedBall z (A * r)) ∧
        IsOpen U ∧ EqOn (fun x ↦ ∑ z ∈ t, w z x) (fun _ ↦ 1) U ∧
        (∀ z, E.rootSeminorm (g z) ≤ C * (r ^ (-β) * m.real (ball z r)) ^ p⁻¹) ∧
        let v := fun x ↦ ∑ z ∈ t, (⨍ y in ball z r, u y ∂m) * w z x
        ((∑ z ∈ t, (⨍ y in ball z r, u y ∂m) • g z : E.domain) : RealLp m p) =ᵐ[m] v ∧
        Continuous v ∧ (∀ x, |v x - u x| ≤ ε) ∧
        tsupport v ⊆ cthickening 1 (tsupport u) ∧ tsupport v ⊆ U := by
  obtain ⟨_, _, hrep⟩ := E.exists_holder_representative hvol hβ hPI hΓ
  obtain ⟨C, A, hC, hA, hconv⟩ := E.exists_discrete_convolution hvol.volumeDoubling hcap
  refine ⟨C, A, hC, hA, fun {u} hu hc ε hε ↦ ?_⟩
  obtain ⟨δ, hδ, _, hδconv⟩ := hconv hu hc ε hε
  have hA' : 0 < A + 1 := by linarith
  let η := min δ (1 / (A + 1))
  have hη : 0 < η := lt_min hδ (one_div_pos.mpr hA')
  refine ⟨η, hη, fun r hr ↦ ?_⟩
  have hrδ : r ∈ Ioo (0 : ℝ) δ := ⟨hr.1, hr.2.trans_le (min_le_left _ _)⟩
  obtain ⟨t, g, a, _, hsep, hga, ha, _, hUnity, henergy, hgaSum, haErr, haSupp⟩ :=
    hδconv r hrδ
  choose w hw hgw _ using fun z ↦ hrep (g z)
  have hwA (z : X) : w z =ᵐ[m] a z := (hgw z).symm.trans (hga z)
  have hW (z : X) : tsupport (w z) ⊆ closedBall z (A * r) := by
    have heq : EqOn (w z) (fun _ ↦ 0) (closedBall z (A * r))ᶜ := by
      apply Measure.eqOn_open_of_ae_eq (μ := m) _ isClosed_closedBall.isOpen_compl
        (hw z).continuousOn continuousOn_const
      filter_upwards [ae_restrict_of_ae (s := (closedBall z (A * r))ᶜ) (hwA z),
        ae_restrict_mem isClosed_closedBall.measurableSet.compl] with x hx hxball
      exact hx.trans ((ha z).2.2 (fun h ↦ hxball (ball_subset_closedBall h)))
    apply closure_minimal _ isClosed_closedBall
    intro x hx
    by_contra hxball
    exact hx (heq hxball)
  let U := interior (cthickening 1 (tsupport u))
  have hU : IsOpen U := isOpen_interior
  have hSumAE : (fun x ↦ ∑ z ∈ t, w z x) =ᵐ[m] fun x ↦ ∑ z ∈ t, a z x :=
    ((eventually_all_finset t).mpr (fun z _ ↦ hwA z)).mono
      (fun x hx ↦ Finset.sum_congr rfl fun z hz ↦ hx z hz)
  have hUnity' : EqOn (fun x ↦ ∑ z ∈ t, w z x) (fun _ ↦ 1) U := by
    have hsum : Continuous (fun x ↦ ∑ z ∈ t, w z x) := continuous_finsetSum t (fun z _ ↦ hw z)
    apply Measure.eqOn_open_of_ae_eq (μ := m) _ hU hsum.continuousOn continuousOn_const
    filter_upwards [ae_restrict_of_ae (s := U) hSumAE, ae_restrict_mem hU.measurableSet] with x hx hxU
    exact hx.trans (hUnity (interior_subset hxU))
  let b (z : X) := ⨍ y in ball z r, u y ∂m
  let v (x : X) := ∑ z ∈ t, b z * w z x
  let va (x : X) := ∑ z ∈ t, b z * a z x
  have hv : Continuous v := continuous_finsetSum t (fun z _ ↦ continuous_const.mul (hw z))
  have hEq : v =ᵐ[m] va := ((eventually_all_finset t).mpr (fun z _ ↦ hwA z)).mono
    (fun x hx ↦ Finset.sum_congr rfl fun z hz ↦ congrArg (b z * ·) (hx z hz))
  have hsmall : (A + 1) * r < 1 := by
    have ht := (lt_div_iff₀ hA').mp (hr.2.trans_le (min_le_right _ _))
    rwa [mul_comm]
  have hext : tsupport v ⊆ cthickening ((A + 1) * r) (tsupport u) := by
    have hclosed : IsClosed (cthickening ((A + 1) * r) (tsupport u)) := isClosed_cthickening
    have hev : EqOn v (fun _ ↦ 0) (cthickening ((A + 1) * r) (tsupport u))ᶜ := by
      apply Measure.eqOn_open_of_ae_eq (μ := m) _ hclosed.isOpen_compl hv.continuousOn continuousOn_const
      filter_upwards [ae_restrict_of_ae hEq, ae_restrict_mem hclosed.measurableSet.compl] with x hx hxs
      exact hx.trans (notMem_support.mp fun h ↦ hxs (haSupp (subset_closure h)))
    apply closure_minimal _ hclosed
    intro x hx
    by_contra hxs
    exact hx (hev hxs)
  have hVsmall : cthickening ((A + 1) * r) (tsupport u) ⊆ U :=
    (cthickening_subset_thickening' zero_lt_one hsmall _).trans
      (interior_maximal (thickening_subset_cthickening _ _) isOpen_thickening)
  refine ⟨t, g, w, U, hsep, hgw, fun z ↦ ⟨hw z, hW z⟩, hU, hUnity', henergy,
    hgaSum.trans hEq.symm, hv, ?_, ?_, ?_⟩
  · intro x
    have hclosed : IsClosed {x | |v x - u x| ≤ ε} :=
      isClosed_le (continuous_abs.comp (hv.sub hu)) continuous_const
    have hae : {x | |v x - u x| ≤ ε} =ᵐ[m] (univ : Set X) := by
      filter_upwards [hEq] with y hy
      simpa only [mem_ofPred_eq, mem_univ, iff_true, hy] using haErr y
    exact (show x ∈ {y | |v y - u y| ≤ ε} from hclosed.ae_eq_univ_iff_eq.1 hae ▸ mem_univ x)
  · exact hext.trans (cthickening_mono hsmall.le _)
  · exact hext.trans hVsmall

end WalkDimensions.PEnergy
