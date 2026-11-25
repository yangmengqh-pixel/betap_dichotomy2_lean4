import WalkDimensions.EnergyDerivativeLaws
import WalkDimensions.SignedMeasureWeights
import WalkDimensions.CoreRestriction
import WalkDimensions.CoreLatticeConvergence
import WalkDimensions.SawtoothCells

/-!
# The quadratic chain rule in the second argument

Subtracting the square of a small sawtooth makes the square affine on
each sawtooth cell. The error tends to zero in the energy seminorm.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy.CompactCore

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {p : ℝ} {E : PEnergy μ p}

noncomputable def mul (f g : E.CompactCore) : E.CompactCore := (f.exists_core_mul g).choose

theorem mul_apply (f g : E.CompactCore) (x : X) : (f.mul g).toFun x = f.toFun x * g.toFun x :=
  congrFun (f.exists_core_mul g).choose_spec x

private theorem root_saw_mul_saw_le (v : E.CompactCore) {r : ℝ} (hr : 0 < r) :
    E.rootSeminorm ((v.saw r).mul (v.saw r)).domainElement ≤
      (2 * r) * E.rootSeminorm v.domainElement := by
  let T := sawtooth r
  let φ (t : ℝ) := T t * T t / (2 * r)
  have hpos : 0 < 2 * r := by positivity
  have hφ : LipschitzWith 1 φ := by
    apply lipschitzWith_iff_dist_le_mul.mpr
    intro a b
    rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul]
    have h : |T a - T b| ≤ |a - b| := by
      simpa only [T, Real.dist_eq, NNReal.coe_one, one_mul] using
        (lipschitzWith_iff_dist_le_mul.mp (lipschitzWith_sawtooth r) a b)
    have hsum : 0 ≤ T a + T b := add_nonneg (sawtooth_nonneg _ _) (sawtooth_nonneg _ _)
    have hs : T a + T b ≤ 2 * r := by
      have hA : T a ≤ r := sawtooth_le hr _
      have hB : T b ≤ r := sawtooth_le hr _
      linarith only [hA, hB]
    change |T a * T a / (2 * r) - T b * T b / (2 * r)| ≤ _
    rw [← sub_div, abs_div, abs_of_pos hpos,
      show T a * T a - T b * T b = (T a - T b) * (T a + T b) by ring,
      abs_mul, abs_of_nonneg hsum]
    exact (div_le_iff₀ hpos).mpr (mul_le_mul h hs hsum (abs_nonneg _))
  have hφ₀ : φ 0 = 0 := by dsimp only [φ, T]; rw [sawtooth_zero, zero_mul, zero_div]
  let V := v.mapLipschitz φ hφ hφ₀
  have he : ((v.saw r).mul (v.saw r)).domainElement = (V.smul (2 * r)).domainElement := by
    apply domainElement_eq_of_toFun_eq
    funext x
    rw [mul_apply]
    change T (v.toFun x) * T (v.toFun x) = (2 * r) * φ (v.toFun x)
    dsimp only [φ]
    field_simp
  rw [he]
  change E.rootSeminorm ((2 * r) • V.domainElement) ≤ _
  rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos hpos]
  exact mul_le_mul_of_nonneg_left (v.root_mapLipschitz_le φ hφ hφ₀) hpos.le

private theorem derivative_of_affine_on (u v w : E.CompactCore)
    {A : Set X} (hA : MeasurableSet A) {a b : ℝ}
    (h : EqOn w.toFun (fun x ↦ a * v.toFun x + b) A) :
    E.energyDerivativeMeasure u.domainElement w.domainElement A =
      a * E.energyDerivativeMeasure u.domainElement v.domainElement A := by
  have hEq : EqOn (fun x ↦ w.toFun x - (v.smul a).toFun x) (fun _ ↦ b) A := by
    intro x hx
    change w.toFun x - a * v.toFun x = b
    rw [h hx]
    ring
  rw [E.energyDerivativeMeasure_eq_of_eqOn_sub_const u w (v.smul a) hA hEq]
  simp only [E.energyDerivativeMeasure_apply _ _ hA]
  change E.energyVariation u.domainElement A hA (a • v.domainElement) =
    a * E.energyVariation u.domainElement A hA v.domainElement
  rw [map_smul, smul_eq_mul]

theorem energyDerivativeMeasure_square (u v : E.CompactCore) :
    E.energyDerivativeMeasure u.domainElement (v.mul v).domainElement =
      weightSignedMeasure (E.energyDerivativeMeasure u.domainElement v.domainElement)
        (fun x ↦ 2 * v.toFun x) := by
  let ν := E.energyDerivativeMeasure u.domainElement v.domainElement
  let Z (x : X) := 2 * v.toFun x
  have hZ : Continuous Z := continuous_const.mul v.continuous
  have hZc : HasCompactSupport Z := v.compactSupport.comp_left (mul_zero (2 : ℝ))
  obtain ⟨L, hL⟩ := hZ.bounded_above_of_compact_support hZc
  have hIZ : ν.Integrable Z := integrable_vectorMeasure_of_bounded ν hZ.measurable
    (fun x ↦ by simpa only [Real.norm_eq_abs] using hL x)
  ext A hA
  let W := weightSignedMeasure ν Z
  change E.energyDerivativeMeasure u.domainElement (v.mul v).domainElement A = W A
  have hApprox (r : ℝ) (hr : 0 < r) :
      |E.energyDerivativeMeasure u.domainElement (v.mul v).domainElement A - W A| ≤
        (2 * r) * ((ν.totalVariation A).toReal +
          (E.energyMeasureRoot A hA u.domainElement) ^ (p - 1) * E.rootSeminorm v.domainElement) := by
    let s := (v.saw r).mul (v.saw r)
    let w := (v.mul v).sub s
    let η := E.energyDerivativeMeasure u.domainElement w.domainElement
    let I := ℤ × Bool
    let i (n : ℕ) : I := (Encodable.decode n).getD (0, false)
    have hi : Surjective i := fun j ↦ ⟨Encodable.encode j, by simp only [i, Encodable.encodek, Option.getD_some]⟩
    let B (n : ℕ) := v.toFun ⁻¹' sawtoothCell r (i n)
    have hB (n : ℕ) : MeasurableSet (B n) :=
      (isClosed_sawtoothCell r (i n)).measurableSet.preimage v.continuous.measurable
    have hCover : (⋃ n, B n) = univ := by
      apply eq_univ_of_forall
      intro x
      obtain ⟨j, hj⟩ := exists_mem_sawtoothCell hr (v.toFun x)
      obtain ⟨n, hn⟩ := hi j
      exact mem_iUnion.mpr ⟨n, by change v.toFun x ∈ sawtoothCell r (i n); rwa [hn]⟩
    have hLocal (n : ℕ) (Q : Set X) (hQ : MeasurableSet Q) (hQB : Q ⊆ B n) :
        |η Q - W Q| ≤ (2 * r) * (ν.totalVariation Q).toReal := by
      let σ := sawtoothSign (i n)
      let b := r * (sawtoothOffsetIndex (i n) : ℝ)
      let a := -(2 * σ * b)
      have hσ : σ = 1 ∨ σ = -1 := sawtoothSign_eq _
      have hσ₂ : σ * σ = 1 := by rcases hσ with he | he <;> rw [he] <;> norm_num
      have hσa : |σ| = 1 := by rcases hσ with he | he <;> simp [he]
      have hSaw (x : X) (hx : x ∈ Q) :
          sawtooth r (v.toFun x) = σ * v.toFun x + b :=
        sawtooth_eq_affine_of_mem_cell hr (hQB hx)
      have hw : EqOn w.toFun (fun x ↦ a * v.toFun x - b * b) Q := by
        intro x hx
        change (v.mul v).toFun x - s.toFun x = _
        rw [mul_apply, show s.toFun x = _ from (v.saw r).mul_apply (v.saw r) x]
        change v.toFun x * v.toFun x - sawtooth r (v.toFun x) * sawtooth r (v.toFun x) = _
        rw [hSaw x hx]
        dsimp only [a]
        linear_combination - (v.toFun x) ^ 2 * hσ₂
      have hEta : η Q = a * ν Q := derivative_of_affine_on u v w hQ hw
      have hConst : ν.Integrable (fun _ : X ↦ a) :=
        integrable_vectorMeasure_of_bounded ν measurable_const (fun _ ↦ le_rfl)
      have hW : weightSignedMeasure ν ((fun _ : X ↦ a) - Z) Q = a * ν Q - W Q := by
        rw [weightSignedMeasure_sub ν hConst hIZ, sub_apply, weightSignedMeasure_apply_const ν a hQ]
      rw [hEta, ← hW]
      apply abs_weightSignedMeasure_apply_le ν (hConst.sub hIZ) hQ
      intro x hx
      change |a - 2 * v.toFun x| ≤ 2 * r
      have he : a - 2 * v.toFun x = -2 * σ * sawtooth r (v.toFun x) := by
        rw [hSaw x hx]
        dsimp only [a]
        linear_combination 2 * v.toFun x * hσ₂
      rw [he, abs_mul, abs_mul, hσa, mul_one, abs_neg, abs_of_nonneg (by norm_num),
        abs_of_nonneg (sawtooth_nonneg _ _)]
      exact mul_le_mul_of_nonneg_left (sawtooth_le hr _) (by norm_num)
    have hE := abs_signedMeasure_sub_apply_le_of_cover η W ν.totalVariation hB hCover
      (mul_nonneg (by norm_num) hr.le) hLocal hA
    have hd : E.energyDerivativeMeasure u.domainElement (v.mul v).domainElement A - η A =
        E.energyDerivativeMeasure u.domainElement s.domainElement A := by
      simp only [E.energyDerivativeMeasure_apply _ _ hA, η]
      have hDom : w.domainElement = (v.mul v).domainElement - s.domainElement := by
        change (v.mul v).domainElement + -s.domainElement = _
        rw [sub_eq_add_neg]
      rw [hDom, map_sub, sub_sub_cancel]
    have hL' : |E.energyDerivativeMeasure u.domainElement s.domainElement A| ≤
        (E.energyMeasureRoot A hA u.domainElement) ^ (p - 1) *
          ((2 * r) * E.rootSeminorm v.domainElement) := by
      rw [E.energyDerivativeMeasure_apply _ _ hA]
      apply (E.abs_energyVariation_le _ _ hA).trans
      exact mul_le_mul_of_nonneg_left ((E.energyMeasureRoot_le A hA s.domainElement).trans
        (root_saw_mul_saw_le v hr)) (Real.rpow_nonneg (apply_nonneg _ _) _)
    calc
      _ ≤ |E.energyDerivativeMeasure u.domainElement (v.mul v).domainElement A - η A| +
          |η A - W A| := abs_sub_le _ _ _
      _ ≤ _ := by rw [hd]; exact (add_le_add hL' hE).trans_eq (by ring)
  let C := (ν.totalVariation A).toReal +
    (E.energyMeasureRoot A hA u.domainElement) ^ (p - 1) * E.rootSeminorm v.domainElement
  have hLim : Tendsto (fun r : ℝ ↦ (2 * r) * C) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [id_eq, mul_zero, zero_mul] using
      (((tendsto_id : Tendsto id (𝓝 (0 : ℝ)) (𝓝 0)).const_mul (2 : ℝ)).mul_const C).mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hzero := ge_of_tendsto hLim (eventually_mem_nhdsWithin.mono fun r hr ↦ hApprox r hr)
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hzero (abs_nonneg _)))

end WalkDimensions.PEnergy.CompactCore
