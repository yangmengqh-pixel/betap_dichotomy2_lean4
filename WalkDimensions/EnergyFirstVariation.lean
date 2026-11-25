import WalkDimensions.ClarksonComplements
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.LocallyConvex.HahnBanach
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The linear first variation of p-energy

The symmetric Clarkson bound provides a differentiable upper envelope.
A seminorming functional provides a lower envelope with the same first
variation.
-/

open Asymptotics Filter MeasureTheory Set
open scoped Topology

namespace WalkDimensions

section Seminorm

variable {Y : Type*} [AddCommGroup Y] [Module ℝ Y]

private theorem exists_seminorm_norming (S : Seminorm ℝ Y) (x : Y) :
    ∃ L : Y →ₗ[ℝ] ℝ, L x = S x ∧ ∀ z, |L z| ≤ S z := by
  by_cases hS : S x = 0
  · exact ⟨0, by simp [hS], fun z ↦ by simpa only [LinearMap.zero_apply, abs_zero] using apply_nonneg S z⟩
  have hx : x ≠ 0 := fun hx ↦ hS (hx.symm ▸ map_zero S)
  let V := Submodule.span ℝ ({x} : Set Y)
  let e : ℝ ≃ₗ[ℝ] V := LinearEquiv.toSpanNonzeroSingleton ℝ Y x hx
  let ℓ : V →ₗ[ℝ] ℝ := S x • e.symm.toLinearMap
  have he (z : V) : e.symm z • x = (z : Y) :=
    LinearEquiv.toSpanNonzeroSingleton_symm_apply_smul ℝ Y x hx z
  have hb (z : V) : ℓ z ≤ S z := by
    calc
      ℓ z = S x * e.symm z := rfl
      _ ≤ S x * |e.symm z| := mul_le_mul_of_nonneg_left (le_abs_self _) (apply_nonneg S _)
      _ = S (e.symm z • x) := by rw [map_smul_eq_mul, Real.norm_eq_abs, mul_comm]
      _ = S z := by rw [he z]
  obtain ⟨L, hL, hnorm⟩ := Module.Dual.exists_extension_of_le_seminorm_real V ℓ hb
  refine ⟨L, ?_, hnorm⟩
  have ht := hL (e 1)
  change L (e 1 : V) = S x * e.symm (e 1) at ht
  rw [e.symm_apply_apply, mul_one] at ht
  change L ((1 : ℝ) • x) = S x at ht
  simpa only [one_smul] using ht

private theorem two_mul_abs_rpow_le_symm {p : ℝ} (hp : 1 < p) (r s : ℝ) :
    2 * |r| ^ p ≤ |r + s| ^ p + |r - s| ^ p := by
  have ht := abs_add_le (r + s) (r - s)
  rw [show r + s + (r - s) = 2 * r by ring, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at ht
  have hr : |r| ≤ (1 / 2 : ℝ) * |r + s| + (1 / 2 : ℝ) * |r - s| := by linarith only [ht]
  have hpow := Real.rpow_le_rpow (abs_nonneg _) hr (zero_lt_one.trans hp).le
  have hcv := (convexOn_rpow hp.le).2 (mem_Ici.mpr (abs_nonneg (r + s)))
    (mem_Ici.mpr (abs_nonneg (r - s))) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  simp only [smul_eq_mul] at hcv
  have hh := hpow.trans hcv
  linarith only [hh]

theorem exists_symm_upper_envelope_of_bound {p : ℝ} (hp : 1 < p) (P : Y → ℝ)
    (hP : ∀ f, 0 ≤ P f) (hSmul : ∀ (t : ℝ) f, P (t • f) = |t| ^ p * P f)
    (hUpper₂ : p ≤ 2 → ∀ f g, P (f + g) + P (f - g) ≤ 2 * (P f + P g))
    (hUpper : 2 ≤ p → ∀ f g, P (f + g) + P (f - g) ≤
      2 * (P f ^ (p - 1)⁻¹ + P g ^ (p - 1)⁻¹) ^ (p - 1))
    (f : Y) {B : ℝ} (hB : 0 ≤ B) :
    ∃ M : ℝ → ℝ, HasDerivAt M 0 0 ∧ M 0 = 2 * P f ∧
      ∀ g : Y, P g ≤ B → ∀ t : ℝ, P (f + t • g) + P (f - t • g) ≤ M t := by
  let A : ℝ := P f
  have hA : 0 ≤ A := hP f
  have habs {q : ℝ} (hq : 1 < q) : HasDerivAt (fun t : ℝ ↦ |t| ^ q) 0 0 := by
    simpa only [mul_zero, zero_mul] using hasDerivAt_abs_rpow (0 : ℝ) hq
  have hzero {q : ℝ} (hq : 1 < q) : |(0 : ℝ)| ^ q = 0 := by
    simp only [abs_zero, Real.zero_rpow (zero_lt_one.trans hq).ne']
  have hlin : ∃ M : ℝ → ℝ, HasDerivAt M 0 0 ∧ M 0 = 2 * A ∧
      ∀ t, M t = 2 * (A + |t| ^ p * B) := by
    refine ⟨fun t ↦ 2 * (A + |t| ^ p * B), ?_, ?_, fun _ ↦ rfl⟩
    · simpa only [zero_mul, mul_zero] using
        (((habs hp).mul_const B).const_add A).const_mul 2
    · dsimp only
      rw [hzero hp, zero_mul, add_zero]
  by_cases h₂ : p ≤ 2
  · obtain ⟨M, hM, hM₀, hMe⟩ := hlin
    refine ⟨M, hM, hM₀, fun g hg t ↦ ?_⟩
    rw [hMe]
    have h := hUpper₂ h₂ f (t • g)
    rw [hSmul] at h
    exact h.trans (by gcongr)
  have h₂' : 2 ≤ p := le_of_lt (lt_of_not_ge h₂)
  let s := p - 1
  have hs : 0 < s := sub_pos.mpr hp
  have hPow (g : Y) (hg : P g ≤ B) (t : ℝ) :
      P (t • g) ^ s⁻¹ ≤ |t| ^ (p * s⁻¹) * B ^ s⁻¹ := by
    rw [hSmul, Real.mul_rpow (by positivity) (hP g), ← Real.rpow_mul (abs_nonneg _)]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (hP g) hg (inv_nonneg.mpr hs.le))
      (Real.rpow_nonneg (abs_nonneg _) _)
  rcases hA.eq_or_lt with hA₀ | hApos
  · obtain ⟨M, hM, hM₀, hMe⟩ := hlin
    refine ⟨M, hM, hM₀, fun g hg t ↦ ?_⟩
    have h := hUpper h₂' f (t • g)
    change _ ≤ 2 * (A ^ s⁻¹ + P (t • g) ^ s⁻¹) ^ s at h
    rw [hMe, ← hA₀, zero_add]
    rw [← hA₀, Real.zero_rpow (inv_ne_zero hs.ne'), zero_add,
      ← Real.rpow_mul (hP (t • g)), inv_mul_cancel₀ hs.ne', Real.rpow_one,
      hSmul] at h
    exact h.trans (by gcongr)
  · have hq : 1 < p * s⁻¹ := by
      rw [← div_eq_mul_inv, one_lt_div₀ hs]
      dsimp [s]
      linarith
    let F (t : ℝ) := A ^ s⁻¹ + |t| ^ (p * s⁻¹) * B ^ s⁻¹
    have hF₀ : F 0 = A ^ s⁻¹ := by dsimp [F]; rw [hzero hq, zero_mul, add_zero]
    have hF₀pos : 0 < F 0 := hF₀ ▸ Real.rpow_pos_of_pos hApos _
    have hF : HasDerivAt F 0 0 := by
      simpa only [F, zero_mul] using ((habs hq).mul_const (B ^ s⁻¹)).const_add (A ^ s⁻¹)
    refine ⟨fun t ↦ 2 * F t ^ s, ?_, ?_, fun g hg t ↦ ?_⟩
    · simpa only [mul_zero, zero_mul] using (hF.rpow_const (p := s) (Or.inl hF₀pos.ne')).const_mul 2
    · dsimp only
      rw [hF₀, ← Real.rpow_mul hA, inv_mul_cancel₀ hs.ne', Real.rpow_one]
    · have h := hUpper h₂' f (t • g)
      change _ ≤ 2 * (A ^ s⁻¹ + P (t • g) ^ s⁻¹) ^ s at h
      apply h.trans
      dsimp only [F]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow
        (add_nonneg (Real.rpow_nonneg hA _) (Real.rpow_nonneg (hP _) _))
        (add_le_add_right (hPow g hg t) _) hs.le) (by norm_num)

set_option maxHeartbeats 600000 in
theorem exists_seminorm_first_variation {p : ℝ} (hp : 1 < p) (S : Seminorm ℝ Y) (P : Y → ℝ)
    (hEq : ∀ f, P f = S f ^ p)
    (hUpper₂ : p ≤ 2 → ∀ f g, P (f + g) + P (f - g) ≤ 2 * (P f + P g))
    (hUpper : 2 ≤ p → ∀ f g, P (f + g) + P (f - g) ≤
      2 * (P f ^ (p - 1)⁻¹ + P g ^ (p - 1)⁻¹) ^ (p - 1))
    (f : Y) :
    ∃ L : Y →ₗ[ℝ] ℝ,
      (∀ g : Y, HasDerivAt (fun t : ℝ ↦ P (f + t • g)) (p * L g) 0) ∧
      ∀ g : Y, |L g| ≤ S f ^ (p - 1) * S g := by
  obtain ⟨L, hL, hdom⟩ := exists_seminorm_norming S f
  let r := S f
  let c := |r| ^ (p - 2) * r
  refine ⟨c • L, fun g ↦ ?_, fun g ↦ ?_⟩
  swap
  · have hr : 0 ≤ r := apply_nonneg _ _
    have hc : c = r ^ (p - 1) := by
      rcases hr.eq_or_lt with h | h
      · have he : r = 0 := h.symm
        simp only [c, he, mul_zero, Real.zero_rpow (sub_pos.mpr hp).ne']
      · dsimp only [c]
        rw [abs_of_pos h]
        calc
          _ = r ^ ((p - 2) + 1) := by rw [Real.rpow_add h, Real.rpow_one]
          _ = _ := by congr 1; ring
    rw [LinearMap.smul_apply, smul_eq_mul, hc, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg hr _)]
    exact mul_le_mul_of_nonneg_left (hdom g) (Real.rpow_nonneg hr _)

  let F (t : ℝ) := P (f + t • g)
  let G (t : ℝ) := |r + t * L g| ^ p
  have hr : 0 ≤ r := apply_nonneg _ _
  have hzero : F 0 = G 0 := by
    simp only [F, G, zero_smul, zero_mul, add_zero, abs_of_nonneg hr, hEq]
    rfl
  have hdom' (t : ℝ) : G t ≤ F t := by
    rw [show F t = S (f + t • g) ^ p from hEq _]
    apply Real.rpow_le_rpow (abs_nonneg _) _ (zero_lt_one.trans hp).le
    have h := hdom (f + t • g)
    rw [map_add, map_smul, smul_eq_mul, hL] at h
    exact h
  have hGsym (t : ℝ) : 2 * F 0 ≤ G t + G (-t) := by
    rw [hzero]
    simpa only [G, zero_mul, add_zero, neg_mul, ← sub_eq_add_neg] using
      two_mul_abs_rpow_le_symm hp r (t * L g)
  obtain ⟨M, hM, hM₀, hupper⟩ := exists_symm_upper_envelope_of_bound hp P
    (fun x ↦ hEq x ▸ Real.rpow_nonneg (apply_nonneg S x) _)
    (fun a x ↦ by rw [hEq, hEq, map_smul_eq_mul, Real.norm_eq_abs,
      Real.mul_rpow (abs_nonneg _) (apply_nonneg _ _)]) hUpper₂ hUpper f (hEq g ▸ Real.rpow_nonneg (apply_nonneg S g) _)
  have hDiffBound (t : ℝ) : F t - G t ≤ M t - M 0 := by
    have h : F t + F (-t) ≤ M t := by
      change P (f + t • g) + P (f + (-t) • g) ≤ M t
      have he : (-t) • g = -(t • g) := neg_smul t g
      rw [he, ← sub_eq_add_neg]
      exact hupper g le_rfl t
    rw [hM₀]
    have hF₀ : F 0 = P f := by simp [F]
    linarith only [h, hGsym t, hdom' (-t), hF₀]
  have ho : (fun t ↦ F t - G t) =o[𝓝 (0 : ℝ)] (fun t ↦ t) := by
    have h := hM.isLittleO
    simp only [smul_zero, sub_zero] at h
    apply isLittleO_iff.mpr
    intro ε hε
    filter_upwards [(isLittleO_iff.mp h) hε] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (hdom' t))]
    exact (hDiffBound t).trans ((le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using ht))
  have hg' : HasDerivAt G (p * (c • L) g) 0 := by
    have hlin : HasDerivAt (fun t : ℝ ↦ r + t * L g) (L g) 0 := by
      simpa only [id_eq, one_mul] using ((hasDerivAt_id (0 : ℝ)).mul_const (L g)).const_add r
    have h := (hasDerivAt_abs_rpow (r + (0 : ℝ) * L g) hp).comp 0 hlin
    change HasDerivAt G _ 0 at h
    simpa only [zero_mul, add_zero, LinearMap.smul_apply, smul_eq_mul, c, mul_assoc] using h
  apply hasDerivAt_iff_isLittleO.mpr
  have hgO := hg'.isLittleO
  simp only [sub_zero] at hgO ⊢
  have hs := ho.add hgO
  convert hs using 1
  funext t
  change F t - F 0 - t * (p * (c • L) g) =
    F t - G t + (G t - G 0 - t * (p * (c • L) g))
  rw [hzero]
  ring

end Seminorm

namespace PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {m : Measure X} [IsFiniteMeasureOnCompacts m] {p : ℝ} (E : PEnergy m p)

/-- The directional derivatives of energy at one base point are given by a
single linear functional, with the normalization of the paper. -/
theorem exists_linear_first_variation (f : E.domain) :
    ∃ L : E.domain →ₗ[ℝ] ℝ, ∀ g : E.domain,
      HasDerivAt (fun t : ℝ ↦ (E.energy (f + t • g) : ℝ)) (p * L g) 0 := by
  obtain ⟨L, hL, _⟩ := exists_seminorm_first_variation E.one_lt E.rootSeminorm
    (fun u ↦ (E.energy u : ℝ)) E.energy_eq_root_rpow
    E.energy_add_add_energy_sub_le_two_mul E.clarkson_two_le f
  exact ⟨L, hL⟩

end PEnergy

end WalkDimensions
