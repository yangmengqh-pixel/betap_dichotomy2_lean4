import WalkDimensions.CompactCore
import WalkDimensions.CoreCutoffs
import WalkDimensions.EnergyLocality
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Representing compact sets by exact energy sublevels

A positive sum of cutoffs supported in shrinking neighbourhoods equals
its maximum precisely on the compact set.
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {p : ℝ} (E : PEnergy μ p)

theorem exists_compactCore_sublevel_eq {K V : Set X}
    (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V) :
    ∃ g : E.CompactCore, {x | g.toFun x ≤ -1} = K ∧ tsupport g.toFun ⊆ V := by
  by_cases hne : K.Nonempty
  swap
  · have h := Set.not_nonempty_iff_eq_empty.mp hne
    refine ⟨⟨0, 0, Lp.coeFn_zero ℝ (ENNReal.ofReal p) μ, continuous_const, HasCompactSupport.zero⟩, ?_, ?_⟩
    · rw [h]
      exact eq_empty_iff_forall_notMem.mpr (fun _ h' ↦ (by norm_num : ¬ (0 : ℝ) ≤ -1) h')
    · simp
  obtain ⟨U, hU, hKU, hUV, hUcomp⟩ := exists_open_between_and_isCompact_closure hK hV hKV
  let S := closure U
  let Uₙ (n : ℕ) := U ∩ {x | infDist x K < oscillationWidth n}
  have hUₙ (n : ℕ) : IsOpen (Uₙ n) := hU.inter (isOpen_lt (continuous_infDist_pt K) continuous_const)
  have hKₙ (n : ℕ) : K ⊆ Uₙ n := fun _ hx ↦
    ⟨hKU hx, (infDist_zero_of_mem hx).trans_lt (oscillationWidth_pos n)⟩
  choose f u hcont hcompact hae hrange hval hs using
    fun n ↦ E.exists_core_cutoff_of_isCompact_subset_isOpen hK (hUₙ n) (hKₙ n)
  let c (n : ℕ) := oscillationWidth n / (1 + E.rootSeminorm (f n))
  have hden (n : ℕ) : 0 < 1 + E.rootSeminorm (f n) := by
    linarith only [apply_nonneg E.rootSeminorm (f n)]
  have hc (n : ℕ) : 0 < c n := div_pos (oscillationWidth_pos n) (hden n)
  have hc' (n : ℕ) : c n ≤ oscillationWidth n := by
    exact div_le_self (oscillationWidth_pos n).le (le_add_of_nonneg_right (apply_nonneg _ _))
  have hsum : Summable oscillationWidth := by
    exact summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hsumc : Summable c := Summable.of_nonneg_of_le (fun n ↦ (hc n).le) hc' hsum
  let t (n : ℕ) (x : X) := c n * u n x
  have ht₀ (n : ℕ) (x : X) : 0 ≤ t n x := mul_nonneg (hc n).le (hrange n x).1
  have ht₁ (n : ℕ) (x : X) : t n x ≤ c n := by
    exact (mul_le_mul_of_nonneg_left (hrange n x).2 (hc n).le).trans_eq (mul_one _)
  have hbound (n : ℕ) (x : X) : ‖t n x‖ ≤ oscillationWidth n := by
    rw [Real.norm_eq_abs, abs_of_nonneg (ht₀ n x)]
    exact (ht₁ n x).trans (hc' n)
  let C := ∑' n, c n
  let G (x : X) := ∑' n, t n x
  have hC : 0 < C := hsumc.tsum_pos (fun n ↦ (hc n).le) 0 (hc 0)
  have ht (x : X) : Summable (fun n ↦ t n x) :=
    Summable.of_nonneg_of_le (fun n ↦ ht₀ n x) (fun n ↦ ht₁ n x) hsumc
  have hG : Continuous G :=
    continuous_tsum (fun n ↦ continuous_const.mul (hcont n)) hsum hbound
  have hout (n : ℕ) (x : X) (hx : x ∉ Uₙ n) : u n x = 0 :=
    notMem_support.mp fun hy ↦ hx (hs n (subset_closure hy))
  have hGout (x : X) (hx : x ∉ S) : G x = 0 := by
    have he : (fun n ↦ t n x) = 0 := funext fun n ↦ by
      change c n * u n x = 0
      rw [hout n x (fun hx' ↦ hx (subset_closure hx'.1)), mul_zero]
    change ∑' n, t n x = 0
    rw [he]
    exact tsum_zero
  have hGcomp : HasCompactSupport G := by
    apply hUcomp.of_isClosed_subset isClosed_closure (closure_minimal ?_ isClosed_closure)
    exact fun x hx ↦ not_not.mp (fun hx' ↦ hx (hGout x hx'))
  have hGK (x : X) : C ≤ G x ↔ x ∈ K := by
    constructor
    · intro hx
      by_contra hxK
      have hdist : 0 < infDist x K := (hK.isClosed.notMem_iff_infDist_pos hne).mp hxK
      obtain ⟨n, hn⟩ := (tendsto_oscillationWidth.eventually_lt_const hdist).exists
      have hn' := hout n x (fun h ↦ hn.not_ge h.2.le)
      have hlt : t n x < c n := by dsimp [t]; rw [hn', mul_zero]; exact hc n
      exact hx.not_gt ((ht x).tsum_lt_tsum (fun i ↦ ht₁ i x) hlt hsumc)
    · intro hx
      have he : (fun n ↦ t n x) = c := funext fun n ↦ by
        dsimp [t]
        rw [hval n hx, mul_one]
      change C ≤ ∑' n, t n x
      rw [he]
  have hGLp : (continuousLp p G hG hGcomp : RealLp μ p) =ᵐ[μ] G :=
    MemLp.coeFn_toLp (hG.memLp_of_hasCompactSupport hGcomp)
  obtain ⟨F, hF, _⟩ := E.exists_of_uniform_approximation (continuousLp p G hG hGcomp) G
    hGLp isClosed_closure.measurableSet (hUcomp.measure_lt_top (μ := μ)).ne
    (M := ∑' n, oscillationWidth n) (by
      intro ε hε
      have huni := tendstoUniformly_tsum hsum hbound
      obtain ⟨A, hA⟩ := ((Metric.tendstoUniformly_iff.mp huni) ε hε).exists
      let w : E.domain := ∑ n ∈ A, c n • f n
      refine ⟨w, fun x ↦ ∑ n ∈ A, t n x, ?_, ?_, ?_⟩
      · apply E.coeFn_finsetSum A
        intro n hn
        filter_upwards [Lp.coeFn_smul (c n) (f n : RealLp μ p), hae n] with x hx hy
        change (c n • (f n : RealLp μ p)) x = _
        rw [hx, Pi.smul_apply, smul_eq_mul, hy]
      · intro x
        by_cases hx : x ∈ S
        · rw [indicator_of_mem hx]
          have hd := hA x
          rw [dist_comm, Real.dist_eq] at hd
          exact hd.le
        · rw [indicator_of_notMem hx, hGout x hx]
          simp only [t, hout _ _ (fun hx' ↦ hx (subset_closure hx'.1)), mul_zero,
            Finset.sum_const_zero, sub_zero, abs_zero, le_refl]
      · have hterm (n : ℕ) : E.rootSeminorm (c n • f n) ≤ oscillationWidth n := by
          rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg (hc n).le]
          dsimp [c]
          rw [div_mul_eq_mul_div, div_le_iff₀ (hden n)]
          nlinarith only [(oscillationWidth_pos n).le]
        have hfin (J : Finset ℕ) : E.rootSeminorm (∑ n ∈ J, c n • f n) ≤
            ∑ n ∈ J, oscillationWidth n := by
          induction J using Finset.induction_on with
          | empty => simp only [Finset.sum_empty, map_zero, le_refl]
          | insert n J hn ih =>
              rw [Finset.sum_insert hn, Finset.sum_insert hn]
              exact (E.rootSeminorm.add_le' _ _).trans (add_le_add (hterm n) ih)
        exact (hfin A).trans (hsum.sum_le_tsum A (fun n _ ↦ (oscillationWidth_pos n).le)))
  let d := -C⁻¹
  have hd : d < 0 := neg_neg_of_pos (inv_pos.mpr hC)
  have hFRep : (F : RealLp μ p) =ᵐ[μ] G := hF ▸ hGLp
  let g : E.CompactCore :=
    { domainElement := d • F
      toFun := fun x ↦ d * G x
      ae_eq := by
        filter_upwards [Lp.coeFn_smul d (F : RealLp μ p), hFRep] with x hx hy
        change (d • (F : RealLp μ p)) x = _
        rw [hx, Pi.smul_apply, smul_eq_mul, hy]
      continuous := continuous_const.mul hG
      compactSupport := hGcomp.comp_left (g := fun x ↦ d * x) (mul_zero _) }
  refine ⟨g, ?_, ?_⟩
  · ext x
    change d * G x ≤ -1 ↔ x ∈ K
    have he : d * C = -1 := by dsimp [d]; rw [neg_mul, inv_mul_cancel₀ hC.ne']
    rw [← hGK x, ← he]
    exact mul_le_mul_left_of_neg hd
  · apply Subset.trans _ hUV
    apply closure_minimal _ isClosed_closure
    intro x hx
    by_contra hx'
    exact hx (show d * G x = 0 by rw [hGout x hx', mul_zero])

end WalkDimensions.PEnergy
