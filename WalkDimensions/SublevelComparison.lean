import WalkDimensions.EnergyStrip

/-!
# Comparison of energy sublevels

Inclusion of sublevel sets on the support of the energy test suffices to
compare their limiting energies. Compactness provides a strict buffer.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy.CompactCore

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {p : ℝ} {E : PEnergy μ p}

theorem sublevelEnergyRoot_le_of_buffer (f g h : E.CompactCore) {a a' b : ℝ}
    (ha : a < a')
    (hsub : ∀ x ∈ tsupport f.toFun, g.toFun x ≤ a' → h.toFun x ≤ b) :
    f.sublevelEnergyRoot g a ≤ f.sublevelEnergyRoot h b := by
  let ε := oscillationWidth
  obtain ⟨r, hr, hlim⟩ := E.exists_ramp_graph_tendsto_zero g.domainElement g.ae_eq g.compactSupport
    a ε (fun n ↦ (oscillationWidth_pos n).le) oscillationWidth_antitone tendsto_oscillationWidth
  have hR : Tendsto (fun n ↦ E.rootSeminorm (r n)) atTop (𝓝 0) :=
    squeeze_zero (fun _ ↦ apply_nonneg _ _) (fun n ↦ E.rootSeminorm_le_graphSeminorm (r n)) hlim
  have htend : Tendsto
      (fun n ↦ E.rootSeminorm (f.oscillation h b n) + E.rootSeminorm (r n))
      atTop (𝓝 (f.sublevelEnergyRoot h b)) := by
    simpa only [add_zero] using (f.tendsto_sublevelEnergyRoot h b).add hR
  apply le_of_tendsto_of_tendsto (f.tendsto_sublevelEnergyRoot g a) htend
  filter_upwards [tendsto_oscillationWidth.eventually_lt_const (sub_pos.mpr ha)] with n hn
  obtain ⟨w, hw, hW⟩ := E.exists_min_add_const (f.oscillation h b n) (r n)
    (f.oscillation_ae h b n) (hr n) (sublevelRamp_nonneg (ε n) a 0)
  have he : w = f.oscillation g a n := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [hw, f.oscillation_ae g a n] with x hx hy
    rw [hx, hy]
    change min (min (sawtooth (ε n) (f.toFun x)) (sublevelRamp (ε n) b (h.toFun x)))
      (offsetRamp (ε n) a (g.toFun x) + sublevelRamp (ε n) a 0) =
        min (sawtooth (ε n) (f.toFun x)) (sublevelRamp (ε n) a (g.toFun x))
    rw [offsetRamp, sub_add_cancel]
    by_cases hxS : x ∈ tsupport f.toFun
    · by_cases hfar : a + ε n ≤ g.toFun x
      · simp only [sublevelRamp_eq_zero hfar, min_eq_right (sawtooth_nonneg _ _),
          min_eq_right (le_min (sawtooth_nonneg _ _) (sublevelRamp_nonneg _ _ _))]
      · have hnear : g.toFun x ≤ a' := by linarith only [lt_of_not_ge hfar, hn]
        rw [sublevelRamp_eq_cap (oscillationWidth_pos n).le (hsub x hxS hnear),
          min_eq_left (sawtooth_le (oscillationWidth_pos n) _)]
    · rw [notMem_support.mp (fun hy' ↦ hxS (subset_closure hy')), sawtooth_zero,
        min_eq_left (sublevelRamp_nonneg _ _ _), min_eq_left (sublevelRamp_nonneg _ _ _)]
  simpa only [he] using hW

omit [MeasurableSpace X] [BorelSpace X] in
private theorem exists_sublevel_buffer {K : Set X} (hK : IsCompact K)
    {u v : X → ℝ} (hu : Continuous u) (hv : Continuous v) {a b c : ℝ}
    (hbc : b < c) (hsub : ∀ x ∈ K, u x ≤ a → v x ≤ b) :
    ∃ a' > a, ∀ x ∈ K, u x ≤ a' → v x ≤ c := by
  let C := K ∩ {x | c ≤ v x}
  have hclosed : IsClosed {x | c ≤ v x} := isClosed_le continuous_const hv
  have hC : IsCompact C := hK.inter_right hclosed
  by_cases hne : C.Nonempty
  · obtain ⟨y, hy, hmin⟩ := hC.exists_isMinOn hne hu.continuousOn
    have hy' : a < u y := lt_of_not_ge fun h ↦ hbc.not_ge (hy.2.trans (hsub y hy.1 h))
    obtain ⟨a', ha, hay⟩ := exists_between hy'
    refine ⟨a', ha, fun x hx hxa ↦ ?_⟩
    by_contra! h
    exact hay.not_ge ((hmin (show x ∈ C from ⟨hx, h.le⟩)).trans hxa)
  · refine ⟨a + 1, by linarith, fun x hx _ ↦ ?_⟩
    by_contra! h
    exact hne ⟨x, hx, h.le⟩

theorem sublevelEnergyRoot_le_of_sublevel_subset (f g h : E.CompactCore) {a b : ℝ}
    (hsub : ∀ x ∈ tsupport f.toFun, g.toFun x ≤ a → h.toFun x ≤ b) :
    f.sublevelEnergyRoot g a ≤ f.sublevelEnergyRoot h b := by
  apply ge_of_tendsto ((f.tendsto_sublevelEnergyRoot_right h b).mono_left
    (nhdsWithin_mono _ (Ioi_subset_Ici_self : Ioi b ⊆ Ici b)))
  filter_upwards [self_mem_nhdsWithin (s := Ioi b)] with c hc
  obtain ⟨a', ha', he⟩ := exists_sublevel_buffer f.compactSupport.isCompact
    g.continuous h.continuous hc hsub
  exact f.sublevelEnergyRoot_le_of_buffer g h ha' he

theorem sublevelDistribution_le_of_sublevel_subset (f g h : E.CompactCore) {a b : ℝ}
    (hsub : ∀ x ∈ tsupport f.toFun, g.toFun x ≤ a → h.toFun x ≤ b) :
    f.sublevelDistribution g a ≤ f.sublevelDistribution h b :=
  Real.rpow_le_rpow (f.sublevelEnergyRoot_nonneg g a)
    (f.sublevelEnergyRoot_le_of_sublevel_subset g h hsub) (zero_lt_one.trans E.one_lt).le

private theorem sublevelEnergyRoot_le_buffered_union (f g h k : E.CompactCore) {a a' b c ε : ℝ}
    (haa' : a < a') (hε : 0 < ε)
    (hsub : ∀ x ∈ tsupport f.toFun, g.toFun x ≤ a' → h.toFun x ≤ b ∨ k.toFun x ≤ c) :
    f.sublevelEnergyRoot g a ≤
      (f.sublevelDistribution h (b + ε) + f.sublevelDistribution k c) ^ p⁻¹ +
      f.sublevelEnergyRoot (h.bandTest (b + ε) (b + 2 * ε)) (bandThreshold (b + ε) (b + 2 * ε)) := by
  let l := b + ε
  let u := b + 2 * ε
  let r := oscillationWidth
  let A (n : ℕ) := f.oscillationCore h l n
  let K (n : ℕ) := f.oscillationCore k c n
  let R (n : ℕ) := h.neg.ramp (r n) (-u)
  let B (n : ℕ) := (K n).minAddConst (R n) (sublevelRamp_nonneg (r n) (-u) 0)
  let V (n : ℕ) := f.oscillationCore (h.bandTest l u) (bandThreshold l u) n
  let T (n : ℕ) := g.ramp (r n) a
  let W (n : ℕ) := (((A n).add (B n)).sup (V n)).minAddConst (T n) (sublevelRamp_nonneg (r n) a 0)
  have hBroot (n : ℕ) : E.rootSeminorm (B n).domainElement ≤
      E.rootSeminorm (K n).domainElement + E.rootSeminorm (R n).domainElement :=
    (K n).root_minAddConst_le (R n) _
  have hBval (n : ℕ) (x : X) :
      (B n).toFun x = min ((K n).toFun x) (sublevelRamp (r n) (-u) (-h.toFun x)) := by
    change min ((K n).toFun x) (offsetRamp (r n) (-u) (-h.toFun x) +
      sublevelRamp (r n) (-u) 0) = _
    rw [offsetRamp, sub_add_cancel]
  have hVval (n : ℕ) (x : X) :
      (V n).toFun x = min (sawtooth (r n) (f.toFun x))
        (min (sublevelRamp (r n) u (h.toFun x)) (sublevelRamp (r n) (-l) (-h.toFun x))) := by
    change min _ (sublevelRamp (r n) (bandThreshold l u) ((h.bandTest l u).toFun x)) = _
    rw [band_ramp_eq]
  let M (n : ℕ) := ((E.energy (A n).domainElement : ℝ) +
    (E.rootSeminorm (K n).domainElement + E.rootSeminorm (R n).domainElement) ^ p) ^ p⁻¹
  have hMlim : Tendsto M atTop
      (𝓝 ((f.sublevelDistribution h l + f.sublevelDistribution k c) ^ p⁻¹)) := by
    have hKlim : Tendsto (fun n ↦ (E.rootSeminorm (K n).domainElement +
          E.rootSeminorm (R n).domainElement) ^ p) atTop (𝓝 (f.sublevelDistribution k c)) := by
      have ht := (f.tendsto_sublevelEnergyRoot k c).add (h.neg.tendsto_root_ramp (-u))
      change Tendsto (fun n ↦ (E.rootSeminorm (f.oscillation k c n) +
          E.rootSeminorm (R n).domainElement) ^ p) atTop (𝓝 (f.sublevelEnergyRoot k c ^ p))
      simpa only [Function.comp_def, add_zero] using
        ((Real.continuous_rpow_const (zero_lt_one.trans E.one_lt).le).tendsto
          (f.sublevelEnergyRoot k c + 0)).comp ht
    have hsum := (f.tendsto_oscillation_energy h l).add hKlim
    exact ((Real.continuous_rpow_const (inv_nonneg.mpr (zero_lt_one.trans E.one_lt).le)).tendsto
      (f.sublevelDistribution h l + f.sublevelDistribution k c)).comp hsum
  have hVlim := f.tendsto_sublevelEnergyRoot (h.bandTest l u) (bandThreshold l u)
  have hlim : Tendsto (fun n ↦ M n + E.rootSeminorm (V n).domainElement +
      E.rootSeminorm (T n).domainElement) atTop
        (𝓝 ((f.sublevelDistribution h l + f.sublevelDistribution k c) ^ p⁻¹ +
          f.sublevelEnergyRoot (h.bandTest l u) (bandThreshold l u))) := by
    change Tendsto (fun n ↦ M n + E.rootSeminorm (f.oscillation (h.bandTest l u) (bandThreshold l u) n) +
      E.rootSeminorm (g.ramp (oscillationWidth n) a).domainElement) atTop _
    simpa only [add_zero] using (hMlim.add hVlim).add (g.tendsto_root_ramp a)
  apply le_of_tendsto_of_tendsto (f.tendsto_sublevelEnergyRoot g a) hlim
  filter_upwards [tendsto_oscillationWidth.eventually_lt_const (sub_pos.mpr haa'),
    tendsto_oscillationWidth.eventually_lt_const (show 0 < ε / 2 by positivity)]
    with n hna hnε
  have hn := oscillationWidth_pos n
  have hgap : l + 2 * r n < u := by dsimp [l, u, r]; linarith only [hnε]
  have hdisj : Disjoint (support (A n).toFun) (support (B n).toFun) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    have hx' : h.toFun x < l + r n := by
      by_contra! hfar
      apply hx
      change min _ (sublevelRamp (r n) l (h.toFun x)) = 0
      rw [sublevelRamp_eq_zero hfar, min_eq_right (sawtooth_nonneg _ _)]
    apply hy
    rw [hBval, sublevelRamp_eq_zero (show -u + r n ≤ -h.toFun x by linarith only [hgap, hx'])]
    exact min_eq_right (le_min (sawtooth_nonneg _ _) (sublevelRamp_nonneg _ _ _))
  have hW : (W n).domainElement = f.oscillation g a n := by
    change (W n).domainElement = (f.oscillationCore g a n).domainElement
    apply domainElement_eq_of_toFun_eq
    funext x
    let U := sawtooth (r n) (f.toFun x)
    have hU₀ : 0 ≤ U := sawtooth_nonneg _ _
    have hU := sawtooth_le hn (f.toFun x)
    change min ((((A n).add (B n)).sup (V n)).toFun x)
        (offsetRamp (r n) a (g.toFun x) + sublevelRamp (r n) a 0) =
      min U (sublevelRamp (r n) a (g.toFun x))
    rw [sup_apply, offsetRamp, sub_add_cancel]
    have hA₀ : 0 ≤ (A n).toFun x := le_min hU₀ (sublevelRamp_nonneg _ _ _)
    have hA : (A n).toFun x ≤ U := min_le_left _ _
    have hB₀ : 0 ≤ (B n).toFun x := by
      rw [hBval]
      exact le_min (le_min hU₀ (sublevelRamp_nonneg _ _ _)) (sublevelRamp_nonneg _ _ _)
    have hB : (B n).toFun x ≤ U := by
      rw [hBval]
      exact (min_le_left _ _).trans (min_le_left _ _)
    have hV : (V n).toFun x ≤ U := min_le_left _ _
    change min (max ((A n).toFun x + (B n).toFun x) ((V n).toFun x)) _ = _
    have hadd : (A n).toFun x + (B n).toFun x ≤ U := by
      by_cases hx : x ∈ support (A n).toFun
      · rw [notMem_support.mp (Set.disjoint_left.mp hdisj hx), add_zero]
        exact hA
      · rw [notMem_support.mp hx, zero_add]
        exact hB
    by_cases hfar : a + r n ≤ g.toFun x
    · rw [sublevelRamp_eq_zero hfar, min_eq_right hU₀,
        min_eq_right ((add_nonneg hA₀ hB₀).trans (le_max_left _ _))]
    · apply congrArg (fun t ↦ min t (sublevelRamp (r n) a (g.toFun x)))
      apply le_antisymm (max_le hadd hV)
      by_cases hx : x ∈ tsupport f.toFun
      · have hg : g.toFun x ≤ a' := by linarith only [lt_of_not_ge hfar, hna]
        have ha (ht : h.toFun x ≤ l) : (A n).toFun x = U := by
          change min U (sublevelRamp (r n) l (h.toFun x)) = U
          rw [sublevelRamp_eq_cap hn.le ht, min_eq_left hU]
        by_cases hxl : h.toFun x ≤ l
        · rw [← ha hxl]
          exact (le_add_of_nonneg_right hB₀).trans (le_max_left _ _)
        have hk : k.toFun x ≤ c := (hsub x hx hg).resolve_left (fun h' ↦
          hxl (h'.trans (by dsimp [l]; linarith only [hε])))
        by_cases hxu : h.toFun x ≤ u
        · have he : (V n).toFun x = U := by
            rw [hVval, sublevelRamp_eq_cap hn.le hxu,
              sublevelRamp_eq_cap hn.le (neg_le_neg (le_of_not_ge hxl)), min_self, min_eq_left hU]
          rw [← he]
          exact le_max_right _ _
        · have he : (B n).toFun x = U := by
            rw [hBval, sublevelRamp_eq_cap hn.le (neg_le_neg (le_of_not_ge hxu))]
            change min (min U (sublevelRamp (r n) c (k.toFun x))) (r n) = U
            rw [sublevelRamp_eq_cap hn.le hk, min_eq_left hU, min_eq_left hU]
          rw [← he]
          exact (le_add_of_nonneg_left hA₀).trans (le_max_left _ _)
      · have hz := notMem_support.mp (fun hy ↦ hx (subset_closure hy))
        change sawtooth (r n) (f.toFun x) ≤ _
        rw [hz, sawtooth_zero]
        exact (add_nonneg hA₀ hB₀).trans (le_max_left _ _)
  have hAB : E.rootSeminorm ((A n).add (B n)).domainElement ≤ M n := by
    rw [E.rootSeminorm_apply, (A n).energy_add_of_disjoint_support (B n) hdisj, NNReal.coe_add]
    apply Real.rpow_le_rpow (by positivity) _ (inv_nonneg.mpr (zero_lt_one.trans E.one_lt).le)
    rw [E.energy_eq_root_rpow (B n).domainElement]
    exact add_le_add_right (Real.rpow_le_rpow (apply_nonneg _ _) (hBroot n)
      (zero_lt_one.trans E.one_lt).le) _
  change E.rootSeminorm (f.oscillation g a n) ≤ _
  rw [← hW]
  exact ((((A n).add (B n)).sup (V n)).root_minAddConst_le (T n) _).trans
    (add_le_add_left ((((A n).add (B n)).root_sup_le (V n)).trans
      (add_le_add_left hAB _)) _)

theorem tendsto_sublevelDistribution_add_width (f g : E.CompactCore) (b c : ℝ) (hc : 0 ≤ c) :
    Tendsto (fun n ↦ f.sublevelDistribution g (b + c * oscillationWidth n))
      atTop (𝓝 (f.sublevelDistribution g b)) := by
  have ht : Tendsto (fun n ↦ b + c * oscillationWidth n) atTop (𝓝[≥] b) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall (fun n ↦ ?_)⟩
    · simpa only [mul_zero, add_zero] using (tendsto_oscillationWidth.const_mul c).const_add b
    · exact le_add_of_nonneg_right (mul_nonneg hc (oscillationWidth_pos n).le)
  exact ((f.sublevelDistribution g).right_continuous' b).tendsto.comp ht

set_option maxHeartbeats 450000 in
theorem sublevelDistribution_le_add_of_sublevel_subset (f g h k : E.CompactCore) {a b c : ℝ}
    (hsub : ∀ x ∈ tsupport f.toFun, g.toFun x ≤ a → h.toFun x ≤ b ∨ k.toFun x ≤ c) :
    f.sublevelDistribution g a ≤ f.sublevelDistribution h b + f.sublevelDistribution k c := by
  let d := oscillationWidth
  let H (n : ℕ) := f.sublevelDistribution h (b + 2 * d n)
  let K (n : ℕ) := f.sublevelDistribution k (c + d n)
  let R (n : ℕ) := f.sublevelDistribution h (b + 3 * d n) - f.sublevelDistribution h (b + d n)
  have hp : 0 < p := zero_lt_one.trans E.one_lt
  have hinv : 0 ≤ p⁻¹ := inv_nonneg.mpr hp.le
  have hlim : Tendsto (fun n ↦ (H n + K n) ^ p⁻¹ + (R n) ^ p⁻¹) atTop
      (𝓝 ((f.sublevelDistribution h b + f.sublevelDistribution k c) ^ p⁻¹)) := by
    have hH : Tendsto H atTop (𝓝 (f.sublevelDistribution h b)) :=
      f.tendsto_sublevelDistribution_add_width h b 2 (by norm_num)
    have hK : Tendsto K atTop (𝓝 (f.sublevelDistribution k c)) := by
      simpa only [one_mul] using f.tendsto_sublevelDistribution_add_width k c 1 zero_le_one
    have hR : Tendsto R atTop (𝓝 0) := by
      simpa only [one_mul, sub_self] using
        (f.tendsto_sublevelDistribution_add_width h b 3 (by norm_num)).sub
          (f.tendsto_sublevelDistribution_add_width h b 1 zero_le_one)
    have hpow := Real.continuous_rpow_const hinv
    have hHK := (hpow.tendsto _).comp (hH.add hK)
    have hRpow := (hpow.tendsto 0).comp hR
    have ht := hHK.add hRpow
    simpa only [Function.comp_def, Real.zero_rpow (inv_ne_zero hp.ne'), add_zero] using ht
  have hRoot : f.sublevelEnergyRoot g a ≤
      (f.sublevelDistribution h b + f.sublevelDistribution k c) ^ p⁻¹ := by
    apply ge_of_tendsto hlim
    refine Eventually.of_forall fun n ↦ ?_
    let ε := d n
    have hε : 0 < ε := oscillationWidth_pos n
    let j (x : X) := min (h.toFun x - b) (k.toFun x - c)
    have hj : Continuous j := (h.continuous.sub continuous_const).min (k.continuous.sub continuous_const)
    have hs : ∀ x ∈ tsupport f.toFun, g.toFun x ≤ a → j x ≤ 0 := by
      intro x hx hga
      rcases hsub x hx hga with hh | hk
      · exact (min_le_left _ _).trans (sub_nonpos.mpr hh)
      · exact (min_le_right _ _).trans (sub_nonpos.mpr hk)
    obtain ⟨a', ha', hbuffer⟩ := exists_sublevel_buffer f.compactSupport.isCompact g.continuous hj hε hs
    have hs' : ∀ x ∈ tsupport f.toFun, g.toFun x ≤ a' →
        h.toFun x ≤ b + ε ∨ k.toFun x ≤ c + ε := by
      intro x hx hxa
      rcases min_le_iff.mp (hbuffer x hx hxa) with hh | hk
      · exact Or.inl (by linarith only [hh])
      · exact Or.inr (by linarith only [hk])
    have hUnion := f.sublevelEnergyRoot_le_buffered_union g h k ha' hε hs'
    have hl : b + ε < b + ε + ε := by linarith only [hε]
    have hu : b + ε + ε < b + ε + 2 * ε := by linarith only [hε]
    have hBand := f.band_energy_le h hl hu
    have hBandRoot : f.sublevelEnergyRoot (h.bandTest (b + ε + ε) (b + ε + 2 * ε))
        (bandThreshold (b + ε + ε) (b + ε + 2 * ε)) ≤ (R n) ^ p⁻¹ := by
      change f.sublevelEnergyRoot (h.bandTest (b + ε + ε) (b + ε + 2 * ε))
        (bandThreshold (b + ε + ε) (b + ε + 2 * ε)) ^ p ≤ _ at hBand
      have hb := Real.rpow_le_rpow (Real.rpow_nonneg (f.sublevelEnergyRoot_nonneg _ _) p) hBand hinv
      rw [← Real.rpow_mul (f.sublevelEnergyRoot_nonneg _ _), mul_inv_cancel₀ hp.ne', Real.rpow_one] at hb
      have he : b + ε + 2 * ε = b + 3 * ε := by ring
      simpa only [R, he] using hb
    have he : b + ε + ε = b + 2 * ε := by ring
    have hr := hUnion.trans (add_le_add_right hBandRoot _)
    simpa only [H, K, he] using hr
  change f.sublevelEnergyRoot g a ^ p ≤ _
  have hs : 0 ≤ f.sublevelDistribution h b + f.sublevelDistribution k c :=
    add_nonneg (Real.rpow_nonneg (f.sublevelEnergyRoot_nonneg _ _) _) (Real.rpow_nonneg (f.sublevelEnergyRoot_nonneg _ _) _)
  have hd := Real.rpow_le_rpow (f.sublevelEnergyRoot_nonneg g a) hRoot hp.le
  rwa [← Real.rpow_mul hs, inv_mul_cancel₀ hp.ne', Real.rpow_one] at hd

end WalkDimensions.PEnergy.CompactCore
