module

public import Camus.Pipelines.NMSC.Anomaly
public import Camus.Pipelines.NMSC.Recovery
public import Camus.External.NMSC.AnomalyRegion

/-!
# Section 3.3: Quartet Filtering on the 3-cycle above two taxa, for all parameters

Section 3.3 motivates Quartet Filtering (Algorithm 1): "The motivation for this approach is that we
do not want to include quartet trees that are not in Q(Nr). On the other hand, we do not want to
eliminate these quartet trees." `Camus/Pipelines/NMSC/Anomaly.lean` shows one network on which
Algorithm 1 does both, for every threshold. This file finds all the parameters of that network for
which it does. The network is `N₃₂` (`Brooqs.net32`) on the taxa `0, 1, 2, 3`, with any metric
parameters (`NMSC.net32On`): `0` and `1` below the hybrid node of a 3-cycle, with an edge of length
`ℓ` above them, `2` on the side `S₁` of the cycle (an edge of length `L` from the top node, then the
hybrid edge of length `h₁` and inheritance probability `γ`), the side `S₂` a hybrid edge of length
`h₂`, and `3` outside the cycle. Whatever the parameters, the four taxa are in the anomalous
configuration (`NMSC.net32On_anomalous`), so `NMSC.NoAnomaly` fails, and `N₃₂` displays only
`01|23` of the three quartet trees on them (`NMSC.net32On_displaysQuartet`). Let
`A = γ(1 - γ)(1 - e^{-L})` and `R = γ²(1 - e^{-h₁}) + (1 - γ)²(1 - e^{-h₂}) + (e^ℓ - 1)`
(`Brooqs.net32_anomalous_iff`).

* If `R < A`, for every threshold, almost surely, for all large numbers of genes, Algorithm 1
  returns no copy of `01|23` and returns a quartet tree that is not in Q(N_r)
  (`NMSC.net32On_filterQuartets`), and no tree of maximum quartet support score is a displayed
  tree of `N₃₂` (`NMSC.net32On_astral`).
* If `A < R`, and only then, the four taxa have the pattern that Quartet Filtering presumes
  (`NMSC.net32On_regularOn_iff`), the bound on the threshold is `t₀(N₃₂) = 1`
  (`NMSC.threshold_net32On`), and for every threshold `0 < t < 1`, almost surely, for all large
  numbers of genes, Algorithm 1 returns exactly the quartet trees of the gene trees that are in
  Q(N_r), with their multiplicities (`NMSC.net32On_filterQuartets_regular`); its support is Q(N_r)
  (`NMSC.net32On_filterQuartets_support`).

So on `N₃₂` Quartet Filtering is defeated exactly in the anomaly zone of
`Brooqs.net32_anomalous_iff`, up to the boundary `A = R`, where the three quartet trees are equally
probable (`Brooqs.net32_boundary_iff_third`), and the strong law of large numbers does not decide
which of them Algorithm 1 keeps. Both zones contain metric parameters
(`Brooqs.net32_anomalous_of_short`, `Brooqs.net32_regular_of_log`).

## Main results

* `NMSC.net32On`, `NMSC.net32On_wellFormed`, `NMSC.net32On_displaysQuartet`,
  `NMSC.net32On_anomalous`: the network, for all parameters.
* `NMSC.net32On_quartetProb_lt_iff`, `NMSC.net32On_quartetProb_gt_iff`: the two zones, for the
  probabilities of the quartet trees of CAMUS.
* `NMSC.net32On_filterQuartets`, `NMSC.net32On_filterQuartets_genes`,
  `NMSC.net32On_filterQuartets_graph`, `NMSC.net32On_astral`: in the anomaly zone, Algorithm 1 and
  ASTRAL fail.
* `NMSC.net32On_regularOn_iff`, `NMSC.threshold_net32On`, `NMSC.net32On_filterQuartets_regular`,
  `NMSC.net32On_filterQuartets_support`, `NMSC.net32On_filterQuartets_support_graph`: in the
  regular zone, Algorithm 1 keeps exactly the quartet trees of Q(N_r).

## Proof

In the anomaly zone, the proof of `NMSC.anomaly_filterQuartets` and `NMSC.anomaly_astral` applies to
any network on `0, 1, 2, 3` that displays only `01|23` and under which `01|23` is strictly the least
probable quartet tree (`NMSC.filterQuartets_of_least`, `NMSC.astral_of_least`). In the regular zone,
`NMSC.nmsc_filterQuartets` applies, with `NMSC.Regular` from `NMSC.net32On_regularOn_iff`.
-/

@[expose] public noncomputable section

namespace Camus

namespace NMSC

open Finset Filter Topology MeasureTheory ProbabilityTheory Coalescent Algorithm1

/-! ### The network -/

/-- The network `N₃₂` of `Brooqs.net32` on the taxa `0, 1, 2, 3`, with any parameters: the taxa
`x = 0` and `y = 1` below the hybrid node of a 3-cycle, with an edge of length `ℓ` above their
cherry; `z = 2` on the side `S₁` of the cycle, an edge of length `L` from the top node followed by
the hybrid edge of length `h₁` and inheritance probability `γ`; the side `S₂` a hybrid edge of
length `h₂`; `w = 3` outside the cycle. `NMSC.anomalyNet` is
`net32On (1/2) (1/20) (1/20) (1/20) 3` (`NMSC.anomalyNet_eq_net32On`). -/
def net32On (γ ℓ h₁ h₂ L : ℝ) : Brooqs.Net taxa4 :=
  Brooqs.net32 γ ℓ h₁ h₂ L ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨2, by decide⟩ ⟨3, by decide⟩

theorem anomalyNet_eq_net32On : anomalyNet = net32On (1 / 2) (1 / 20) (1 / 20) (1 / 20) 3 := rfl

/-- `net32On` is a metric network with distinct leaf labels when `0 < γ < 1` and its edge lengths
are positive. -/
theorem net32On_wellFormed {γ ℓ h₁ h₂ L : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hℓ : 0 < ℓ)
    (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) (hL : 0 < L) : (net32On γ ℓ h₁ h₂ L).WellFormed :=
  Brooqs.net32_wellFormed (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hγ0 hγ1 hℓ hh₁ hh₂ hL

/-- The leaves of `net32On` have distinct labels, whatever the parameters. -/
theorem net32On_nodup (γ ℓ h₁ h₂ L : ℝ) : (net32On γ ℓ h₁ h₂ L).leaves.Nodup := by
  rw [net32On, Brooqs.net32_leaves]
  decide

/-- The taxa of `net32On` are `0, 1, 2, 3`. -/
theorem net32On_taxa (γ ℓ h₁ h₂ L : ℝ) : ∀ x : taxa4, x ∈ (net32On γ ℓ h₁ h₂ L).taxa := by
  rw [net32On, Brooqs.Net.taxa, Brooqs.net32_leaves]
  decide

/-- Of the three quartet trees on `0, 1, 2, 3`, `net32On` displays only `01|23`, whatever the
parameters. -/
theorem net32On_displaysQuartet (γ ℓ h₁ h₂ L : ℝ) (s : Fin 3) :
    DisplaysQuartet (net32On γ ℓ h₁ h₂ L) (key4.quartet s) ↔ s = 0 := by
  obtain ⟨h0, h1, h2⟩ := Brooqs.net32_displays (X := taxa4) (x := ⟨0, by decide⟩)
    (y := ⟨1, by decide⟩) (z := ⟨2, by decide⟩) (w := ⟨3, by decide⟩) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) γ ℓ h₁ h₂ L
  obtain ⟨e0, e1, e2⟩ := displaysQuartet_iff (net32On γ ℓ h₁ h₂ L) key4 keyTaxa_key4
  fin_cases s
  · exact ⟨fun _ => rfl, fun _ => e0.2 h0⟩
  · exact ⟨fun h => absurd (e1.1 h) h1, fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd (e2.1 h) h2, fun h => absurd h (by decide)⟩

/-- The four taxa `0, 1, 2, 3` of `net32On` are in the anomalous configuration
(`Brooqs.Net.Anomalous`), whatever the parameters: `0` and `1` below the hybrid node of the
3-cycle, `2` on a side of it and `3` outside it. -/
theorem net32On_anomalous (γ ℓ h₁ h₂ L : ℝ) :
    (net32On γ ℓ h₁ h₂ L).Anomalous (keyTaxon key4 keyTaxa_key4) := by
  refine ⟨Brooqs.net32Cycle (X := taxa4) γ ℓ h₁ h₂ L ⟨0, by decide⟩ ⟨1, by decide⟩
    ⟨2, by decide⟩ ⟨3, by decide⟩, ?_, ?_, ?_⟩
  · show #(Brooqs.Net.lin (keyTaxon key4 keyTaxa_key4)
      (.tree 1 (.leaf ⟨0, by decide⟩) 1 (.leaf ⟨1, by decide⟩) : Brooqs.Net taxa4)) = 2
    decide
  · simp only [Brooqs.Net.Cycle.top, Brooqs.net32Cycle, Brooqs.Net.lin, Brooqs.Net.taxa,
      Brooqs.Net.leaves, Brooqs.Side.leaves]
    decide
  · intro n hn
    simp only [Brooqs.net32Cycle, Brooqs.Side.nodes, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hn
    subst hn
    show #(Brooqs.Net.lin (keyTaxon key4 keyTaxa_key4)
      (.leaf ⟨2, by decide⟩ : Brooqs.Net taxa4)) ≤ 1
    decide

/-- `NMSC.NoAnomaly` fails for `net32On`, whatever the parameters. -/
theorem not_noAnomaly_net32On (γ ℓ h₁ h₂ L : ℝ) : ¬ NoAnomaly (net32On γ ℓ h₁ h₂ L) :=
  fun h => h _ (keyTaxon key4 keyTaxa_key4).injective (net32On_anomalous γ ℓ h₁ h₂ L)

/-! ### The probabilities of the quartet trees -/

/-- **The anomaly zone, for the quartet trees of CAMUS.** For all parameters, under the NMSC on
`net32On`, the quartet tree `01|23` is strictly less probable than `02|13` iff
`γ²(1 - e^{-h₁}) + (1 - γ)²(1 - e^{-h₂}) + (e^ℓ - 1) < γ(1 - γ)(1 - e^{-L})`
(`Brooqs.net32_anomalous_iff`). -/
theorem net32On_quartetProb_lt_iff (γ ℓ h₁ h₂ L : ℝ) :
    quartetProb (net32On γ ℓ h₁ h₂ L) (key4.quartet 0) <
        quartetProb (net32On γ ℓ h₁ h₂ L) (key4.quartet 1) ↔
      γ ^ 2 * (1 - Real.exp (-h₁)) + (1 - γ) ^ 2 * (1 - Real.exp (-h₂)) + (Real.exp ℓ - 1) <
        γ * (1 - γ) * (1 - Real.exp (-L)) := by
  obtain ⟨p0, p1, -⟩ := quartetProb_eq_quartetCF _ (net32On_nodup γ ℓ h₁ h₂ L) key4 keyTaxa_key4
  rw [p0, p1]
  exact Brooqs.net32_anomalous_iff (X := taxa4) (x := ⟨0, by decide⟩) (y := ⟨1, by decide⟩)
    (z := ⟨2, by decide⟩) (w := ⟨3, by decide⟩) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) γ ℓ h₁ h₂ L

/-- **The regular zone, for the quartet trees of CAMUS.** For all parameters, under the NMSC on
`net32On`, the quartet tree `01|23` is strictly more probable than `02|13` iff
`γ(1 - γ)(1 - e^{-L}) < γ²(1 - e^{-h₁}) + (1 - γ)²(1 - e^{-h₂}) + (e^ℓ - 1)`
(`Brooqs.net32_regular_iff`). -/
theorem net32On_quartetProb_gt_iff (γ ℓ h₁ h₂ L : ℝ) :
    quartetProb (net32On γ ℓ h₁ h₂ L) (key4.quartet 1) <
        quartetProb (net32On γ ℓ h₁ h₂ L) (key4.quartet 0) ↔
      γ * (1 - γ) * (1 - Real.exp (-L)) <
        γ ^ 2 * (1 - Real.exp (-h₁)) + (1 - γ) ^ 2 * (1 - Real.exp (-h₂)) + (Real.exp ℓ - 1) := by
  obtain ⟨p0, p1, -⟩ := quartetProb_eq_quartetCF _ (net32On_nodup γ ℓ h₁ h₂ L) key4 keyTaxa_key4
  rw [p0, p1]
  exact Brooqs.net32_regular_iff (X := taxa4) (x := ⟨0, by decide⟩) (y := ⟨1, by decide⟩)
    (z := ⟨2, by decide⟩) (w := ⟨3, by decide⟩) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) γ ℓ h₁ h₂ L

/-- Under the NMSC on `net32On`, the quartet trees `02|13` and `03|12` are equally probable, for
all parameters. -/
theorem net32On_quartetProb_eq (γ ℓ h₁ h₂ L : ℝ) :
    quartetProb (net32On γ ℓ h₁ h₂ L) (key4.quartet 1) =
      quartetProb (net32On γ ℓ h₁ h₂ L) (key4.quartet 2) := by
  obtain ⟨-, p1, p2⟩ := quartetProb_eq_quartetCF _ (net32On_nodup γ ℓ h₁ h₂ L) key4 keyTaxa_key4
  rw [p1, p2]
  exact (Brooqs.net32_quartetCF_excess (X := taxa4) (x := ⟨0, by decide⟩) (y := ⟨1, by decide⟩)
    (z := ⟨2, by decide⟩) (w := ⟨3, by decide⟩) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) γ ℓ h₁ h₂ L).2.2.symm

/-- In the anomaly zone, `01|23` is strictly less probable than each of the two other quartet
trees on `0, 1, 2, 3`. -/
theorem net32On_quartetProb_least {γ ℓ h₁ h₂ L : ℝ}
    (hzone : γ ^ 2 * (1 - Real.exp (-h₁)) + (1 - γ) ^ 2 * (1 - Real.exp (-h₂)) +
      (Real.exp ℓ - 1) < γ * (1 - γ) * (1 - Real.exp (-L))) (s : Fin 3) (hs : s ≠ 0) :
    quartetProb (net32On γ ℓ h₁ h₂ L) (key4.quartet 0) <
      quartetProb (net32On γ ℓ h₁ h₂ L) (key4.quartet s) := by
  have h1 := (net32On_quartetProb_lt_iff γ ℓ h₁ h₂ L).2 hzone
  fin_cases s
  · exact absurd rfl hs
  · exact h1
  · exact h1.trans_eq (net32On_quartetProb_eq γ ℓ h₁ h₂ L)

/-! ### The anomaly zone: Quartet Filtering and ASTRAL fail -/

/-- On the taxa `0, 1, 2, 3`, the quartet support score of a well-labelled tree is the number of
copies of the one quartet tree it induces. -/
private theorem ar_quartetSupport (Q : Multiset Quartet) {T : PhyloTree} (hT : T.WellLabelled)
    (hTt : T.taxa = taxa4) : quartetSupport Q T = Q.count (key4.quartet (T.splitOf key4)) := by
  rw [quartetSupport_eq_sum_keys Q T hT, hTt, keysOn_taxa4, sum_singleton]

/-- The tree `((0, 2), (1, 3))`, which induces `02|13`. -/
private def ar_tree : PhyloTree := .fork (.fork (.leaf 0) (.leaf 2)) (.fork (.leaf 1) (.leaf 3))

private theorem ar_tree_facts : ar_tree.WellLabelled ∧ ar_tree.taxa = taxa4 ∧
    (key4.quartet 1).induced ar_tree = true := by
  refine ⟨by decide, by decide, by decide⟩

section Genes

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  [MeasurableSpace (Finset (Finset taxa4))] [MeasurableSingletonClass (Finset (Finset taxa4))]

/-- For independent gene trees with the law of the NMSC on a metric network on `0, 1, 2, 3` under
which `01|23` is strictly the least probable quartet tree, almost surely, for all large numbers `n`
of genes, `01|23` has strictly fewer copies than each of the two others among the quartet trees of
the first `n` gene trees, and `02|13` has a copy. -/
private theorem ar_eventually {N : Brooqs.Net taxa4} (hN : N.WellFormed)
    (hlt : ∀ s, s ≠ 0 → quartetProb N (key4.quartet 0) < quartetProb N (key4.quartet s))
    (G : ℕ → Ω → Finset (Finset taxa4)) (hind : iIndepFun G P)
    (hid : ∀ n, IdentDistrib (G n) (G 0) P P)
    (hlaw : ∀ T, P.real (G 0 ⁻¹' {T}) = N.geneTreeDist id T) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      (∀ s, s ≠ 0 → (geneQuartets (fun i => G i ω) n).count (key4.quartet 0) <
        (geneQuartets (fun i => G i ω) n).count (key4.quartet s)) ∧
      0 < (geneQuartets (fun i => G i ω) n).count (key4.quartet 1) := by
  set p : Fin 3 → ℝ := fun s => quartetProb N (key4.quartet s) with hpdef
  have hp : ∀ s, P.real {ω | Induces (G 0 ω) (key4.quartet s)} = p s := fun s =>
    measureReal_induces N (G 0) (hid 0).aemeasurable_fst hlaw _
  have hp1 : 0 < p 1 := (quartetProb_nonneg hN _).trans_lt (hlt 1 (by decide))
  -- the strong law of large numbers, for the three quartet trees
  have hconv : ∀ᵐ ω ∂P, ∀ s, Tendsto (fun n : ℕ =>
      ((geneQuartets (fun i => G i ω) n).count (key4.quartet s) : ℝ) / n) atTop (𝓝 (p s)) := by
    rw [ae_all_iff]
    intro s
    rw [← hp]
    exact ae_tendsto_frequency G hind hid _
  filter_upwards [hconv] with ω hω
  have hsep : ∀ s, ∀ᶠ n in atTop, s ≠ 0 →
      ((geneQuartets (fun i => G i ω) n).count (key4.quartet 0) : ℝ) / n <
        ((geneQuartets (fun i => G i ω) n).count (key4.quartet s) : ℝ) / n := by
    intro s
    by_cases hs : s = 0
    · exact Eventually.of_forall fun _ h => absurd hs h
    · filter_upwards [((hω s).sub (hω 0)).eventually_const_lt (sub_pos.2 (hlt s hs))]
        with n hn _
      linarith
  filter_upwards [eventually_all.2 hsep, (hω 1).eventually_const_lt hp1, eventually_gt_atTop 0]
    with n hn hn1 hn0
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn0
  refine ⟨fun s hs => ?_, ?_⟩
  · exact_mod_cast (div_lt_div_iff_of_pos_right hn').1 (hn s hs)
  · have : (0 : ℝ) < (geneQuartets (fun i => G i ω) n).count (key4.quartet 1) := by
      have h := mul_lt_mul_of_pos_right hn1 hn'
      rw [zero_mul, div_mul_cancel₀ _ hn'.ne'] at h
      exact h
    exact_mod_cast this

/-- **Quartet Filtering fails when the displayed quartet tree is the least probable.** Let `N` be
a metric network on the taxa `0, 1, 2, 3` that displays only `01|23` of the three quartet trees on
them, and under which `01|23` is strictly the least probable. Let the gene trees be independent,
each with the law of the NMSC on `N`. For every threshold `t`, almost surely, for all large numbers
`n` of genes, Algorithm 1 applied to the quartet trees of the first `n` gene trees returns no copy
of `01|23` and returns a quartet tree that is not in Q(N_r). The proof is that of
`NMSC.anomaly_filterQuartets`. -/
theorem filterQuartets_of_least {N : Brooqs.Net taxa4} (hN : N.WellFormed)
    (hdisp : ∀ s, DisplaysQuartet N (key4.quartet s) ↔ s = 0)
    (hlt : ∀ s, s ≠ 0 → quartetProb N (key4.quartet 0) < quartetProb N (key4.quartet s))
    (G : ℕ → Ω → Finset (Finset taxa4)) (hind : iIndepFun G P)
    (hid : ∀ n, IdentDistrib (G n) (G 0) P P)
    (hlaw : ∀ T, P.real (G 0 ⁻¹' {T}) = N.geneTreeDist id T) (t : ℝ) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      (filterQuartets t (geneQuartets (fun i => G i ω) n)).count (key4.quartet 0) = 0 ∧
      ∃ q ∈ filterQuartets t (geneQuartets (fun i => G i ω) n), ¬ DisplaysQuartet N q := by
  filter_upwards [ar_eventually hN hlt G hind hid hlaw] with ω hω
  filter_upwards [hω] with n hn
  obtain ⟨hmin, hpos⟩ := hn
  set Q := geneQuartets (fun i => G i ω) n
  set f := frequencies (Q.map quartetEquiv) key4
  have hf : ∀ s, f s = Q.count (key4.quartet s) := fun s => frequencies_map Q key4 s
  -- the quartet tree `01|23` has strictly the smallest count: it is `q₃`
  have h3 : (rank f).2.2 = 0 := rank_snd_snd_eq_of_lt fun s hs => by
    rw [hf, hf]
    exact hmin s hs
  refine ⟨?_, ?_⟩
  · rw [count_filterQuartets]
    have := filterBlock_third_count t (Q.map quartetEquiv) key4
    rwa [h3] at this
  · -- the most frequent quartet tree `q₁` is kept, and it is not `01|23`
    set s₁ := (rank f).1
    have hs₁ : s₁ ≠ 0 := h3 ▸ (rank_distinct f).2.1
    have hmax : f 1 ≤ f s₁ := by
      obtain ⟨h12, h23⟩ := rank_ordered f
      rcases rank_covers f 1 with h | h | h <;> rw [h] <;> omega
    have hcount : 0 < (filterQuartets t Q).count (key4.quartet s₁) := by
      rw [count_filterQuartets]
      have h1 : (filterBlock t (Q.map quartetEquiv) key4).count (key4, s₁) = f s₁ :=
        filterBlock_top_count t (Q.map quartetEquiv) key4
      have h2 : 0 < f 1 := by
        rw [hf]
        exact hpos
      change 0 < (filterBlock t (Q.map quartetEquiv) key4).count (key4, s₁)
      omega
    exact ⟨key4.quartet s₁, Multiset.count_pos.1 hcount,
      fun h => hs₁ ((hdisp s₁).1 h)⟩

/-- **ASTRAL fails when the displayed quartet tree is the least probable.** Under the assumptions
of `NMSC.filterQuartets_of_least`, almost surely, for all large numbers `n` of genes, no tree of
maximum quartet support score for the quartet trees of the first `n` gene trees (among the
well-labelled trees on `0, 1, 2, 3`) is a displayed tree of `N`. The proof is that of
`NMSC.anomaly_astral`. -/
theorem astral_of_least {N : Brooqs.Net taxa4} (hN : N.WellFormed)
    (hdisp : ∀ s, DisplaysQuartet N (key4.quartet s) ↔ s = 0)
    (hlt : ∀ s, s ≠ 0 → quartetProb N (key4.quartet 0) < quartetProb N (key4.quartet s))
    (G : ℕ → Ω → Finset (Finset taxa4)) (hind : iIndepFun G P)
    (hid : ∀ n, IdentDistrib (G n) (G 0) P P)
    (hlaw : ∀ T, P.real (G 0 ⁻¹' {T}) = N.geneTreeDist id T) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ T : PhyloTree, T.WellLabelled → T.taxa = taxa4 →
      (∀ T' : PhyloTree, T'.WellLabelled → T'.taxa = taxa4 →
        quartetSupport (geneQuartets (fun i => G i ω) n) T' ≤
          quartetSupport (geneQuartets (fun i => G i ω) n) T) →
      ¬ DisplaysTree N T := by
  filter_upwards [ar_eventually hN hlt G hind hid hlaw] with ω hω
  filter_upwards [hω] with n hn T hT hTt hopt
  obtain ⟨hmin, -⟩ := hn
  set Q := geneQuartets (fun i => G i ω) n
  obtain ⟨h1, h2, h3⟩ := ar_tree_facts
  have hk : ({key4.a, key4.b, key4.c, key4.d} : Finset ℕ) ⊆ T.taxa := by
    rw [hTt]
    exact subset_rfl
  have hk₁ : ({key4.a, key4.b, key4.c, key4.d} : Finset ℕ) ⊆ ar_tree.taxa := by
    rw [h2]
    exact subset_rfl
  -- the tree `((0, 2), (1, 3))` scores the copies of `02|13`
  have hs₁ : ar_tree.splitOf key4 = 1 :=
    ((PhyloTree.induced_iff_splitOf ar_tree h1 key4 hk₁ 1).1 h3).symm
  have hle := hopt ar_tree h1 h2
  rw [ar_quartetSupport Q h1 h2, hs₁, ar_quartetSupport Q hT hTt] at hle
  -- so `T` does not induce `01|23`
  have hne : T.splitOf key4 ≠ 0 := by
    intro h0
    rw [h0] at hle
    exact absurd hle (not_le.2 (hmin 1 (by decide)))
  -- but every displayed tree of the network does
  rintro ⟨K, hK, hiff⟩
  have hT' : (key4.quartet (T.splitOf key4)).induced T = true :=
    (PhyloTree.induced_iff_splitOf T hT key4 hk _).2 rfl
  exact hne ((hdisp _).1 ⟨K, hK, (hiff _).2 hT'⟩)

/-- **Section 3.3: Quartet Filtering fails in the anomaly zone.** Let `0 < γ < 1` and `ℓ`, `h₁`,
`h₂`, `L` be positive, with
`γ²(1 - e^{-h₁}) + (1 - γ)²(1 - e^{-h₂}) + (e^ℓ - 1) < γ(1 - γ)(1 - e^{-L})`
(`Brooqs.net32_anomalous_iff`), and let the gene trees be independent, each with the law of the
NMSC on `net32On γ ℓ h₁ h₂ L`. For every threshold `t`, almost surely, for all large numbers `n` of
genes, Algorithm 1 applied to the quartet trees of the first `n` gene trees returns no copy of
`01|23`, the only quartet tree on these taxa in Q(N_r), and returns a quartet tree that is not in
Q(N_r). `NMSC.anomaly_filterQuartets` is the case `γ = 1/2`, `ℓ = h₁ = h₂ = 1/20`, `L = 3`. -/
theorem net32On_filterQuartets {γ ℓ h₁ h₂ L : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hℓ : 0 < ℓ)
    (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) (hL : 0 < L)
    (hzone : γ ^ 2 * (1 - Real.exp (-h₁)) + (1 - γ) ^ 2 * (1 - Real.exp (-h₂)) +
      (Real.exp ℓ - 1) < γ * (1 - γ) * (1 - Real.exp (-L)))
    (G : ℕ → Ω → Finset (Finset taxa4)) (hind : iIndepFun G P)
    (hid : ∀ n, IdentDistrib (G n) (G 0) P P)
    (hlaw : ∀ T, P.real (G 0 ⁻¹' {T}) = (net32On γ ℓ h₁ h₂ L).geneTreeDist id T) (t : ℝ) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      (filterQuartets t (geneQuartets (fun i => G i ω) n)).count (key4.quartet 0) = 0 ∧
      ∃ q ∈ filterQuartets t (geneQuartets (fun i => G i ω) n),
        ¬ DisplaysQuartet (net32On γ ℓ h₁ h₂ L) q :=
  filterQuartets_of_least (net32On_wellFormed hγ0 hγ1 hℓ hh₁ hh₂ hL)
    (net32On_displaysQuartet γ ℓ h₁ h₂ L) (net32On_quartetProb_least hzone) G hind hid hlaw t

/-- **Section 3.3: ASTRAL fails in the anomaly zone.** Under the assumptions of
`NMSC.net32On_filterQuartets`, almost surely, for all large numbers `n` of genes, no tree of maximum
quartet support score for the quartet trees of the first `n` gene trees (among the well-labelled
trees on `0, 1, 2, 3`) is a displayed tree of `net32On γ ℓ h₁ h₂ L`. -/
theorem net32On_astral {γ ℓ h₁ h₂ L : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hℓ : 0 < ℓ)
    (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) (hL : 0 < L)
    (hzone : γ ^ 2 * (1 - Real.exp (-h₁)) + (1 - γ) ^ 2 * (1 - Real.exp (-h₂)) +
      (Real.exp ℓ - 1) < γ * (1 - γ) * (1 - Real.exp (-L)))
    (G : ℕ → Ω → Finset (Finset taxa4)) (hind : iIndepFun G P)
    (hid : ∀ n, IdentDistrib (G n) (G 0) P P)
    (hlaw : ∀ T, P.real (G 0 ⁻¹' {T}) = (net32On γ ℓ h₁ h₂ L).geneTreeDist id T) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ T : PhyloTree, T.WellLabelled → T.taxa = taxa4 →
      (∀ T' : PhyloTree, T'.WellLabelled → T'.taxa = taxa4 →
        quartetSupport (geneQuartets (fun i => G i ω) n) T' ≤
          quartetSupport (geneQuartets (fun i => G i ω) n) T) →
      ¬ DisplaysTree (net32On γ ℓ h₁ h₂ L) T :=
  astral_of_least (net32On_wellFormed hγ0 hγ1 hℓ hh₁ hh₂ hL)
    (net32On_displaysQuartet γ ℓ h₁ h₂ L) (net32On_quartetProb_least hzone) G hind hid hlaw

/-- **Section 3.3: Quartet Filtering fails in the anomaly zone, in the graph representation.**
Under the assumptions of `NMSC.net32On_filterQuartets`, let
`N_r = Realization.graph (baseTree N) (pairs N)` be the graph of `N = net32On γ ℓ h₁ h₂ L`. `N_r`
displays `01|23`, and for every threshold `t`, almost surely, for all large numbers `n` of genes,
Algorithm 1 applied to the quartet trees of the first `n` gene trees returns no copy of `01|23` and
returns a quartet tree that `N_r` does not display. -/
theorem net32On_filterQuartets_graph {γ ℓ h₁ h₂ L : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hℓ : 0 < ℓ)
    (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) (hL : 0 < L)
    (hzone : γ ^ 2 * (1 - Real.exp (-h₁)) + (1 - γ) ^ 2 * (1 - Real.exp (-h₂)) +
      (Real.exp ℓ - 1) < γ * (1 - γ) * (1 - Real.exp (-L)))
    (G : ℕ → Ω → Finset (Finset taxa4)) (hind : iIndepFun G P)
    (hid : ∀ n, IdentDistrib (G n) (G 0) P P)
    (hlaw : ∀ T, P.real (G 0 ⁻¹' {T}) = (net32On γ ℓ h₁ h₂ L).geneTreeDist id T) (t : ℝ) :
    (Realization.graph (baseTree (net32On γ ℓ h₁ h₂ L))
        (pairs (net32On γ ℓ h₁ h₂ L))).DisplaysQuartet (key4.quartet 0) ∧
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      (filterQuartets t (geneQuartets (fun i => G i ω) n)).count (key4.quartet 0) = 0 ∧
      ∃ q ∈ filterQuartets t (geneQuartets (fun i => G i ω) n),
        ¬ (Realization.graph (baseTree (net32On γ ℓ h₁ h₂ L))
          (pairs (net32On γ ℓ h₁ h₂ L))).DisplaysQuartet q := by
  have hiff := graph_displaysQuartet_iff (net32On_wellFormed hγ0 hγ1 hℓ hh₁ hh₂ hL)
    (net32On_taxa γ ℓ h₁ h₂ L)
  refine ⟨(hiff _).2 ((net32On_displaysQuartet γ ℓ h₁ h₂ L 0).2 rfl), ?_⟩
  filter_upwards [net32On_filterQuartets hγ0 hγ1 hℓ hh₁ hh₂ hL hzone G hind hid hlaw t] with ω hω
  filter_upwards [hω] with n hn
  obtain ⟨h0, q, hq, hnq⟩ := hn
  exact ⟨h0, q, hq, fun h => hnq ((hiff q).1 h)⟩

end Genes

/-- Section 3.4, for gene trees that exist: the hypotheses of `NMSC.net32On_filterQuartets` on the
gene trees hold for the coordinates of `Brooqs.Net.genes`, the product law of independent gene trees
under the NMSC. -/
theorem net32On_filterQuartets_genes {γ ℓ h₁ h₂ L : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hℓ : 0 < ℓ) (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) (hL : 0 < L)
    (hzone : γ ^ 2 * (1 - Real.exp (-h₁)) + (1 - γ) ^ 2 * (1 - Real.exp (-h₂)) +
      (Real.exp ℓ - 1) < γ * (1 - γ) * (1 - Real.exp (-L))) (t : ℝ) :
    ∀ᵐ ω ∂((net32On γ ℓ h₁ h₂ L).genes (net32On_wellFormed hγ0 hγ1 hℓ hh₁ hh₂ hL)),
      ∀ᶠ n in atTop,
        (filterQuartets t (geneQuartets (fun i => ω i) n)).count (key4.quartet 0) = 0 ∧
        ∃ q ∈ filterQuartets t (geneQuartets (fun i => ω i) n),
          ¬ DisplaysQuartet (net32On γ ℓ h₁ h₂ L) q :=
  net32On_filterQuartets hγ0 hγ1 hℓ hh₁ hh₂ hL hzone
    (fun n (ω : ℕ → Finset (Finset taxa4)) => ω n)
    ((net32On γ ℓ h₁ h₂ L).genes_iIndepFun (net32On_wellFormed hγ0 hγ1 hℓ hh₁ hh₂ hL))
    ((net32On γ ℓ h₁ h₂ L).genes_identDistrib (net32On_wellFormed hγ0 hγ1 hℓ hh₁ hh₂ hL))
    ((net32On γ ℓ h₁ h₂ L).genes_law (net32On_wellFormed hγ0 hγ1 hℓ hh₁ hh₂ hL)) t

/-! ### The regular zone: Quartet Filtering keeps Q(N_r) -/

/-- **The CF pattern on `N₃₂`.** For metric parameters, the four taxa `0, 1, 2, 3` of `net32On`
have the pattern that Quartet Filtering presumes (`NMSC.RegularOn`) iff
`γ(1 - γ)(1 - e^{-L}) < γ²(1 - e^{-h₁}) + (1 - γ)²(1 - e^{-h₂}) + (e^ℓ - 1)`. -/
theorem net32On_regularOn_iff {γ ℓ h₁ h₂ L : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hℓ : 0 < ℓ)
    (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) (hL : 0 < L) :
    RegularOn (net32On γ ℓ h₁ h₂ L) key4 ↔
      γ * (1 - γ) * (1 - Real.exp (-L)) <
        γ ^ 2 * (1 - Real.exp (-h₁)) + (1 - γ) ^ 2 * (1 - Real.exp (-h₂)) + (Real.exp ℓ - 1) := by
  have hN := net32On_wellFormed hγ0 hγ1 hℓ hh₁ hh₂ hL
  have hdisp := net32On_displaysQuartet γ ℓ h₁ h₂ L
  have heq := net32On_quartetProb_eq γ ℓ h₁ h₂ L
  have hother : ∀ a : Fin 3, ∃ u : Fin 3, u ≠ a ∧ u ≠ 0 := by decide
  have hpair : ∀ a b : Fin 3, a ≠ 0 → b ≠ 0 → a = b ∨ (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) := by
    decide
  rw [← net32On_quartetProb_gt_iff]
  constructor
  · rintro (⟨s₁, h₁', -, hmax, -, -⟩ | ⟨s₃, -, hd, -⟩)
    · obtain rfl := (hdisp s₁).1 h₁'
      exact hmax 1 (by decide)
    · -- two quartet trees would be displayed, but only `01|23` is
      obtain ⟨u, hu₃, hu0⟩ := hother s₃
      exact absurd ((hdisp u).1 (hd u hu₃)) hu0
  · intro hlt
    refine Or.inl ⟨0, (hdisp 0).2 rfl, fun s hs hd => hs ((hdisp s).1 hd), fun s hs => ?_,
      fun s s' hs hs' => ?_, fun s => quartetProb_pos hN (net32On_taxa γ ℓ h₁ h₂ L) ?_⟩
    · rcases hpair s 1 hs (by decide) with rfl | ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact hlt
      · exact hlt
      · exact heq.symm.trans_lt hlt
    · rcases hpair s s' hs hs' with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact heq
      · exact heq.symm
    · rw [QuartetKey.quartet_taxa]
      exact keyTaxa_key4

/-- In the regular zone, every set of four taxa of `net32On` (there is one) has the pattern
`NMSC.RegularOn`. -/
theorem net32On_regular {γ ℓ h₁ h₂ L : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hℓ : 0 < ℓ)
    (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) (hL : 0 < L)
    (hzone : γ * (1 - γ) * (1 - Real.exp (-L)) <
      γ ^ 2 * (1 - Real.exp (-h₁)) + (1 - γ) ^ 2 * (1 - Real.exp (-h₂)) + (Real.exp ℓ - 1)) :
    Regular (net32On γ ℓ h₁ h₂ L) := by
  intro k hk
  rw [keysOn_taxa4, mem_singleton] at hk
  subst hk
  exact (net32On_regularOn_iff hγ0 hγ1 hℓ hh₁ hh₂ hL).2 hzone

/-- The bound `t₀(N₃₂)` on the threshold is `1`, whatever the parameters: `N₃₂` displays one
quartet tree on its four taxa, so no ratio `(p₂ - p₃)/(p₂ + p₃)` enters `NMSC.threshold`. -/
theorem threshold_net32On (γ ℓ h₁ h₂ L : ℝ) : threshold (net32On γ ℓ h₁ h₂ L) = 1 := by
  have hother : ∀ a : Fin 3, ∃ u : Fin 3, u ≠ a ∧ u ≠ 0 := by decide
  have h : ratios (net32On γ ℓ h₁ h₂ L) = ∅ := by
    rw [ratios, image_eq_empty, filter_eq_empty_iff]
    rintro ⟨k, s, s₃⟩ hx ⟨-, -, hall⟩
    simp only [mem_product, mem_univ, and_true] at hx
    rw [keysOn_taxa4, mem_singleton] at hx
    subst hx
    obtain ⟨u, hu₃, hu0⟩ := hother s₃
    exact hu0 ((net32On_displaysQuartet γ ℓ h₁ h₂ L u).1 (hall u hu₃))
  unfold threshold
  apply le_antisymm
  · exact min'_le _ _ (mem_insert_self 1 _)
  · refine le_min' _ _ _ fun r hr => ?_
    rw [h, insert_empty, mem_singleton] at hr
    exact hr.ge

section Genes

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  [MeasurableSpace (Finset (Finset taxa4))] [MeasurableSingletonClass (Finset (Finset taxa4))]

/-- **Section 3.4: Quartet Filtering in the regular zone.** Let `0 < γ < 1` and `ℓ`, `h₁`, `h₂`,
`L` be positive, with
`γ(1 - γ)(1 - e^{-L}) < γ²(1 - e^{-h₁}) + (1 - γ)²(1 - e^{-h₂}) + (e^ℓ - 1)`
(`Brooqs.net32_regular_iff`), and let the gene trees be independent, each with the law of the NMSC
on `net32On γ ℓ h₁ h₂ L`. For every threshold `0 < t < 1` (`1 = t₀(N₃₂)`,
`NMSC.threshold_net32On`), almost surely, for all large numbers `n` of genes, Algorithm 1 applied to
the multiset `Q` of the quartet trees of the first `n` gene trees returns exactly the quartet trees
of `Q` in Q(N_r), with their multiplicities (`NMSC.nmsc_filterQuartets`). -/
theorem net32On_filterQuartets_regular {γ ℓ h₁ h₂ L : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hℓ : 0 < ℓ) (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) (hL : 0 < L)
    (hzone : γ * (1 - γ) * (1 - Real.exp (-L)) <
      γ ^ 2 * (1 - Real.exp (-h₁)) + (1 - γ) ^ 2 * (1 - Real.exp (-h₂)) + (Real.exp ℓ - 1))
    (G : ℕ → Ω → Finset (Finset taxa4)) (hind : iIndepFun G P)
    (hid : ∀ n, IdentDistrib (G n) (G 0) P P)
    (hlaw : ∀ T, P.real (G 0 ⁻¹' {T}) = (net32On γ ℓ h₁ h₂ L).geneTreeDist id T) {t : ℝ}
    (ht : 0 < t) (ht₁ : t < 1) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      filterQuartets t (geneQuartets (fun i => G i ω) n) =
        (geneQuartets (fun i => G i ω) n).filter (DisplaysQuartet (net32On γ ℓ h₁ h₂ L)) :=
  nmsc_filterQuartets (net32On_wellFormed hγ0 hγ1 hℓ hh₁ hh₂ hL) G hind hid hlaw
    (net32On_regular hγ0 hγ1 hℓ hh₁ hh₂ hL hzone) ht
    ((threshold_net32On γ ℓ h₁ h₂ L).symm ▸ ht₁)

/-- **Sections 3.3 and 3.4: the input of CAMUS in the regular zone.** Under the assumptions of
`NMSC.net32On_filterQuartets_regular`, almost surely, for all large numbers `n` of genes, the
quartet trees that Quartet Filtering returns are exactly those in Q(N_r). -/
theorem net32On_filterQuartets_support {γ ℓ h₁ h₂ L : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hℓ : 0 < ℓ) (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) (hL : 0 < L)
    (hzone : γ * (1 - γ) * (1 - Real.exp (-L)) <
      γ ^ 2 * (1 - Real.exp (-h₁)) + (1 - γ) ^ 2 * (1 - Real.exp (-h₂)) + (Real.exp ℓ - 1))
    (G : ℕ → Ω → Finset (Finset taxa4)) (hind : iIndepFun G P)
    (hid : ∀ n, IdentDistrib (G n) (G 0) P P)
    (hlaw : ∀ T, P.real (G 0 ⁻¹' {T}) = (net32On γ ℓ h₁ h₂ L).geneTreeDist id T) {t : ℝ}
    (ht : 0 < t) (ht₁ : t < 1) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ q,
      q ∈ filterQuartets t (geneQuartets (fun i => G i ω) n) ↔
        DisplaysQuartet (net32On γ ℓ h₁ h₂ L) q := by
  filter_upwards [net32On_filterQuartets_regular hγ0 hγ1 hℓ hh₁ hh₂ hL hzone G hind hid hlaw ht
      ht₁,
    eventually_mem_geneQuartets (net32On_wellFormed hγ0 hγ1 hℓ hh₁ hh₂ hL)
      (net32On_taxa γ ℓ h₁ h₂ L) G hind hid hlaw] with ω h1 h2
  filter_upwards [h1, h2] with n hn hall q
  rw [hn, Multiset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro hq
    obtain ⟨K, hKmem, hK⟩ := hq
    exact ⟨hall q (mem_quartetsOn.2 hK.1), ⟨K, hKmem, hK⟩⟩

/-- **Sections 3.3 and 3.4 in the regular zone, in the graph representation.** Under the
assumptions of `NMSC.net32On_filterQuartets_regular`, almost surely, for all large numbers `n` of
genes, the quartet trees that Quartet Filtering returns are exactly those displayed by the graph
`Realization.graph (baseTree N) (pairs N)` of `N = net32On γ ℓ h₁ h₂ L`. -/
theorem net32On_filterQuartets_support_graph {γ ℓ h₁ h₂ L : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hℓ : 0 < ℓ) (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) (hL : 0 < L)
    (hzone : γ * (1 - γ) * (1 - Real.exp (-L)) <
      γ ^ 2 * (1 - Real.exp (-h₁)) + (1 - γ) ^ 2 * (1 - Real.exp (-h₂)) + (Real.exp ℓ - 1))
    (G : ℕ → Ω → Finset (Finset taxa4)) (hind : iIndepFun G P)
    (hid : ∀ n, IdentDistrib (G n) (G 0) P P)
    (hlaw : ∀ T, P.real (G 0 ⁻¹' {T}) = (net32On γ ℓ h₁ h₂ L).geneTreeDist id T) {t : ℝ}
    (ht : 0 < t) (ht₁ : t < 1) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ q,
      q ∈ filterQuartets t (geneQuartets (fun i => G i ω) n) ↔
        (Realization.graph (baseTree (net32On γ ℓ h₁ h₂ L))
          (pairs (net32On γ ℓ h₁ h₂ L))).DisplaysQuartet q := by
  filter_upwards [net32On_filterQuartets_support hγ0 hγ1 hℓ hh₁ hh₂ hL hzone G hind hid hlaw ht
    ht₁] with ω hω
  filter_upwards [hω] with n hn q
  rw [hn q, graph_displaysQuartet_iff (net32On_wellFormed hγ0 hγ1 hℓ hh₁ hh₂ hL)
    (net32On_taxa γ ℓ h₁ h₂ L) q]

end Genes

end NMSC

end Camus
