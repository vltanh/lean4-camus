module

public import Camus.Pipelines.NMSC.Filtering

/-!
# Section 3.3: Quartet Filtering and ASTRAL on an anomalous network

Section 3.3 motivates Quartet Filtering (Algorithm 1): "The motivation for this approach is that we
do not want to include quartet trees that are not in Q(Nr). On the other hand, we do not want to
eliminate these quartet trees." It also notes that "there is no guarantee that the tree T* that
ASTRAL produces will be in T". This file shows that, for one level-1 network under the NMSC,
Algorithm 1 does both things that the paper does not want, whatever the threshold, and that the
tree of maximum quartet support score is not a displayed tree.

The network is `N₃₂` of `Brooqs.net32_anomaly` on the taxa `0, 1, 2, 3` (`NMSC.anomalyNet`): `0`
and `1` below the hybrid node of a 3-cycle, `2` on a side of the cycle and `3` outside it. Of the
three quartet trees on these taxa, it displays only `01|23` (`NMSC.anomalyNet_displaysQuartet`),
and under the NMSC `01|23` is strictly less probable than `02|13` and `03|12`, which are equally
probable (`NMSC.anomalyNet_quartetProb`). By the strong law of large numbers, for all large numbers
of genes `01|23` is the least frequent of the three, so Algorithm 1 drops it and keeps the most
frequent one, which is not in Q(N_r) (`NMSC.anomaly_filterQuartets`); and every tree of maximum
quartet support score induces a quartet tree other than `01|23`, so it is not a displayed tree of
the network (`NMSC.anomaly_astral`).

## Main results

* `NMSC.anomalyNet`, `NMSC.anomalyNet_displaysQuartet`, `NMSC.anomalyNet_quartetProb`: the network,
  its displayed quartet trees on `0, 1, 2, 3`, and their probabilities.
* `NMSC.anomalyNet_not_regularOn`: the four taxa do not have the CF pattern that Quartet Filtering
  presumes (`NMSC.RegularOn`).
* `NMSC.anomaly_filterQuartets`, `NMSC.anomaly_filterQuartets_genes`: for every threshold, almost
  surely, for all large numbers of genes, Algorithm 1 returns a quartet tree not in Q(N_r) and no
  copy of the one in Q(N_r).
* `NMSC.anomaly_astral`: almost surely, for all large numbers of genes, no tree of maximum quartet
  support score is a displayed tree of the network.
-/

@[expose] public noncomputable section

namespace Camus

namespace NMSC

open Finset Filter Topology MeasureTheory ProbabilityTheory Coalescent Algorithm1

/-- The four taxa `0, 1, 2, 3`. -/
abbrev taxa4 : Finset ℕ := {0, 1, 2, 3}

/-- The set of the four taxa `0 < 1 < 2 < 3`. -/
def key4 : QuartetKey := ⟨0, 1, 2, 3, by decide, by decide, by decide⟩

theorem keyTaxa_key4 : keyTaxa key4 ⊆ taxa4 := subset_rfl

/-- The anomalous network `N₃₂` of `Brooqs.net32_anomaly` on the taxa `0, 1, 2, 3`: the taxa
`x = 0` and `y = 1` below the hybrid node of a 3-cycle, `z = 2` on a side of the cycle and `w = 3`
outside it, with `γ = 1/2`, `ℓ = h₁ = h₂ = 1/20` and `L = 3`. -/
def anomalyNet : Brooqs.Net taxa4 :=
  Brooqs.net32 (1 / 2) (1 / 20) (1 / 20) (1 / 20) 3 ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨2, by decide⟩
    ⟨3, by decide⟩

theorem anomalyNet_wellFormed : anomalyNet.WellFormed :=
  Brooqs.net32_wellFormed (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem an_keyTaxon (i : Fin 4) :
    keyTaxon key4 keyTaxa_key4 i = ⟨![0, 1, 2, 3] i, by fin_cases i <;> decide⟩ := rfl

/-- Of the three quartet trees on `0, 1, 2, 3`, the network displays only `01|23`. -/
theorem anomalyNet_displaysQuartet (s : Fin 3) :
    DisplaysQuartet anomalyNet (key4.quartet s) ↔ s = 0 := by
  obtain ⟨h0, h1, h2⟩ := Brooqs.net32_displays (X := taxa4) (x := ⟨0, by decide⟩)
    (y := ⟨1, by decide⟩) (z := ⟨2, by decide⟩) (w := ⟨3, by decide⟩) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (1 / 2) (1 / 20) (1 / 20) (1 / 20) 3
  obtain ⟨e0, e1, e2⟩ := displaysQuartet_iff anomalyNet key4 keyTaxa_key4
  fin_cases s
  · exact ⟨fun _ => rfl, fun _ => e0.2 h0⟩
  · exact ⟨fun h => absurd (e1.1 h) h1, fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd (e2.1 h) h2, fun h => absurd h (by decide)⟩

/-- The probabilities of the three quartet trees on `0, 1, 2, 3` under the NMSC on the network:
the one it displays, `01|23`, is strictly the least probable, and the two others are equally
probable. -/
theorem anomalyNet_quartetProb :
    quartetProb anomalyNet (key4.quartet 0) < quartetProb anomalyNet (key4.quartet 1) ∧
      quartetProb anomalyNet (key4.quartet 1) = quartetProb anomalyNet (key4.quartet 2) := by
  obtain ⟨p0, p1, p2⟩ := quartetProb_eq_quartetCF anomalyNet anomalyNet_wellFormed.2 key4
    keyTaxa_key4
  rw [p0, p1, p2]
  exact Brooqs.net32_anomaly (X := taxa4) (x := ⟨0, by decide⟩) (y := ⟨1, by decide⟩)
    (z := ⟨2, by decide⟩) (w := ⟨3, by decide⟩) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

/-- The only set of four taxa of `0, 1, 2, 3`. -/
theorem keysOn_taxa4 : keysOn taxa4 = {key4} := by
  ext k
  rw [mem_keysOn, mem_singleton]
  constructor
  · intro h
    obtain ⟨a, b, c, d, hab, hbc, hcd⟩ := k
    simp only [insert_subset_iff, singleton_subset_iff, mem_insert, mem_singleton] at h
    obtain ⟨ha, hb, hc, hd⟩ := h
    have hd3 : d ≤ 3 := by rcases hd with rfl | rfl | rfl | rfl <;> omega
    have ha0 : a = 0 := by omega
    have hb1 : b = 1 := by omega
    have hc2 : c = 2 := by omega
    have hd3' : d = 3 := by rcases ha with rfl | rfl | rfl | rfl <;> omega
    subst ha0 hb1 hc2 hd3'
    rfl
  · rintro rfl
    exact subset_rfl

/-- On the taxa `0, 1, 2, 3`, the quartet support score of a well-labelled tree is the number of
copies of the one quartet tree it induces. -/
private theorem an_quartetSupport (Q : Multiset Quartet) {T : PhyloTree} (hT : T.WellLabelled)
    (hTt : T.taxa = taxa4) : quartetSupport Q T = Q.count (key4.quartet (T.splitOf key4)) := by
  rw [quartetSupport_eq_sum_keys Q T hT, hTt, keysOn_taxa4, sum_singleton]

/-- The tree `((0, 2), (1, 3))`, which induces `02|13`. -/
private def an_tree : PhyloTree := .fork (.fork (.leaf 0) (.leaf 2)) (.fork (.leaf 1) (.leaf 3))

private theorem an_tree_facts : an_tree.WellLabelled ∧ an_tree.taxa = taxa4 ∧
    (key4.quartet 1).induced an_tree = true := by
  refine ⟨by decide, by decide, by decide⟩

/-- The four taxa `0, 1, 2, 3` of the network do not have the CF pattern that Quartet Filtering
presumes (`RegularOn`): the quartet tree it displays is not the most probable. -/
theorem anomalyNet_not_regularOn : ¬ RegularOn anomalyNet key4 := by
  obtain ⟨h01, -⟩ := anomalyNet_quartetProb
  rintro (⟨s₁, h₁, -, hmax, -, -⟩ | ⟨s₃, h₃, hdisp, -⟩)
  · obtain rfl := (anomalyNet_displaysQuartet s₁).1 h₁
    exact absurd (hmax 1 (by decide)) (not_lt.2 h01.le)
  · -- two quartet trees would be displayed, but only `01|23` is
    have h1 := (anomalyNet_displaysQuartet 1).1
    have h2 := (anomalyNet_displaysQuartet 2).1
    fin_cases s₃
    · exact absurd (h1 (hdisp 1 (by decide))) (by decide)
    · exact absurd (h2 (hdisp 2 (by decide))) (by decide)
    · exact absurd (h1 (hdisp 1 (by decide))) (by decide)

section Genes

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  [MeasurableSpace (Finset (Finset taxa4))] [MeasurableSingletonClass (Finset (Finset taxa4))]

/-- For independent gene trees with the law of the NMSC on the network, almost surely, for all large
numbers `n` of genes, the quartet tree `01|23` has strictly fewer copies than each of the two others
among the quartet trees of the first `n` gene trees, and the quartet tree `02|13` has a copy. -/
private theorem an_eventually (G : ℕ → Ω → Finset (Finset taxa4)) (hind : iIndepFun G P)
    (hid : ∀ n, IdentDistrib (G n) (G 0) P P)
    (hlaw : ∀ T, P.real (G 0 ⁻¹' {T}) = anomalyNet.geneTreeDist id T) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      (∀ s, s ≠ 0 → (geneQuartets (fun i => G i ω) n).count (key4.quartet 0) <
        (geneQuartets (fun i => G i ω) n).count (key4.quartet s)) ∧
      0 < (geneQuartets (fun i => G i ω) n).count (key4.quartet 1) := by
  set p : Fin 3 → ℝ := fun s => quartetProb anomalyNet (key4.quartet s) with hpdef
  have hp : ∀ s, P.real {ω | Induces (G 0 ω) (key4.quartet s)} = p s := fun s =>
    measureReal_induces anomalyNet (G 0) (hid 0).aemeasurable_fst hlaw _
  obtain ⟨h01, h12⟩ := anomalyNet_quartetProb
  have hlt : ∀ s, s ≠ 0 → p 0 < p s := by
    intro s hs
    fin_cases s
    · exact absurd rfl hs
    · exact h01
    · exact lt_of_lt_of_eq h01 h12
  have hp1 : 0 < p 1 := by
    have : 0 ≤ p 0 := by
      rw [← hp]
      exact measureReal_nonneg
    linarith [hlt 1 (by decide)]
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

/-- **Section 3.3: Quartet Filtering fails under the NMSC.** Let the gene trees be independent,
each with the law of the NMSC on the network `N₃₂` of `anomalyNet`, on the taxa `0, 1, 2, 3`. For
every threshold `t`, almost surely, for all large numbers `n` of genes, Algorithm 1 applied to the
quartet trees of the first `n` gene trees returns no copy of `01|23`, the only quartet tree on these
taxa in Q(N_r), and returns a quartet tree that is not in Q(N_r). Section 3.3 wants neither: "we do
not want to include quartet trees that are not in Q(Nr). On the other hand, we do not want to
eliminate these quartet trees." The quartet tree of Q(N_r) is the least frequent, so Algorithm 1
never keeps it, and always keeps the most frequent one. -/
theorem anomaly_filterQuartets (G : ℕ → Ω → Finset (Finset taxa4)) (hind : iIndepFun G P)
    (hid : ∀ n, IdentDistrib (G n) (G 0) P P)
    (hlaw : ∀ T, P.real (G 0 ⁻¹' {T}) = anomalyNet.geneTreeDist id T) (t : ℝ) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      (filterQuartets t (geneQuartets (fun i => G i ω) n)).count (key4.quartet 0) = 0 ∧
      ∃ q ∈ filterQuartets t (geneQuartets (fun i => G i ω) n),
        ¬ DisplaysQuartet anomalyNet q := by
  filter_upwards [an_eventually G hind hid hlaw] with ω hω
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
      fun h => hs₁ ((anomalyNet_displaysQuartet s₁).1 h)⟩

/-- Section 3.4, for gene trees that exist: the hypotheses of `anomaly_filterQuartets` hold for the
coordinates of `anomalyNet.genes`, the product law of independent gene trees under the NMSC
(`Brooqs.Net.genes`). -/
theorem anomaly_filterQuartets_genes (t : ℝ) :
    ∀ᵐ ω ∂(anomalyNet.genes anomalyNet_wellFormed), ∀ᶠ n in atTop,
      (filterQuartets t (geneQuartets (fun i => ω i) n)).count (key4.quartet 0) = 0 ∧
      ∃ q ∈ filterQuartets t (geneQuartets (fun i => ω i) n),
        ¬ DisplaysQuartet anomalyNet q :=
  anomaly_filterQuartets (fun n (ω : ℕ → Finset (Finset taxa4)) => ω n)
    (anomalyNet.genes_iIndepFun anomalyNet_wellFormed)
    (anomalyNet.genes_identDistrib anomalyNet_wellFormed)
    (anomalyNet.genes_law anomalyNet_wellFormed) t

/-- **Section 3.3: the tree of ASTRAL need not be displayed.** "There is no guarantee that the tree
T* that ASTRAL produces will be in T." Let the gene trees be independent, each with the law of the
NMSC on the network `N₃₂` of `anomalyNet`. Almost surely, for all large numbers `n` of genes, no
tree of maximum quartet support score for the quartet trees of the first `n` gene trees (ASTRAL's
exact optimum, among the well-labelled trees on `0, 1, 2, 3`) is a displayed tree of `N₃₂`: every
displayed tree induces `01|23`, the least frequent quartet tree. -/
theorem anomaly_astral (G : ℕ → Ω → Finset (Finset taxa4)) (hind : iIndepFun G P)
    (hid : ∀ n, IdentDistrib (G n) (G 0) P P)
    (hlaw : ∀ T, P.real (G 0 ⁻¹' {T}) = anomalyNet.geneTreeDist id T) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ T : PhyloTree, T.WellLabelled → T.taxa = taxa4 →
      (∀ T' : PhyloTree, T'.WellLabelled → T'.taxa = taxa4 →
        quartetSupport (geneQuartets (fun i => G i ω) n) T' ≤
          quartetSupport (geneQuartets (fun i => G i ω) n) T) →
      ¬ DisplaysTree anomalyNet T := by
  filter_upwards [an_eventually G hind hid hlaw] with ω hω
  filter_upwards [hω] with n hn T hT hTt hopt
  obtain ⟨hmin, -⟩ := hn
  set Q := geneQuartets (fun i => G i ω) n
  obtain ⟨h1, h2, h3⟩ := an_tree_facts
  have hk : ({key4.a, key4.b, key4.c, key4.d} : Finset ℕ) ⊆ T.taxa := by
    rw [hTt]
    exact subset_rfl
  have hk₁ : ({key4.a, key4.b, key4.c, key4.d} : Finset ℕ) ⊆ an_tree.taxa := by
    rw [h2]
    exact subset_rfl
  -- the tree `((0, 2), (1, 3))` scores the copies of `02|13`
  have hs₁ : an_tree.splitOf key4 = 1 :=
    ((PhyloTree.induced_iff_splitOf an_tree h1 key4 hk₁ 1).1 h3).symm
  have hle := hopt an_tree h1 h2
  rw [an_quartetSupport Q h1 h2, hs₁, an_quartetSupport Q hT hTt] at hle
  -- so `T` does not induce `01|23`
  have hne : T.splitOf key4 ≠ 0 := by
    intro h0
    rw [h0] at hle
    exact absurd hle (not_le.2 (hmin 1 (by decide)))
  -- but every displayed tree of the network does
  rintro ⟨K, hK, hiff⟩
  have hT' : (key4.quartet (T.splitOf key4)).induced T = true :=
    (PhyloTree.induced_iff_splitOf T hT key4 hk _).2 rfl
  exact hne ((anomalyNet_displaysQuartet _).1 ⟨K, hK, (hiff _).2 hT'⟩)

end Genes

end NMSC

end Camus
