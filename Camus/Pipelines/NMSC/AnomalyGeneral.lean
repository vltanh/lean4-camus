module

public import Camus.Pipelines.NMSC.AnomalyRegion
public import Camus.External.NMSC.AnomalyGeneral

/-!
# Section 3.3: Quartet Filtering on four taxa in the anomalous configuration, in any network

Section 3.3 motivates Quartet Filtering (Algorithm 1): "The motivation for this approach is that we
do not want to include quartet trees that are not in Q(Nr). On the other hand, we do not want to
eliminate these quartet trees." `Camus/Pipelines/NMSC/AnomalyRegion.lean` shows that on the 3-cycle
above two taxa `N₃₂` the filter is defeated exactly in the anomaly zone. This file extends the
result to four taxa in the anomalous configuration in an arbitrary metric network `N` with distinct
leaf labels on the taxa `L`: a cycle `C` of `N` with two of the four taxa below its hybrid node
and the two others in two other components. By `Brooqs.Net.Cycle.splitCF_of_anomalous`, `N`
displays one quartet tree on the four taxa, the one that groups the two taxa below the hybrid node
(`NMSC.pairIndex`), and the probabilities of the three quartet trees are those of `N₃₂` with the
probability `p` that the lineages of the two taxa reach the hybrid node apart in place of `e^{-ℓ}`,
and with the positive lengths `h₁`, `h₂`, `L` added up along the sides of `C`
(`Brooqs.Net.Cycle.anomalyH₁`, `Brooqs.Net.Cycle.anomalyH₂`, `Brooqs.Net.Cycle.anomalyL`;
`NMSC.anomalous_quartetProb`). With
`D = γ(1 - γ)(1 - e^{-L}) - γ²(1 - e^{-h₁}) - (1 - γ)²(1 - e^{-h₂})`
(`Brooqs.Net.Cycle.anomalyExcess`; `NMSC.anomalous_filterQuartets`):

* if `1 - p < p D`, for every threshold, almost surely, for all large numbers of genes, Algorithm 1
  returns no copy of the quartet tree of Q(N_r) on the four taxa and returns a quartet tree on them
  that is not in Q(N_r);
* if `p D < 1 - p`, for every threshold `0 < t < t₀(N)`, almost surely, for all large numbers of
  genes, Algorithm 1 returns on the four taxa exactly the copies of the quartet tree of Q(N_r);
* if `p D = 1 - p`, the three quartet trees have probability `1/3`, and for every threshold `t > 0`,
  almost surely, for all large numbers of genes, Algorithm 1 returns on the four taxa the copies of
  a single quartet tree (`NMSC.anomalous_filterQuartets_boundary`, from
  `NMSC.filterQuartets_block_of_equal`); it neither almost surely ends up keeping the one of
  Q(N_r) nor almost surely ends up dropping it (`Camus/Pipelines/NMSC/AnomalyBoundary.lean`).

## Main results

* `NMSC.filterQuartets_block_of_least`: on four taxa where the network displays one quartet tree
  and it is strictly the least probable, Algorithm 1 drops it and keeps another one, for every
  threshold (the argument of `NMSC.anomaly_filterQuartets`, for any network).
* `NMSC.filterQuartets_block_of_most`: on four taxa where the network displays one quartet tree,
  strictly the most probable, and the two others are equally probable, Algorithm 1 keeps exactly
  its copies.
* `NMSC.filterQuartets_block_of_equal`: on four taxa whose three quartet trees are equally probable,
  Algorithm 1 keeps the copies of a single quartet tree.
* `NMSC.pairIndex`, `NMSC.blockSample`, `NMSC.anomalous_quartetProb`: the displayed quartet tree
  and the probabilities of the three quartet trees in the anomalous configuration.
* `NMSC.anomalous_filterQuartets`, `NMSC.anomalous_filterQuartets_boundary`: Quartet Filtering in
  the three zones.
-/

@[expose] public noncomputable section

namespace Camus

namespace NMSC

open Finset Filter Topology MeasureTheory ProbabilityTheory Coalescent Algorithm1

variable {L : Finset ℕ}

/-! ### Algorithm 1 on four taxa, from the probabilities of their quartet trees -/

section Genes

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  [MeasurableSpace (Finset (Finset L))] [MeasurableSingletonClass (Finset (Finset L))]

/-- By the strong law of large numbers, the relative frequencies of the three quartet trees on the
four taxa `k` converge almost surely to their probabilities. -/
theorem ae_tendsto_block {N : Brooqs.Net L} (k : QuartetKey) (G : ℕ → Ω → Finset (Finset L))
    (hind : iIndepFun G P) (hid : ∀ n, IdentDistrib (G n) (G 0) P P)
    (hlaw : ∀ T, P.real (G 0 ⁻¹' {T}) = N.geneTreeDist id T) :
    ∀ᵐ ω ∂P, ∀ u, Tendsto (fun n : ℕ =>
      ((geneQuartets (fun i => G i ω) n).count (k.quartet u) : ℝ) / n) atTop
        (𝓝 (quartetProb N (k.quartet u))) := by
  rw [ae_all_iff]
  intro u
  rw [← measureReal_induces N (G 0) (hid 0).aemeasurable_fst hlaw (k.quartet u)]
  exact ae_tendsto_frequency G hind hid _

/-- **Algorithm 1 drops the displayed quartet tree when it is the least probable.** Let the gene
trees be independent, each with the law of the NMSC on the network `N` on the taxa `L`, and let `N`
display exactly one of the three quartet trees on the four taxa `k`, `k.quartet d`, strictly the
least probable. For every threshold `t`, almost surely, for all large numbers `n` of genes,
Algorithm 1 applied to the quartet trees of the first `n` gene trees returns no copy of
`k.quartet d`, the only quartet tree on these taxa in Q(N_r), and returns a quartet tree on these
taxa that is not in Q(N_r). The argument of `NMSC.anomaly_filterQuartets`. -/
theorem filterQuartets_block_of_least {N : Brooqs.Net L} {k : QuartetKey} {d : Fin 3}
    (hdisp : ∀ u, DisplaysQuartet N (k.quartet u) ↔ u = d)
    (hlt : ∀ u, u ≠ d → quartetProb N (k.quartet d) < quartetProb N (k.quartet u))
    (G : ℕ → Ω → Finset (Finset L)) (hind : iIndepFun G P)
    (hid : ∀ n, IdentDistrib (G n) (G 0) P P)
    (hlaw : ∀ T, P.real (G 0 ⁻¹' {T}) = N.geneTreeDist id T) (t : ℝ) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      (filterQuartets t (geneQuartets (fun i => G i ω) n)).count (k.quartet d) = 0 ∧
      ∃ q ∈ filterQuartets t (geneQuartets (fun i => G i ω) n), q.key = k ∧
        ¬ DisplaysQuartet N q := by
  filter_upwards [ae_tendsto_block k G hind hid hlaw] with ω hω
  -- eventually the displayed quartet tree has strictly the fewest copies
  have hsep : ∀ u, ∀ᶠ n in atTop, u ≠ d →
      ((geneQuartets (fun i => G i ω) n).count (k.quartet d) : ℝ) / n <
        ((geneQuartets (fun i => G i ω) n).count (k.quartet u) : ℝ) / n := by
    intro u
    by_cases hu : u = d
    · exact Eventually.of_forall fun _ h => absurd hu h
    · filter_upwards [((hω u).sub (hω d)).eventually_const_lt (sub_pos.2 (hlt u hu))]
        with n hn _
      linarith
  filter_upwards [eventually_all.2 hsep, eventually_gt_atTop 0] with n hn hn0
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn0
  have hmin : ∀ u, u ≠ d → (geneQuartets (fun i => G i ω) n).count (k.quartet d) <
      (geneQuartets (fun i => G i ω) n).count (k.quartet u) := fun u hu => by
    exact_mod_cast (div_lt_div_iff_of_pos_right hn').1 (hn u hu)
  set Q := geneQuartets (fun i => G i ω) n
  set f := frequencies (Q.map quartetEquiv) k
  have hf : ∀ u, f u = Q.count (k.quartet u) := fun u => frequencies_map Q k u
  -- the displayed quartet tree is `q₃`
  have h3 : (rank f).2.2 = d := rank_snd_snd_eq_of_lt fun u hu => by
    rw [hf, hf]
    exact hmin u hu
  refine ⟨?_, ?_⟩
  · rw [count_filterQuartets]
    have := filterBlock_third_count t (Q.map quartetEquiv) k
    rwa [h3] at this
  · -- the most frequent quartet tree `q₁` is kept, and it is not displayed
    set s₁ := (rank f).1
    have hs₁ : s₁ ≠ d := h3 ▸ (rank_distinct f).2.1
    have hcount : 0 < (filterQuartets t Q).count (k.quartet s₁) := by
      rw [count_filterQuartets]
      have h1 : (filterBlock t (Q.map quartetEquiv) k).count (k, s₁) = f s₁ :=
        filterBlock_top_count t (Q.map quartetEquiv) k
      have h2 : 0 < f s₁ := by
        rw [hf]
        exact lt_of_le_of_lt (Nat.zero_le _) (hmin s₁ hs₁)
      change 0 < (filterBlock t (Q.map quartetEquiv) k).count (k, s₁)
      omega
    exact ⟨k.quartet s₁, Multiset.count_pos.1 hcount, rfl,
      fun h => hs₁ ((hdisp s₁).1 h)⟩

/-- **Algorithm 1 keeps the displayed quartet tree when it is the most probable.** Let the gene
trees be independent, each with the law of the NMSC on the metric network `N` with distinct leaf
labels on the taxa `L`, and let `N` display exactly one of the three quartet trees on the four taxa
`k` of `L`, strictly the most probable, the two others being equally probable. For every threshold
`0 < t < t₀(N)`, almost surely, for all large numbers `n` of genes, Algorithm 1 returns on these
taxa exactly the copies of the quartet tree in Q(N_r) (`NMSC.nmsc_filterBlock`). -/
theorem filterQuartets_block_of_most {N : Brooqs.Net L} (hN : N.WellFormed)
    (htaxa : ∀ x : L, x ∈ N.taxa) {k : QuartetKey} (hk : k ∈ keysOn L) {d : Fin 3}
    (hdisp : ∀ u, DisplaysQuartet N (k.quartet u) ↔ u = d)
    (hgt : ∀ u, u ≠ d → quartetProb N (k.quartet u) < quartetProb N (k.quartet d))
    (heq : ∀ u u', u ≠ d → u' ≠ d → quartetProb N (k.quartet u) = quartetProb N (k.quartet u'))
    (G : ℕ → Ω → Finset (Finset L)) (hind : iIndepFun G P)
    (hid : ∀ n, IdentDistrib (G n) (G 0) P P)
    (hlaw : ∀ T, P.real (G 0 ⁻¹' {T}) = N.geneTreeDist id T) {t : ℝ} (ht : 0 < t)
    (ht₀ : t < threshold N) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ u,
      (filterQuartets t (geneQuartets (fun i => G i ω) n)).count (k.quartet u) =
        if DisplaysQuartet N (k.quartet u) then
          (geneQuartets (fun i => G i ω) n).count (k.quartet u) else 0 := by
  have hreg : RegularOn N k := Or.inl ⟨d, (hdisp d).2 rfl, fun u hu h => hu ((hdisp u).1 h),
    hgt, heq, fun u => quartetProb_pos hN htaxa (by
      rw [QuartetKey.quartet_taxa]
      exact mem_keysOn.1 hk)⟩
  filter_upwards [nmsc_filterBlock hN G hind hid hlaw ht ht₀ hk hreg] with ω hω
  filter_upwards [hω] with n hn u
  rw [count_filterQuartets]
  exact hn u

/-- **Algorithm 1 when the three quartet trees are equally probable.** Let the gene trees be
independent, each with the law of the NMSC on the network `N` on the taxa `L`, and let the three
quartet trees on the four taxa `k` have the same positive probability. For every threshold `t > 0`,
almost surely, for all large numbers `n` of genes, Algorithm 1 returns on these taxa the copies of a
single quartet tree, the most frequent: the test `f₂ - f₃ > t (f₂ + f₃)` fails, since `f₂ - f₃`
grows more slowly than `n` while `f₂ + f₃` grows like `n`. -/
theorem filterQuartets_block_of_equal {N : Brooqs.Net L} {k : QuartetKey}
    (hpos : 0 < quartetProb N (k.quartet 0))
    (heq : ∀ u, quartetProb N (k.quartet u) = quartetProb N (k.quartet 0))
    (G : ℕ → Ω → Finset (Finset L)) (hind : iIndepFun G P)
    (hid : ∀ n, IdentDistrib (G n) (G 0) P P)
    (hlaw : ∀ T, P.real (G 0 ⁻¹' {T}) = N.geneTreeDist id T) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∃ u, ∀ u',
      (filterQuartets t (geneQuartets (fun i => G i ω) n)).count (k.quartet u') =
        if u' = u then (geneQuartets (fun i => G i ω) n).count (k.quartet u) else 0 := by
  filter_upwards [ae_tendsto_block k G hind hid hlaw] with ω hω
  set p := quartetProb N (k.quartet 0)
  -- the test fails eventually for every two quartet trees
  have hdrop : ∀ u u', ∀ᶠ n in atTop,
      |((geneQuartets (fun i => G i ω) n).count (k.quartet u) : ℝ) / n -
        ((geneQuartets (fun i => G i ω) n).count (k.quartet u') : ℝ) / n| <
      t * (((geneQuartets (fun i => G i ω) n).count (k.quartet u) : ℝ) / n +
        ((geneQuartets (fun i => G i ω) n).count (k.quartet u') : ℝ) / n) := by
    intro u u'
    have hlim := (((hω u).add (hω u')).const_mul t).sub ((hω u).sub (hω u')).abs
    have hlim_pos : 0 < t * (quartetProb N (k.quartet u) + quartetProb N (k.quartet u')) -
        |quartetProb N (k.quartet u) - quartetProb N (k.quartet u')| := by
      rw [heq u, heq u', sub_self, abs_zero, sub_zero]
      positivity
    filter_upwards [hlim.eventually_const_lt hlim_pos] with n hn
    linarith
  filter_upwards [eventually_all.2 fun u => eventually_all.2 (hdrop u), eventually_gt_atTop 0]
    with n hn hn0
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn0
  set Q := geneQuartets (fun i => G i ω) n
  obtain ⟨f, hfdef⟩ : ∃ f, frequencies (Q.map quartetEquiv) k = f := ⟨_, rfl⟩
  have hf : ∀ u, f u = Q.count (k.quartet u) := fun u => hfdef ▸ frequencies_map Q k u
  have hnot : ¬ retainSecond t (f (rank f).2.1) (f (rank f).2.2) := by
    intro hret
    unfold retainSecond at hret
    have hgap := hn (rank f).2.1 (rank f).2.2
    rw [← hf, ← hf] at hgap
    have hdiv : t * ((f (rank f).2.1 : ℝ) / n + (f (rank f).2.2 : ℝ) / n) <
        (f (rank f).2.1 : ℝ) / n - (f (rank f).2.2 : ℝ) / n := by
      rw [← add_div, ← sub_div, ← mul_div_assoc]
      exact (div_lt_div_iff_of_pos_right hn').2 hret
    linarith [le_abs_self ((f (rank f).2.1 : ℝ) / n - (f (rank f).2.2 : ℝ) / n)]
  have hfb : filterBlock t (Q.map quartetEquiv) k =
      Multiset.replicate (f (rank f).1) (k, (rank f).1) := by
    simp only [filterBlock, hfdef]
    split_ifs with h
    · rw [hfdef] at h
      exact absurd h hnot
    · rw [add_zero]
  refine ⟨(rank f).1, fun u' => ?_⟩
  rw [count_filterQuartets]
  change (filterBlock t (Q.map quartetEquiv) k).count (k, u') = _
  rw [hfb, Multiset.count_replicate]
  by_cases hu : u' = (rank f).1
  · subst hu
    simp [hf]
  · have hne : (k, (rank f).1) ≠ (k, u') := fun h => hu (Prod.ext_iff.1 h).2.symm
    simp [hne, hu]

end Genes

/-! ### Four taxa in the anomalous configuration -/

/-- The index of the quartet tree on four taxa that groups the taxa `i` and `j`: `ab|cd` (`0`) for
`{i, j} = {0, 1}` or `{2, 3}`, `ac|bd` (`1`) for `{0, 2}` or `{1, 3}`, and `ad|bc` (`2`)
otherwise. -/
def pairIndex (i j : Fin 4) : Fin 3 :=
  if ({i, j} : Finset (Fin 4)) = {0, 1} ∨ ({i, j} : Finset (Fin 4)) = {2, 3} then 0
  else if ({i, j} : Finset (Fin 4)) = {0, 2} ∨ ({i, j} : Finset (Fin 4)) = {1, 3} then 1 else 2

private theorem pi_pair : ∀ i j : Fin 4, i ≠ j → ∀ u : Fin 3,
    (Brooqs.splitOf3 u = {i, j} ∨ Brooqs.splitOf3 u = {i, j}ᶜ) ↔ u = pairIndex i j := by
  decide

private theorem pi_third (d u : Fin 3) (hu : u ≠ d) : ∃ u' : Fin 3, u' ≠ d ∧ u' ≠ u ∧
    ∀ f : Fin 3 → ℝ, f 0 + f 1 + f 2 = f d + f u + f u' := by
  obtain ⟨u', h1, h2, h3⟩ : ∃ u' : Fin 3, u' ≠ d ∧ u' ≠ u ∧
      ({d, u, u'} : Finset (Fin 3)) = univ := by
    revert d u
    decide
  refine ⟨u', h1, h2, fun f => ?_⟩
  rw [← Fin.sum_univ_three, ← h3, sum_insert (by simp [hu.symm, h1.symm]),
    sum_insert (by simp [h2.symm]), sum_singleton]
  ring

private theorem pi_card : ∀ u : Fin 3, #(Brooqs.splitOf3 u) = 2 := by decide

/-- The four taxa of `k` listed as `t i, t j, t a, t b`, where `t = keyTaxon k hk` lists them in
increasing order: the two below the hybrid node of the cycle first. -/
def blockSample (k : QuartetKey) (hk : keyTaxa k ⊆ L) (i j a b : Fin 4) : Fin 4 → L :=
  ![keyTaxon k hk i, keyTaxon k hk j, keyTaxon k hk a, keyTaxon k hk b]

/-- **The quartet trees on four taxa in the anomalous configuration.** Let `N` be a metric network
with distinct leaf labels on the taxa `L`, `k` four taxa of `L` (`t = keyTaxon k hk` lists them in
increasing order), and `C` a cycle of `N` with exactly `t i` and `t j` below its hybrid node, at
least three of the four taxa below its top node and at most one in each network hanging from its
sides (`Brooqs.Net.Anomalous`); `a` and `b` are the two other labels. Then `N` displays exactly one
of the three quartet trees on `k`, the one of index `pairIndex i j`, which groups `t i` and `t j`;
and, with `p` the probability that the lineages of `t i` and `t j` reach the hybrid node apart and
`γ` the inheritance probability of `C`, and the positive lengths `h₁`, `h₂`, `L₀` added up along the
sides of `C` (`Brooqs.Net.Cycle.anomalyH₁`, `Brooqs.Net.Cycle.anomalyH₂`,
`Brooqs.Net.Cycle.anomalyL`, for the taxa listed by `NMSC.blockSample`), the displayed quartet tree
has probability
`1 - p + p (γ²(1 - 2/3 e^{-h₁}) + (1 - γ)²(1 - 2/3 e^{-h₂}) + 2γ(1 - γ) e^{-L₀}/3)` and each of the
two others `p (γ² e^{-h₁}/3 + (1 - γ)² e^{-h₂}/3 + γ(1 - γ)(1 - e^{-L₀}/3))`
(`Brooqs.Net.Cycle.splitCF_of_anomalous`). -/
theorem anomalous_quartetProb {N : Brooqs.Net L} (hN : N.WellFormed)
    (htaxa : ∀ x : L, x ∈ N.taxa) {k : QuartetKey} (hk : keyTaxa k ⊆ L) (C : N.Cycle)
    {i j a b : Fin 4} (hinj : Function.Injective ![i, j, a, b])
    (hbelow : C.below.lin (keyTaxon k hk) = {i, j}) (h3 : 3 ≤ #(C.top.lin (keyTaxon k hk)))
    (h1 : ∀ n ∈ C.side₁.nodes ++ C.side₂.nodes, #(n.2.2.lin (keyTaxon k hk)) ≤ 1) :
    (∀ u, DisplaysQuartet N (k.quartet u) ↔ u = pairIndex i j) ∧
    0 < C.anomalyH₁ (blockSample k hk i j a b) ∧ 0 < C.anomalyH₂ (blockSample k hk i j a b) ∧
      0 < C.anomalyL (blockSample k hk i j a b) ∧
      quartetProb N (k.quartet (pairIndex i j)) = 1 - C.apartProb (blockSample k hk i j a b) +
        C.apartProb (blockSample k hk i j a b) *
          (C.γ ^ 2 * (1 - 2 / 3 * Real.exp (-C.anomalyH₁ (blockSample k hk i j a b))) +
            (1 - C.γ) ^ 2 * (1 - 2 / 3 * Real.exp (-C.anomalyH₂ (blockSample k hk i j a b))) +
              2 * C.γ * (1 - C.γ) * (Real.exp (-C.anomalyL (blockSample k hk i j a b)) / 3)) ∧
      ∀ u, u ≠ pairIndex i j → quartetProb N (k.quartet u) =
        C.apartProb (blockSample k hk i j a b) *
          (C.γ ^ 2 * (Real.exp (-C.anomalyH₁ (blockSample k hk i j a b)) / 3) +
            (1 - C.γ) ^ 2 * (Real.exp (-C.anomalyH₂ (blockSample k hk i j a b)) / 3) +
              C.γ * (1 - C.γ) * (1 - Real.exp (-C.anomalyL (blockSample k hk i j a b)) / 3)) := by
  unfold blockSample
  set s : Fin 4 → L := ⇑(keyTaxon k hk) with hsdef
  have hs : Function.Injective s := (keyTaxon k hk).injective
  have hsN : ∀ l, s l ∈ N.taxa := fun l => htaxa _
  have hij : i ≠ j := fun h => absurd (hinj (a₁ := 0) (a₂ := 1) h) (by decide)
  have hpair := pi_pair i j hij
  -- the probabilities of the quartet trees are split CFs
  have hprob : ∀ u, quartetProb N (k.quartet u) = N.splitCF s (Brooqs.splitOf3 u) := by
    obtain ⟨p0, p1, p2⟩ := quartetProb_eq_quartetCF N hN.2 k hk
    intro u
    have hu3 : u = 0 ∨ u = 1 ∨ u = 2 := by
      revert u
      decide
    rcases hu3 with rfl | rfl | rfl
    · rw [p0]
      exact N.quartetCF_eq_splitCF_of s (i := 0) (j := 1) (k := 2) (l := 3) (by decide)
    · rw [p1]
      exact N.quartetCF_eq_splitCF_of s (i := 0) (j := 2) (k := 1) (l := 3) (by decide)
    · rw [p2]
      exact N.quartetCF_eq_splitCF_of s (i := 0) (j := 3) (k := 1) (l := 2) (by decide)
  -- the displayed quartet trees are the displayed splits
  have hB : C.below ∈ N.subnets := Brooqs.Net.mem_subnets_trans C.mem (by
    simp [Brooqs.Net.subnets, Brooqs.Net.self_mem_subnets])
  have hd3 : ∀ u, DisplaysQuartet N (k.quartet u) ↔ N.disp3 (s 0) (s 1) (s 2) (s 3) u := by
    obtain ⟨d0, d1, d2⟩ := displaysQuartet_iff N k hk
    intro u
    fin_cases u
    · exact d0
    · exact d1
    · exact d2
  have hdisp : ∀ u, DisplaysQuartet N (k.quartet u) ↔ u = pairIndex i j := by
    intro u
    rw [hd3, Brooqs.Net.disp3_iff_split, Brooqs.Net.displaysSplit_iff_of_subnet hN.2 hB
      (card_pair hij) hbelow (pi_card u), hpair u]
  refine ⟨hdisp, ?_⟩
  obtain ⟨p1, p2, p3, e0, -, -⟩ := C.splitCF_of_anomalous hN hs hsN hinj hbelow h3 h1
  -- the displayed quartet tree
  have hd : quartetProb N (k.quartet (pairIndex i j)) = N.splitCF s {i, j} := by
    rw [hprob]
    rcases (hpair (pairIndex i j)).2 rfl with h | h
    · rw [h]
    · rw [h, Brooqs.Net.splitCF_compl]
  -- the two others are equally probable, and the three add up to `1`
  have hweak := Brooqs.Net.weakPattern hN hs hsN
  have heq : ∀ u u', u ≠ pairIndex i j → u' ≠ pairIndex i j →
      quartetProb N (k.quartet u) = quartetProb N (k.quartet u') := by
    rcases hweak with ⟨s₁, h₁', -, hsame, -⟩ | ⟨s₃, -, hdd, -⟩
    · have hs₁ : s₁ = pairIndex i j := (hdisp s₁).1 ((hd3 s₁).2 h₁')
      intro u u' hu hu'
      rw [hprob, hprob, ← Brooqs.Net.cf3_eq_splitCF, ← Brooqs.Net.cf3_eq_splitCF]
      exact hsame u u' (hs₁ ▸ hu) (hs₁ ▸ hu')
    · -- two displayed quartet trees: impossible
      exfalso
      obtain ⟨u, hu3, hu⟩ : ∃ u : Fin 3, u ≠ s₃ ∧ u ≠ pairIndex i j := by
        clear hdd
        revert s₃
        generalize pairIndex i j = d
        intro s₃
        fin_cases s₃ <;> fin_cases d <;> decide
      exact hu ((hdisp u).1 ((hd3 u).2 (hdd u hu3)))
  have hsum : quartetProb N (k.quartet 0) + quartetProb N (k.quartet 1) +
      quartetProb N (k.quartet 2) = 1 := by
    rw [hprob, hprob, hprob]
    exact Brooqs.Net.splitCF_sum hN.2 hsN
  refine ⟨p1, p2, p3, by rw [hd, e0], fun u hu => ?_⟩
  obtain ⟨u', hu'd, hu'u, hf⟩ := pi_third (pairIndex i j) u hu
  have h3' : quartetProb N (k.quartet 0) + quartetProb N (k.quartet 1) +
      quartetProb N (k.quartet 2) = quartetProb N (k.quartet (pairIndex i j)) +
        quartetProb N (k.quartet u) + quartetProb N (k.quartet u') :=
    hf (fun v => quartetProb N (k.quartet v))
  rw [hsum, heq u' u hu'd hu, hd, e0] at h3'
  linarith

section Genes

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  [MeasurableSpace (Finset (Finset L))] [MeasurableSingletonClass (Finset (Finset L))]

/-- **Section 3.3: Quartet Filtering on four taxa in the anomalous configuration.** Under the
assumptions of `NMSC.anomalous_quartetProb`, let the gene trees be independent, each with the law
of the NMSC on `N`. With `p`, `γ`, and the positive lengths `h₁`, `h₂`, `L₀` of
`NMSC.anomalous_quartetProb`, and
`D = γ(1 - γ)(1 - e^{-L₀}) - γ²(1 - e^{-h₁}) - (1 - γ)²(1 - e^{-h₂})`
(`Brooqs.Net.Cycle.anomalyExcess`):
* if `1 - p < p D` (the anomaly zone), for every threshold `t`, almost surely, for all large
  numbers `n` of genes, Algorithm 1 returns no copy of the quartet tree of Q(N_r) on the four taxa
  `k` and returns a quartet tree on `k` that is not in Q(N_r);
* if `p D < 1 - p`, for every threshold `0 < t < t₀(N)`, almost surely, for all large numbers `n`
  of genes, Algorithm 1 returns on `k` exactly the copies of the quartet tree of Q(N_r). -/
theorem anomalous_filterQuartets {N : Brooqs.Net L} (hN : N.WellFormed)
    (htaxa : ∀ x : L, x ∈ N.taxa) {k : QuartetKey} (hk : keyTaxa k ⊆ L) (C : N.Cycle)
    {i j a b : Fin 4} (hinj : Function.Injective ![i, j, a, b])
    (hbelow : C.below.lin (keyTaxon k hk) = {i, j}) (h3 : 3 ≤ #(C.top.lin (keyTaxon k hk)))
    (h1 : ∀ n ∈ C.side₁.nodes ++ C.side₂.nodes, #(n.2.2.lin (keyTaxon k hk)) ≤ 1)
    (G : ℕ → Ω → Finset (Finset L)) (hind : iIndepFun G P)
    (hid : ∀ n, IdentDistrib (G n) (G 0) P P)
    (hlaw : ∀ T, P.real (G 0 ⁻¹' {T}) = N.geneTreeDist id T) :
    (1 - C.apartProb (blockSample k hk i j a b) <
      C.apartProb (blockSample k hk i j a b) * C.anomalyExcess (blockSample k hk i j a b) →
        ∀ t, ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
          (filterQuartets t (geneQuartets (fun i => G i ω) n)).count
              (k.quartet (pairIndex i j)) = 0 ∧
            ∃ q ∈ filterQuartets t (geneQuartets (fun i => G i ω) n), q.key = k ∧
              ¬ DisplaysQuartet N q) ∧
      (C.apartProb (blockSample k hk i j a b) * C.anomalyExcess (blockSample k hk i j a b) <
        1 - C.apartProb (blockSample k hk i j a b) →
        ∀ t, 0 < t → t < threshold N → ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ u,
          (filterQuartets t (geneQuartets (fun i => G i ω) n)).count (k.quartet u) =
            if DisplaysQuartet N (k.quartet u) then
              (geneQuartets (fun i => G i ω) n).count (k.quartet u) else 0) := by
  obtain ⟨hdisp, -, -, -, e0, e1⟩ := anomalous_quartetProb hN htaxa hk C hinj hbelow h3 h1
  refine ⟨fun hzone t => ?_, fun hzone t ht ht₀ => ?_⟩
  · refine filterQuartets_block_of_least hdisp (fun u hu => ?_) G hind hid hlaw t
    rw [e0, e1 u hu]
    unfold Brooqs.Net.Cycle.anomalyExcess at hzone
    linarith
  · refine filterQuartets_block_of_most hN htaxa (mem_keysOn.2 hk) hdisp (fun u hu => ?_)
      (fun u u' hu hu' => by rw [e1 u hu, e1 u' hu']) G hind hid hlaw ht ht₀
    rw [e0, e1 u hu]
    unfold Brooqs.Net.Cycle.anomalyExcess at hzone
    linarith

/-- **Quartet Filtering on the boundary of the anomaly zone.** Under the assumptions of
`NMSC.anomalous_filterQuartets`, if `p D = 1 - p`, the three quartet trees on the four taxa `k` have
probability `1/3`, and for every threshold `t > 0`, almost surely, for all large numbers `n` of
genes, Algorithm 1 returns on `k` the copies of a single quartet tree
(`NMSC.filterQuartets_block_of_equal`). -/
theorem anomalous_filterQuartets_boundary {N : Brooqs.Net L} (hN : N.WellFormed)
    (htaxa : ∀ x : L, x ∈ N.taxa) {k : QuartetKey} (hk : keyTaxa k ⊆ L) (C : N.Cycle)
    {i j a b : Fin 4} (hinj : Function.Injective ![i, j, a, b])
    (hbelow : C.below.lin (keyTaxon k hk) = {i, j}) (h3 : 3 ≤ #(C.top.lin (keyTaxon k hk)))
    (h1 : ∀ n ∈ C.side₁.nodes ++ C.side₂.nodes, #(n.2.2.lin (keyTaxon k hk)) ≤ 1)
    (G : ℕ → Ω → Finset (Finset L)) (hind : iIndepFun G P)
    (hid : ∀ n, IdentDistrib (G n) (G 0) P P)
    (hlaw : ∀ T, P.real (G 0 ⁻¹' {T}) = N.geneTreeDist id T) :
    C.apartProb (blockSample k hk i j a b) * C.anomalyExcess (blockSample k hk i j a b) =
      1 - C.apartProb (blockSample k hk i j a b) →
        (∀ u, quartetProb N (k.quartet u) = 1 / 3) ∧
        ∀ t, 0 < t → ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∃ u, ∀ u',
          (filterQuartets t (geneQuartets (fun i => G i ω) n)).count (k.quartet u') =
            if u' = u then (geneQuartets (fun i => G i ω) n).count (k.quartet u) else 0 := by
  intro hzone
  obtain ⟨-, -, -, -, e0, e1⟩ := anomalous_quartetProb hN htaxa hk C hinj hbelow h3 h1
  unfold Brooqs.Net.Cycle.anomalyExcess at hzone
  -- the three probabilities are equal; they add up to `1`
  have hall : ∀ u, quartetProb N (k.quartet u) =
      quartetProb N (k.quartet (pairIndex i j)) := fun u => by
    by_cases hu : u = pairIndex i j
    · rw [hu]
    · rw [e1 u hu, e0]
      linarith
  have hsum : quartetProb N (k.quartet 0) + quartetProb N (k.quartet 1) +
      quartetProb N (k.quartet 2) = 1 := by
    obtain ⟨q0, q1, q2⟩ := quartetProb_eq_quartetCF N hN.2 k hk
    rw [q0, q1, q2]
    have hsN : ∀ l, keyTaxon k hk l ∈ N.taxa := fun l => htaxa _
    have := Brooqs.Net.splitCF_sum hN.2 hsN
    rw [N.quartetCF_eq_splitCF_of (keyTaxon k hk) (i := 0) (j := 1) (k := 2) (l := 3) (by decide),
      N.quartetCF_eq_splitCF_of (keyTaxon k hk) (i := 0) (j := 2) (k := 1) (l := 3) (by decide),
      N.quartetCF_eq_splitCF_of (keyTaxon k hk) (i := 0) (j := 3) (k := 1) (l := 2) (by decide)]
    exact this
  have hthird : ∀ u, quartetProb N (k.quartet u) = 1 / 3 := fun u => by
    rw [hall u]
    rw [hall 0, hall 1, hall 2] at hsum
    linarith
  refine ⟨hthird, fun t ht => ?_⟩
  exact filterQuartets_block_of_equal (by rw [hthird]; norm_num)
    (fun u => by rw [hthird, hthird]) G hind hid hlaw ht

end Genes

end NMSC

end Camus
