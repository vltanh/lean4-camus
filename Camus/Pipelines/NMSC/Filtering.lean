module

public import Camus.Pipelines.NMSC.Quartets
public import Camus.Pipelines.Astral
public import Camus.External.NMSC.Pattern

/-!
# Section 3.4: Quartet Filtering under the NMSC, when the quartet CFs have the regular pattern

Section 3.3 designs Quartet Filtering (Algorithm 1) for gene trees that evolve down a level-1
network `N` under the NMSC: "Our approach is to take the distribution on quartet trees, and decide
whether for a given set of four species, the distribution is suggestive of an ILS-only scenario. If
so, then we would just keep the most frequently observed quartet tree, and otherwise we would keep
the top two most frequent quartet trees. The motivation for this approach is that we do not want to
include quartet trees that are not in Q(Nr). On the other hand, we do not want to eliminate these
quartet trees." This file proves that the aim is reached when every set of four taxa has the CF
pattern that this design presumes (`NMSC.RegularOn`): if `N` displays one quartet tree on the four
taxa, it is strictly the most probable and the two others are equally probable; if `N` displays two
of them, the third is strictly the least probable. Then for every threshold `0 < t < t₀(N)`, where
`t₀(N)` is the least ratio `(p₂ − p₃)/(p₂ + p₃)` over the sets of four taxa on which `N` displays
two quartet trees (`NMSC.threshold`), almost surely, for all large numbers of genes, Quartet
Filtering returns exactly the quartet trees of the gene trees that are in Q(N_r), with their
multiplicities (`NMSC.nmsc_filterQuartets`).

The pattern holds on every set of four taxa except in one configuration: a cycle with two of the
four taxa below its hybrid node and the two others in two other components
(`Brooqs.Net.Anomalous`, `Brooqs.Net.regularOn_of_not_anomalous`). So Quartet Filtering is
consistent for Q(N_r) on networks without this configuration (`NMSC.NoAnomaly`,
`NMSC.nmsc_filterQuartets_of_noAnomaly`), for instance networks whose hybrid nodes each have a
single leaf below them (`NMSC.noAnomaly_of_below`). It is not in general:
`Camus/Pipelines/NMSC/Anomaly.lean` shows a network on which the only quartet tree in Q(N_r) on four
taxa is strictly the least probable, and Quartet Filtering then fails for every threshold.

## Main results

* `NMSC.RegularOn`, `NMSC.Regular`, `NMSC.regularOn_iff`: the CF pattern on a set of four taxa, and
  on all of them.
* `NMSC.threshold`, `NMSC.lt_threshold_iff`, `NMSC.threshold_pos`: the threshold `t₀(N)`.
* `NMSC.nmsc_filterBlock`, `NMSC.nmsc_filterQuartets`: Quartet Filtering under the NMSC, for
  networks with the pattern.
* `NMSC.NoAnomaly`, `NMSC.noAnomaly_of_below`, `NMSC.regular_of_noAnomaly`,
  `NMSC.nmsc_filterQuartets_of_noAnomaly`: networks without the anomalous configuration.

## Proof

As for the multispecies coalescent (`Coalescent.msc_filterQuartets`): by the strong law of large
numbers the relative frequencies of the three quartet trees on four taxa converge almost surely to
their probabilities (`Coalescent.ae_tendsto_frequency`). Where `N` displays one quartet tree, it is
eventually the most frequent and the test of Algorithm 1 fails for the two others, since the gap
between their frequencies tends to `0` and `t > 0` (`Algorithm1.eventually_msc_pattern`). Where `N`
displays two, the third is eventually the least frequent and the test holds, since
`t < (p₂ − p₃)/(p₂ + p₃)` (`Algorithm1.eventually_retain_pattern`).
-/

@[expose] public noncomputable section

namespace Camus

namespace NMSC

open Finset Filter Topology MeasureTheory ProbabilityTheory Coalescent Algorithm1

variable {L : Finset ℕ}

/-- The quartet CFs of the four taxa of `k` under the NMSC on `N` have the pattern that the design
of Quartet Filtering presumes (Section 3.3, `Brooqs.RegularPattern`):
* `N` displays exactly one of the three quartet trees on them, `s₁`; it is strictly the most
  probable, and the two others are equally probable, with positive probability; or
* `N` displays exactly two of them; the third, `s₃`, is strictly the least probable. -/
def RegularOn (N : Brooqs.Net L) (k : QuartetKey) : Prop :=
  Brooqs.RegularPattern (fun s => DisplaysQuartet N (k.quartet s))
    (fun s => quartetProb N (k.quartet s))

/-- Every set of four taxa of `L` has the pattern `RegularOn`. -/
def Regular (N : Brooqs.Net L) : Prop := ∀ k ∈ keysOn L, RegularOn N k

/-- The ratios `(p₂ − p₃)/(p₂ + p₃)` of the sets of four taxa of `L` on which `N` displays two
quartet trees: `p₂` is the probability of one of the two displayed quartet trees, `p₃` that of the
third. -/
def ratios (N : Brooqs.Net L) : Finset ℝ :=
  ((keysOn L ×ˢ (univ : Finset (Fin 3)) ×ˢ (univ : Finset (Fin 3))).filter fun x =>
      x.2.1 ≠ x.2.2 ∧ ¬ DisplaysQuartet N (x.1.quartet x.2.2) ∧
        ∀ s, s ≠ x.2.2 → DisplaysQuartet N (x.1.quartet s)).image fun x =>
    (quartetProb N (x.1.quartet x.2.1) - quartetProb N (x.1.quartet x.2.2)) /
      (quartetProb N (x.1.quartet x.2.1) + quartetProb N (x.1.quartet x.2.2))

/-- The threshold `t₀(N)` of Section 3.4: the least of the ratios `(p₂ − p₃)/(p₂ + p₃)` of the sets
of four taxa on which `N` displays two quartet trees, and `1` if there are none. -/
def threshold (N : Brooqs.Net L) : ℝ := (insert 1 (ratios N)).min' (insert_nonempty _ _)

/-- `t < t₀(N)` iff `t < 1` and `t` is below every ratio. -/
theorem lt_threshold_iff (N : Brooqs.Net L) (t : ℝ) :
    t < threshold N ↔ t < 1 ∧ ∀ r ∈ ratios N, t < r := by
  rw [threshold, Finset.lt_min'_iff]
  simp

/-- On a set of four taxa on which `N` displays two quartet trees, a threshold below `t₀(N)` keeps
the second most probable one in the limit. -/
theorem retainSecond_of_lt_threshold {N : Brooqs.Net L} {t : ℝ} (ht : t < threshold N)
    {k : QuartetKey} (hk : k ∈ keysOn L) {s₃ s : Fin 3} (hs : s ≠ s₃)
    (h₃ : ¬ DisplaysQuartet N (k.quartet s₃)) (h : ∀ s, s ≠ s₃ → DisplaysQuartet N (k.quartet s))
    (hlt : quartetProb N (k.quartet s₃) < quartetProb N (k.quartet s))
    (hnn : 0 ≤ quartetProb N (k.quartet s₃)) :
    retainSecond t (quartetProb N (k.quartet s)) (quartetProb N (k.quartet s₃)) := by
  rw [retainSecond_iff_ratio _ _ _ (by linarith)]
  refine ((lt_threshold_iff N t).1 ht).2 _ (mem_image.2 ⟨(k, s, s₃), mem_filter.2 ⟨?_, hs, h₃, h⟩,
    rfl⟩)
  simp [hk]

/-- The probability that a gene tree induces a quartet tree is nonnegative. -/
theorem quartetProb_nonneg {N : Brooqs.Net L} (hN : N.WellFormed) (q : Quartet) :
    0 ≤ quartetProb N q :=
  sum_nonneg fun G _ => by
    split_ifs
    · exact Brooqs.Net.geneTreeDist_nonneg hN id G
    · exact le_rfl

private theorem fl_exists_other : ∀ a b : Fin 3, ∃ u : Fin 3, u ≠ a ∧ u ≠ b := by
  decide

/-- If every set of four taxa has the pattern `RegularOn`, the threshold `t₀(N)` is positive. -/
theorem threshold_pos {N : Brooqs.Net L} (hN : N.WellFormed) (hreg : Regular N) :
    0 < threshold N := by
  have h := (lt_threshold_iff N 0).2 ⟨one_pos, fun r hr => ?_⟩
  · exact h
  obtain ⟨⟨k, s, s₃⟩, hx, rfl⟩ := mem_image.1 hr
  obtain ⟨hx, hs, h₃, hdisp⟩ := mem_filter.1 hx
  simp only [mem_product, mem_univ, and_true] at hx
  have hnn := quartetProb_nonneg hN (k.quartet s₃)
  rcases hreg k hx with ⟨s₁, -, hnot, -, -, -⟩ | ⟨s₃', h₃', -, hlt⟩
  · -- one displayed quartet tree: impossible, two values other than `s₃` are displayed
    exfalso
    obtain ⟨u, hu₃, hu₁⟩ := fl_exists_other s₃ s₁
    exact hnot u hu₁ (hdisp u hu₃)
  · have heq : s₃' = s₃ := by
      by_contra hne
      exact h₃' (hdisp s₃' hne)
    subst heq
    have hl := hlt s hs
    exact div_pos (by linarith) (by linarith)

section Genes

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  [MeasurableSpace (Finset (Finset L))] [MeasurableSingletonClass (Finset (Finset L))]

/-- **Section 3.4: Quartet Filtering under the NMSC, on four taxa.** Let the gene trees be
independent, each with the law of the NMSC on the metric network `N` with distinct leaf labels, and
let the four taxa of `k` have the pattern `RegularOn`. For every threshold `0 < t < t₀(N)`, almost
surely, for all large numbers `n` of genes, Algorithm 1 applied to the quartet trees of the first
`n` gene trees keeps on these four taxa every copy of the quartet trees in Q(N_r) and no copy of the
others. -/
theorem nmsc_filterBlock {N : Brooqs.Net L} (hN : N.WellFormed) (G : ℕ → Ω → Finset (Finset L))
    (hind : iIndepFun G P) (hid : ∀ n, IdentDistrib (G n) (G 0) P P)
    (hlaw : ∀ T, P.real (G 0 ⁻¹' {T}) = N.geneTreeDist id T) {t : ℝ} (ht : 0 < t)
    (ht₀ : t < threshold N) {k : QuartetKey} (hk : k ∈ keysOn L) (hreg : RegularOn N k) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ s,
      (filterBlock t ((geneQuartets (fun i => G i ω) n).map quartetEquiv) k).count (k, s) =
        if DisplaysQuartet N (k.quartet s) then
          (geneQuartets (fun i => G i ω) n).count (k.quartet s) else 0 := by
  set p : Fin 3 → ℝ := fun s => quartetProb N (k.quartet s) with hpdef
  have hp : ∀ s, P.real {ω | Induces (G 0 ω) (k.quartet s)} = p s := fun s =>
    measureReal_induces N (G 0) (hid 0).aemeasurable_fst hlaw _
  -- by the strong law, the relative frequencies converge almost surely
  have hconv : ∀ᵐ ω ∂P, ∀ s, Tendsto (fun n : ℕ =>
      ((geneQuartets (fun i => G i ω) n).count (k.quartet s) : ℝ) / n) atTop (𝓝 (p s)) := by
    rw [ae_all_iff]
    intro s
    rw [← hp]
    exact ae_tendsto_frequency G hind hid _
  filter_upwards [hconv] with ω hω
  rcases hreg with ⟨s₁, h₁, hnot, hmax, heq, hpos⟩ | ⟨s₃, h₃, hdisp, hmin⟩
  · -- one displayed quartet tree: eventually it is the most frequent, and the test fails
    filter_upwards [eventually_msc_pattern hω hmax heq (fun s _ => hpos s) ht] with n hn s
    simp only [← frequencies_map] at hn
    rw [filterBlock_eq_replicate hn.1 hn.2, Multiset.count_replicate]
    by_cases hs : s = s₁
    · subst hs
      rw [ite_eq_left rfl, ite_eq_left h₁, count_map_quartetEquiv]
    · rw [ite_eq_right (fun h => hs (Prod.ext_iff.1 h).2.symm), ite_eq_right (hnot s hs)]
  · -- two displayed quartet trees: eventually the third is the least frequent, and the test holds
    have hret : ∀ s, s ≠ s₃ → retainSecond t (p s) (p s₃) := fun s hs =>
      retainSecond_of_lt_threshold ht₀ hk hs h₃ hdisp (hmin s hs)
        (quartetProb_nonneg hN (k.quartet s₃))
    filter_upwards [eventually_retain_pattern hω hmin hret] with n hn s
    simp only [← frequencies_map] at hn
    rw [filterBlock_count_of_retain hn.1 hn.2 s, count_map_quartetEquiv]
    by_cases hs : s = s₃
    · subst hs
      rw [ite_eq_left rfl, ite_eq_right h₃]
    · rw [ite_eq_right hs, ite_eq_left (hdisp s hs)]

/-- **Section 3.4: Quartet Filtering under the NMSC.** Let the gene trees be independent, each with
the law of the NMSC on the metric network `N` with distinct leaf labels on the taxa `L`, and let
every set of four taxa have the pattern `RegularOn`. For every threshold `0 < t < t₀(N)`, almost
surely, for all large numbers `n` of genes, Algorithm 1 applied to the multiset `Q` of the quartet
trees of the first `n` gene trees returns exactly the quartet trees of `Q` in Q(N_r), with their
multiplicities: "we do not want to include quartet trees that are not in Q(Nr). On the other hand,
we do not want to eliminate these quartet trees." -/
theorem nmsc_filterQuartets {N : Brooqs.Net L} (hN : N.WellFormed)
    (G : ℕ → Ω → Finset (Finset L)) (hind : iIndepFun G P)
    (hid : ∀ n, IdentDistrib (G n) (G 0) P P)
    (hlaw : ∀ T, P.real (G 0 ⁻¹' {T}) = N.geneTreeDist id T) (hreg : Regular N) {t : ℝ}
    (ht : 0 < t) (ht₀ : t < threshold N) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      filterQuartets t (geneQuartets (fun i => G i ω) n) =
        (geneQuartets (fun i => G i ω) n).filter (DisplaysQuartet N) := by
  have hblock : ∀ᵐ ω ∂P, ∀ k ∈ keysOn L, ∀ᶠ n in atTop, ∀ s,
      (filterBlock t ((geneQuartets (fun i => G i ω) n).map quartetEquiv) k).count (k, s) =
        if DisplaysQuartet N (k.quartet s) then
          (geneQuartets (fun i => G i ω) n).count (k.quartet s) else 0 :=
    (eventually_all_finset (keysOn L)).2 fun k hk =>
      nmsc_filterBlock hN G hind hid hlaw ht ht₀ hk (hreg k hk)
  filter_upwards [hblock] with ω hω
  filter_upwards [(eventually_all_finset (keysOn L)).2 hω] with n hn
  ext q
  rw [count_filterQuartets, Multiset.count_filter]
  have hqk : q.key.quartet q.split = q := Quartet.key_quartet q
  by_cases hq : q.taxa ⊆ L
  · have hk : q.key ∈ keysOn L := mem_keysOn.2 (by
      have := hq
      rwa [← hqk, QuartetKey.quartet_taxa] at this)
    rw [hn q.key hk q.split, hqk]
  · -- no gene tree induces a quartet tree on other taxa
    have h0 := count_geneQuartets_eq_zero (fun i => G i ω) n hq
    have := count_filterBlock_le t ((geneQuartets (fun i => G i ω) n).map quartetEquiv) q.key
      (q.key, q.split)
    rw [count_map_quartetEquiv _ q.key q.split, hqk, h0] at this
    rw [Nat.le_zero.1 this]
    split_ifs <;> simp [h0]

end Genes

/-! ### Networks without the anomalous configuration -/

/-- No four taxa of `N` are in the anomalous configuration of `Brooqs.Net.Anomalous`: no cycle has
two of them below its hybrid node and the two others in two other components. -/
def NoAnomaly (N : Brooqs.Net L) : Prop :=
  ∀ s : Fin 4 → L, Function.Injective s → ¬ N.Anomalous s

/-- A network whose hybrid nodes each have a single leaf below them has no anomalous set of four
taxa. -/
theorem noAnomaly_of_below {N : Brooqs.Net L} (h : ∀ Ω : N.Cycle, Ω.below.leaves.length ≤ 1) :
    NoAnomaly N := by
  rintro s hs ⟨Ω, h2, -, -⟩
  have hle : #(Ω.below.lin s) ≤ 1 := by
    refine (card_le_card_of_injOn (t := Ω.below.taxa) s (fun l hl => ?_) hs.injOn).trans ?_
    · simp only [Brooqs.Net.lin, coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at hl
      exact hl
    · exact (List.toFinset_card_le _).trans (h Ω)
  omega

/-- The pattern of `Brooqs.Net.RegularOn` for the four taxa of `k` is the pattern `RegularOn` of the
quartet trees of CAMUS on them. -/
theorem regularOn_iff (N : Brooqs.Net L) (hN : N.leaves.Nodup) (k : QuartetKey)
    (hk : keyTaxa k ⊆ L) :
    RegularOn N k ↔ N.RegularOn (keyTaxon k hk 0) (keyTaxon k hk 1) (keyTaxon k hk 2)
      (keyTaxon k hk 3) := by
  obtain ⟨d0, d1, d2⟩ := displaysQuartet_iff N k hk
  obtain ⟨p0, p1, p2⟩ := quartetProb_eq_quartetCF N hN k hk
  have hd : (fun s => DisplaysQuartet N (k.quartet s)) =
      N.disp3 (keyTaxon k hk 0) (keyTaxon k hk 1) (keyTaxon k hk 2) (keyTaxon k hk 3) := by
    funext s
    fin_cases s
    · exact propext d0
    · exact propext d1
    · exact propext d2
  have hc : (fun s => quartetProb N (k.quartet s)) =
      N.cf3 (keyTaxon k hk 0) (keyTaxon k hk 1) (keyTaxon k hk 2) (keyTaxon k hk 3) := by
    funext s
    fin_cases s
    · exact p0
    · exact p1
    · exact p2
  rw [RegularOn, Brooqs.Net.RegularOn, hd, hc]

/-- A metric network with distinct leaf labels on the taxa `L`, without the anomalous configuration,
has the pattern `RegularOn` on every set of four taxa. -/
theorem regular_of_noAnomaly {N : Brooqs.Net L} (hN : N.WellFormed)
    (htaxa : ∀ x : L, x ∈ N.taxa) (hna : NoAnomaly N) : Regular N := by
  intro k hk
  have hk' : keyTaxa k ⊆ L := mem_keysOn.1 hk
  rw [regularOn_iff N hN.2 k hk']
  exact Brooqs.Net.regularOn_of_not_anomalous hN (keyTaxon k hk').injective (fun l => htaxa _)
    (hna _ (keyTaxon k hk').injective)

section Unconditional

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  [MeasurableSpace (Finset (Finset L))] [MeasurableSingletonClass (Finset (Finset L))]

/-- **Section 3.4: Quartet Filtering under the NMSC.** Let the gene trees be independent, each with
the law of the NMSC on a metric level-1 network `N` with distinct leaf labels on the taxa `L`, and
let no four taxa of `N` be in the anomalous configuration (`NoAnomaly`). For every threshold
`0 < t < t₀(N)`, almost surely, for all large numbers `n` of genes, Algorithm 1 applied to the
multiset `Q` of the quartet trees of the first `n` gene trees returns exactly the quartet trees of
`Q` in Q(N_r), with their multiplicities. -/
theorem nmsc_filterQuartets_of_noAnomaly {N : Brooqs.Net L} (hN : N.WellFormed)
    (htaxa : ∀ x : L, x ∈ N.taxa) (hna : NoAnomaly N) (G : ℕ → Ω → Finset (Finset L))
    (hind : iIndepFun G P) (hid : ∀ n, IdentDistrib (G n) (G 0) P P)
    (hlaw : ∀ T, P.real (G 0 ⁻¹' {T}) = N.geneTreeDist id T) {t : ℝ} (ht : 0 < t)
    (ht₀ : t < threshold N) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      filterQuartets t (geneQuartets (fun i => G i ω) n) =
        (geneQuartets (fun i => G i ω) n).filter (DisplaysQuartet N) :=
  nmsc_filterQuartets hN G hind hid hlaw (regular_of_noAnomaly hN htaxa hna) ht ht₀

end Unconditional

end NMSC

end Camus
