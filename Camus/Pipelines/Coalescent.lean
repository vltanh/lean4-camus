module

public import Camus.Pipelines.Coalescent.Frequencies
public import Camus.Pipelines.Coalescent.Quartets
public import Camus.Pipelines.Coalescent.Topology
public import Mathlib.Probability.StrongLaw

/-!
# Section 3.4: Quartet Filtering under the multispecies coalescent

Section 3.4 explains Algorithm 1 (Quartet Filtering) by the multispecies coalescent (MSC): when
"the gene trees evolve down the tree under the MSC ... for large numbers of gene trees, we expect
the distribution on quartet tree topologies to be close to the expected values under the MSC,
which is f1>f2=f3. For finite numbers of gene trees, we would not expect f2=f3, but as the number
of genes increases, the gap between f2 and f3 will approach 0", so that Algorithm 1 keeps only
the most frequent quartet tree; and the second most frequent is kept "for t small enough
(specifically, t<(f2−f3)/(f2+f3))". This file proves the corresponding statements for gene trees
drawn independently from a distribution. Under the MSC on a rooted binary species tree, for every
threshold `t > 0`, almost surely, for all large numbers of genes, Algorithm 1 keeps on every four
taxa exactly the copies of the quartet tree of the species tree. When the two least probable
topologies have probabilities `p₂ > p₃` (as under a network with reticulations) and
`t < (p₂ − p₃)/(p₂ + p₃)`, almost surely, for all large numbers of genes, it keeps the second
topology too. The threshold must be positive in the first statement: for `t = 0` the test keeps
`q₂` whenever `f₂ > f₃` (`retainSecond_zero`).

The gene trees are random variables `G n : Ω → Finset (Finset L)`, unrooted trees on the taxa `L`
in the representation of lean4-adr11 (`Camus/Pipelines/Coalescent/Quartets.lean`), independent
(`ProbabilityTheory.iIndepFun`) and identically distributed (`ProbabilityTheory.IdentDistrib`).
Under the MSC on `σ`, `G 0` has the distribution `σ.unrootedDist id`. The multiset `Q` given to
Algorithm 1 is `geneQuartets`: all quartet trees induced by the first `n` gene trees, each gene
tree contributing one copy of each quartet tree it induces.

## Main results

* `Coalescent.geneQuartets`, `Coalescent.count_geneQuartets`: the multiset `Q` of the quartet
  trees of the first `n` gene trees, and its multiplicities.
* `Coalescent.ae_tendsto_frequency`: the strong law of large numbers for the relative frequency of
  a quartet tree.
* `Coalescent.measureReal_induces`: under the MSC, the probability that a gene tree induces a
  quartet tree is `quartetProb`.
* `Coalescent.msc_filterBlock`: under the MSC and for `t > 0`, almost surely, eventually
  Algorithm 1 keeps on four taxa exactly the copies of the quartet tree of the species tree.
* `Coalescent.msc_filterQuartets`, `Coalescent.msc_filterQuartets_induced`: the same on all sets
  of four taxa at once: almost surely, eventually `filterQuartets t Q` is the multiset of the
  quartet trees of `Q` induced by the species tree, that is, of those in Q(T) for the species
  tree `T` as a tree of CAMUS.
* `Coalescent.filterBlock_keeps_second`: if `p₁ ≥ p₂ > p₃` and `t < (p₂ − p₃)/(p₂ + p₃)`, almost
  surely, eventually Algorithm 1 keeps every copy of the two most probable topologies and none of
  the third.

## Proof (the paper's)

* Under the MSC, the probabilities of the three topologies on four taxa are `p₁ > p₂ = p₃ > 0`,
  `p₁` for the topology of the species tree (`Coalescent.msc_pattern_of_induces`, Section 3.3).
* For large numbers of gene trees the relative frequencies approach these probabilities: almost
  surely `fᵢ → pᵢ`, by the strong law of large numbers applied to the indicator that a gene tree
  induces the quartet tree (`Coalescent.ae_tendsto_frequency`).
* The gap between `f₂` and `f₃` approaches `0`, while `t (f₂ + f₃) → 2 t p₂`, which is positive
  since `t > 0` and `p₂ > 0`; so the test of Algorithm 1 eventually fails, and the topology of the
  species tree is eventually the most frequent (`Algorithm1.eventually_msc_pattern`).
* For the converse, the test holds for `p₂` against `p₃`, hence for `p₁`, and eventually for the
  frequencies (`Algorithm1.eventually_retain_pattern`).
-/

@[expose] public section

namespace Camus

namespace Coalescent

open Finset Filter Topology MeasureTheory ProbabilityTheory ADR11 Algorithm1

variable {L : Finset ℕ}

/-! ### The multiset of the quartet trees of the gene trees -/

/-- The quartet tree on the taxa `a, b, c, d` with topology `s`, when `a < b < c < d`. -/
def mkQuartet (x : ℕ × ℕ × ℕ × ℕ × Fin 3) : Option Quartet :=
  if h : x.1 < x.2.1 ∧ x.2.1 < x.2.2.1 ∧ x.2.2.1 < x.2.2.2.1 then
    some ⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1, h.1, h.2.1, h.2.2, x.2.2.2.2⟩
  else none

/-- A quartet tree comes from at most one tuple. -/
theorem mkQuartet_inj (x x' : ℕ × ℕ × ℕ × ℕ × Fin 3) (q : Quartet) (h : q ∈ mkQuartet x)
    (h' : q ∈ mkQuartet x') : x = x' := by
  obtain ⟨a, b, c, d, s⟩ := x
  obtain ⟨a', b', c', d', s'⟩ := x'
  simp only [mkQuartet, Option.mem_def] at h h'
  split_ifs at h h'
  obtain rfl := Option.some.inj h
  simp only [Option.some.injEq, Quartet.mk.injEq] at h'
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h'
  rfl

/-- The quartet trees whose four taxa are in `L`. -/
def quartetsOn (L : Finset ℕ) : Finset Quartet :=
  (L ×ˢ L ×ˢ L ×ˢ L ×ˢ (univ : Finset (Fin 3))).filterMap mkQuartet mkQuartet_inj

/-- The quartet trees on taxa of `L` are those whose four taxa are in `L`. -/
theorem mem_quartetsOn {q : Quartet} : q ∈ quartetsOn L ↔ q.taxa ⊆ L := by
  simp only [quartetsOn, mem_filterMap, mem_product, mem_univ, and_true]
  constructor
  · rintro ⟨⟨a, b, c, d, s⟩, ⟨ha, hb, hc, hd⟩, h⟩
    simp only [mkQuartet] at h
    split_ifs at h
    obtain rfl := Option.some.inj h
    simp [Quartet.taxa, insert_subset_iff, ha, hb, hc, hd]
  · intro h
    simp only [Quartet.taxa, insert_subset_iff, singleton_subset_iff] at h
    exact ⟨(q.a, q.b, q.c, q.d, q.split), ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩,
      by simp [mkQuartet, q.ab, q.bc, q.cd]⟩

/-- The quartet trees induced by the gene tree `T`. -/
def quartetsOf (T : Finset (Finset L)) : Finset Quartet := (quartetsOn L).filter (Induces T)

/-- The quartet trees of `T` are those that `T` induces. -/
theorem mem_quartetsOf {T : Finset (Finset L)} {q : Quartet} :
    q ∈ quartetsOf T ↔ Induces T q := by
  rw [quartetsOf, mem_filter, mem_quartetsOn]
  exact and_iff_right_of_imp fun h => h.1

/-- Section 3.3: the multiset `Q` of the quartet trees of the gene trees `genes 0, …,
genes (n - 1)`, "all quartet trees induced by any gene tree": each gene tree contributes every
quartet tree that it induces. -/
def geneQuartets (genes : ℕ → Finset (Finset L)) (n : ℕ) : Multiset Quartet :=
  ∑ i ∈ range n, (quartetsOf (genes i)).val

/-- The multiplicity of `q` in `Q` is the number of gene trees among the first `n` that induce
`q`. -/
theorem count_geneQuartets (genes : ℕ → Finset (Finset L)) (n : ℕ) (q : Quartet) :
    (geneQuartets genes n).count q = #{i ∈ range n | Induces (genes i) q} := by
  rw [geneQuartets, Multiset.count_sum', card_filter]
  refine sum_congr rfl fun i _ => ?_
  rw [Multiset.count_eq_of_nodup (quartetsOf (genes i)).nodup]
  simp only [mem_val, mem_quartetsOf]

/-- The quartet trees of `Q` are on taxa of `L`. -/
theorem count_geneQuartets_eq_zero (genes : ℕ → Finset (Finset L)) (n : ℕ) {q : Quartet}
    (hq : ¬ q.taxa ⊆ L) : (geneQuartets genes n).count q = 0 := by
  rw [count_geneQuartets, card_eq_zero, filter_eq_empty_iff]
  exact fun i _ h => hq h.1

/-! ### Frequencies and probabilities -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  [MeasurableSpace (Finset (Finset L))] [MeasurableSingletonClass (Finset (Finset L))]

/-- The strong law of large numbers for quartet trees: for independent and identically
distributed gene trees, almost surely, the proportion of the first `n` gene trees that induce the
quartet tree `q` (its multiplicity in `Q` divided by `n`) tends to the probability that a gene tree
induces `q`. -/
theorem ae_tendsto_frequency (G : ℕ → Ω → Finset (Finset L)) (hind : iIndepFun G P)
    (hid : ∀ n, IdentDistrib (G n) (G 0) P P) (q : Quartet) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => ((geneQuartets (fun i => G i ω) n).count q : ℝ) / n) atTop
      (𝓝 (P.real {ω | Induces (G 0 ω) q})) := by
  set φ : Finset (Finset L) → ℝ := fun T => if Induces T q then 1 else 0 with hφ_def
  have hφ : Measurable φ := Measurable.of_discrete
  -- the indicator that the first gene tree induces `q` is integrable, with mean the probability
  have hnull : NullMeasurableSet {ω | Induces (G 0 ω) q} P :=
    (hid 0).aemeasurable_fst.nullMeasurableSet_preimage
      (s := {T : Finset (Finset L) | Induces T q}) MeasurableSet.of_discrete
  have hind_eq : (fun ω => φ (G 0 ω)) = Set.indicator {ω | Induces (G 0 ω) q} 1 := by
    ext ω
    simp [hφ_def, Set.indicator_apply]
  have hint : Integrable (fun ω => φ (G 0 ω)) P := by
    rw [hind_eq]
    exact (integrable_const (1 : ℝ)).indicator₀ hnull
  have hmean : ∫ ω, φ (G 0 ω) ∂P = P.real {ω | Induces (G 0 ω) q} := by
    rw [hind_eq, integral_indicator₀ hnull]
    simp only [Pi.one_apply, setIntegral_const, smul_eq_mul, mul_one]
  -- the strong law, for the indicators of the independent gene trees
  have h := strong_law_ae_real (fun n ω => φ (G n ω)) hint
    (fun a b hab => (hind.indepFun hab).comp hφ hφ) (fun n => (hid n).comp hφ)
  filter_upwards [h] with ω hω
  rw [← hmean]
  refine hω.congr fun n => ?_
  rw [count_geneQuartets, card_filter, Nat.cast_sum]
  refine congrArg (· / (n : ℝ)) (sum_congr rfl fun i _ => ?_)
  simp only [hφ_def]
  split_ifs <;> simp

/-- Under the MSC: if the gene tree `G0` has the distribution `σ.unrootedDist id` of the
multispecies coalescent on `σ`, the probability that it induces `q` is `quartetProb σ q`. -/
theorem measureReal_induces (σ : SpeciesTree L) (G0 : Ω → Finset (Finset L))
    (hG0 : AEMeasurable G0 P) (hlaw : ∀ T, P.real (G0 ⁻¹' {T}) = σ.unrootedDist id T)
    (q : Quartet) : P.real {ω | Induces (G0 ω) q} = quartetProb σ q := by
  have hmap : ∀ S : Set (Finset (Finset L)), P.real (G0 ⁻¹' S) = (P.map G0).real S := fun S => by
    rw [measureReal_def, measureReal_def,
      Measure.map_apply_of_aemeasurable hG0 MeasurableSet.of_discrete]
  have hset : {ω | Induces (G0 ω) q} =
      G0 ⁻¹' ↑(univ.filter fun T : Finset (Finset L) => Induces T q) := by
    ext ω
    simp
  rw [hset, hmap, ← sum_measureReal_singleton, sum_filter]
  refine sum_congr rfl fun T _ => ?_
  split_ifs
  · rw [← hmap, hlaw]
  · rfl

/-! ### Quartet Filtering under the multispecies coalescent -/

/-- The numbers of copies counted by Algorithm 1 on the encoded multiset are the multiplicities of
the quartet trees. -/
theorem frequencies_map (Q : Multiset Quartet) (k : QuartetKey) (s : Fin 3) :
    frequencies (Q.map quartetEquiv) k s = Q.count (k.quartet s) :=
  encoded_frequency Q (k.quartet s)

/-- The multiplicity of `(k, s)` in the encoded multiset is that of the quartet tree of topology
`s` on the four taxa of `k`. -/
theorem count_map_quartetEquiv (Q : Multiset Quartet) (k : QuartetKey) (s : Fin 3) :
    (Q.map quartetEquiv).count (k, s) = Q.count (k.quartet s) :=
  encoded_frequency Q (k.quartet s)

/-- Section 3.4: Quartet Filtering under the multispecies coalescent. Let the gene trees be
independent, each with the distribution of the MSC on a rooted binary species tree `σ`, and let
`a < b < c < d` be the four taxa of `k`, on which `σ` induces the topology `s`. For every threshold
`t > 0`, almost surely, for all large numbers `n` of genes, Algorithm 1 applied to the quartet
trees of the first `n` gene trees keeps on these four taxa exactly the copies of the quartet tree
of `σ`: the most frequent topology is eventually that of `σ`, since `f₁ → p₁ > p₂ = p₃`, and the
second is dropped, since `(f₂ − f₃)/(f₂ + f₃) → 0 < t`. -/
theorem msc_filterBlock {σ : SpeciesTree L} (hσ : σ.IsBinary) (G : ℕ → Ω → Finset (Finset L))
    (hind : iIndepFun G P) (hid : ∀ n, IdentDistrib (G n) (G 0) P P)
    (hlaw : ∀ T, P.real (G 0 ⁻¹' {T}) = σ.unrootedDist id T) {t : ℝ} (ht : 0 < t)
    (k : QuartetKey) (hk : keyTaxa k ⊆ L) {s : Fin 3}
    (hs : Induces (unroot σ.clusters) (k.quartet s)) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      filterBlock t ((geneQuartets (fun i => G i ω) n).map quartetEquiv) k =
        Multiset.replicate ((geneQuartets (fun i => G i ω) n).count (k.quartet s)) (k, s) := by
  -- the probabilities of the three topologies have the pattern of the MSC
  obtain ⟨hmax, heq, hpos⟩ := msc_pattern_of_induces hσ k hk hs
  -- by the strong law, the relative frequencies converge to them almost surely
  have hconv : ∀ᵐ ω ∂P, ∀ s', Tendsto (fun n : ℕ =>
      ((geneQuartets (fun i => G i ω) n).count (k.quartet s') : ℝ) / n) atTop
      (𝓝 (quartetProb σ (k.quartet s'))) := by
    rw [ae_all_iff]
    intro s'
    rw [← measureReal_induces σ (G 0) (hid 0).aemeasurable_fst hlaw]
    exact ae_tendsto_frequency G hind hid _
  filter_upwards [hconv] with ω hω
  -- eventually the topology of `σ` is the most frequent and the test fails for the two others
  filter_upwards [eventually_msc_pattern hω hmax heq hpos ht] with n hn
  simp only [← frequencies_map] at hn
  rw [filterBlock_eq_replicate hn.1 hn.2, count_map_quartetEquiv]

/-- Section 3.4: Quartet Filtering under the multispecies coalescent, on all sets of four taxa.
Let the gene trees be independent, each with the distribution of the MSC on a rooted binary
species tree `σ`. For every threshold `t > 0`, almost surely, for all large numbers `n` of genes,
Algorithm 1 applied to the multiset `Q` of the quartet trees of the first `n` gene trees returns
exactly the quartet trees of `Q` that the species tree induces, with their multiplicities. -/
theorem msc_filterQuartets {σ : SpeciesTree L} (hσ : σ.IsBinary)
    (G : ℕ → Ω → Finset (Finset L)) (hind : iIndepFun G P)
    (hid : ∀ n, IdentDistrib (G n) (G 0) P P)
    (hlaw : ∀ T, P.real (G 0 ⁻¹' {T}) = σ.unrootedDist id T) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      filterQuartets t (geneQuartets (fun i => G i ω) n) =
        (geneQuartets (fun i => G i ω) n).filter (Induces (unroot σ.clusters)) := by
  -- the sets of four taxa of `σ`, and the topology that `σ` induces on each
  set keys := (quartetsOn L).image Quartet.key
  have hkeys : ∀ k ∈ keys, keyTaxa k ⊆ L := by
    intro k hk
    obtain ⟨q, hq, rfl⟩ := mem_image.1 hk
    exact mem_quartetsOn.1 hq
  have hspecies : ∀ k ∈ keys, ∃! s, Induces (unroot σ.clusters) (k.quartet s) :=
    fun k hk => existsUnique_species hσ k (hkeys k hk)
  -- almost surely, on every set of four taxa, eventually only the quartet tree of `σ` is kept
  have hblock : ∀ᵐ ω ∂P, ∀ k ∈ keys, ∀ᶠ n in atTop, ∀ s,
      Induces (unroot σ.clusters) (k.quartet s) →
        filterBlock t ((geneQuartets (fun i => G i ω) n).map quartetEquiv) k =
          Multiset.replicate ((geneQuartets (fun i => G i ω) n).count (k.quartet s)) (k, s) := by
    refine (eventually_all_finset keys).2 fun k hk => ?_
    obtain ⟨s, hs, huniq⟩ := hspecies k hk
    filter_upwards [msc_filterBlock hσ G hind hid hlaw ht k (hkeys k hk) hs] with ω hω
    filter_upwards [hω] with n hn s' hs'
    rw [huniq s' hs']
    exact hn
  filter_upwards [hblock] with ω hω
  filter_upwards [(eventually_all_finset keys).2 hω] with n hn
  -- compare the multiplicities of each quartet tree `q`
  ext q
  rw [count_filterQuartets, Multiset.count_filter]
  by_cases hq : q.taxa ⊆ L
  · have hk : q.key ∈ keys := mem_image.2 ⟨q, mem_quartetsOn.2 hq, rfl⟩
    obtain ⟨s, hs, huniq⟩ := hspecies q.key hk
    have hqk : q.key.quartet q.split = q := rfl
    rw [hn q.key hk s hs, Multiset.count_replicate]
    by_cases hqs : q.split = s
    · have hind' : Induces (unroot σ.clusters) q := by rw [← hqk, hqs]; exact hs
      rw [ite_eq_left hind', ← hqs, hqk]
      simp
    · have hind' : ¬ Induces (unroot σ.clusters) q := fun h =>
        hqs (huniq q.split h)
      rw [ite_eq_right hind']
      simp only [Prod.mk.injEq, true_and]
      exact ite_eq_right (Ne.symm hqs)
  · -- no gene tree induces a quartet tree on other taxa
    have h0 := count_geneQuartets_eq_zero (fun i => G i ω) n hq
    have hind' : ¬ Induces (unroot σ.clusters) q := fun h => hq h.1
    rw [ite_eq_right hind']
    have := count_filterBlock_le t ((geneQuartets (fun i => G i ω) n).map quartetEquiv) q.key
      (q.key, q.split)
    rw [count_map_quartetEquiv _ q.key q.split] at this
    have hqk : q.key.quartet q.split = q := rfl
    rw [hqk, h0] at this
    omega

/-- Section 3.4: Quartet Filtering under the multispecies coalescent, with the species tree as a
tree of CAMUS. Let the gene trees be independent, each with the distribution of the MSC on a
species tree `σ` whose rooted topology is the tree `tree` of CAMUS (`σ` is then binary). For every
threshold `t > 0`, almost surely, for all large numbers `n` of genes, Algorithm 1 applied to the
multiset `Q` of the quartet trees of the first `n` gene trees returns exactly the quartet trees of
`Q` that belong to Q(tree), with their multiplicities. -/
theorem msc_filterQuartets_induced {σ : SpeciesTree L} {tree : PhyloTree}
    (htree : HasTopology σ tree) (G : ℕ → Ω → Finset (Finset L)) (hind : iIndepFun G P)
    (hid : ∀ n, IdentDistrib (G n) (G 0) P P)
    (hlaw : ∀ T, P.real (G 0 ⁻¹' {T}) = σ.unrootedDist id T) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      filterQuartets t (geneQuartets (fun i => G i ω) n) =
        (geneQuartets (fun i => G i ω) n).filter fun q => q.induced tree = true := by
  filter_upwards [msc_filterQuartets (isBinary_of_hasTopology htree) G hind hid hlaw ht]
    with ω hω
  filter_upwards [hω] with n hn
  rw [hn]
  exact Multiset.filter_congr fun q _ => induces_iff_induced htree q

/-! ### The converse signal -/

/-- Section 3.4: the converse signal. Let the gene trees be independent and identically
distributed (for instance under a network with reticulations, not formalized here), and let the
three topologies `s₁, s₂, s₃` on the four taxa `a < b < c < d` of `k` have probabilities
`p s₁ ≥ p s₂ > p s₃`. For every threshold `t < (p s₂ − p s₃)/(p s₂ + p s₃)`, almost surely, for all
large numbers `n` of genes, Algorithm 1 keeps on these four taxa every copy of the two most
probable topologies and no copy of `s₃`, in the limit of the paper's "for t small enough
(specifically, t<(f2−f3)/(f2+f3)), then we will include q2". -/
theorem filterBlock_keeps_second (G : ℕ → Ω → Finset (Finset L)) (hind : iIndepFun G P)
    (hid : ∀ n, IdentDistrib (G n) (G 0) P P) (k : QuartetKey) (p : Fin 3 → ℝ)
    (hp : ∀ s, P.real {ω | Induces (G 0 ω) (k.quartet s)} = p s) {s₁ s₂ s₃ : Fin 3}
    (h₁₂ : s₁ ≠ s₂) (h₁₃ : s₁ ≠ s₃) (h₂₃ : s₂ ≠ s₃) (hp₂₃ : p s₃ < p s₂) (hp₁₂ : p s₂ ≤ p s₁)
    {t : ℝ} (ht : t < (p s₂ - p s₃) / (p s₂ + p s₃)) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ s,
      (filterBlock t ((geneQuartets (fun i => G i ω) n).map quartetEquiv) k).count (k, s) =
        if s = s₃ then 0 else (geneQuartets (fun i => G i ω) n).count (k.quartet s) := by
  have hp₃ : 0 ≤ p s₃ := by
    rw [← hp]
    exact measureReal_nonneg
  -- the two other topologies are `s₁` and `s₂`
  have hcases : ∀ s, s ≠ s₃ → s = s₁ ∨ s = s₂ :=
    fun s hs => fin_three_cases h₁₂ h₁₃ h₂₃ hs
  -- the test holds for the probabilities of `s₂`, hence of `s₁`, against `s₃`
  have hret₂ : retainSecond t (p s₂) (p s₃) :=
    (retainSecond_iff_ratio t _ _ (by linarith)).2 ht
  have hmin : ∀ s, s ≠ s₃ → p s₃ < p s := by
    intro s hs
    rcases hcases s hs with rfl | rfl
    · linarith
    · exact hp₂₃
  have hret : ∀ s, s ≠ s₃ → retainSecond t (p s) (p s₃) := by
    intro s hs
    rcases hcases s hs with rfl | rfl
    · exact retainSecond_of_le hp₃ hp₂₃ hp₁₂ hret₂
    · exact hret₂
  -- by the strong law, the relative frequencies converge almost surely
  have hconv : ∀ᵐ ω ∂P, ∀ s, Tendsto (fun n : ℕ =>
      ((geneQuartets (fun i => G i ω) n).count (k.quartet s) : ℝ) / n) atTop (𝓝 (p s)) := by
    rw [ae_all_iff]
    intro s
    rw [← hp]
    exact ae_tendsto_frequency G hind hid _
  filter_upwards [hconv] with ω hω
  filter_upwards [eventually_retain_pattern hω hmin hret] with n hn s
  simp only [← frequencies_map] at hn
  rw [filterBlock_count_of_retain hn.1 hn.2 s, count_map_quartetEquiv]

end Coalescent

end Camus
