module

public import Camus.Pipelines.Algorithm1
public import ADR11.Identifiability.Proposition3
public import ADR11.MSC.Marginal

/-!
# Section 3.3: quartet trees of gene trees under the multispecies coalescent

Section 3.3 motivates Algorithm 1 by "the multi-species coalescent (MSC) model (Takahata 1989)
under which, for every four species, the most probable quartet tree matches the species tree and
the other two quartet trees have the same lower probability". This file proves this statement for
rooted binary species trees, from the MSC of lean4-adr11 (a formalization of Allman, Degnan and
Rhodes 2011), and states it with the quartet trees of CAMUS (`msc_pattern`).

## Representation

The taxa form a finite set `L` of labels, natural numbers as in CAMUS. A species tree is an
`ADR11.SpeciesTree L`: its clusters, with a positive length on every edge. A gene tree is an
unrooted tree on `L` in the representation of ADR11, the set `T : Finset (Finset L)` of the sides
of its splits; under the MSC with one lineage per taxon it has probability `σ.unrootedDist id T`.
A quartet tree of CAMUS on the taxa `a < b < c < d` has the topology `split`: `0` is ab|cd, `1` is
ac|bd, `2` is ad|bc. The gene tree `T` induces the quartet tree `q` (`Induces T q`) when a side of
a split of `T` meets `{a, b, c, d}` in a side of `q`: `Quartet.induced`, with splits in place of
clades. The four taxa of a key `k` (`QuartetKey`), relabelled `0, 1, 2, 3` in increasing order
(`keyTaxon`), give the quartet species tree `quartetSpeciesTree σ k` on `Fin 4`, and the topology
`s` is the unrooted tree of ADR11 on `Fin 4` with the split `side s | (side s)ᶜ`,
`side s = {0, s + 1}`: `treeOfClusters {{0, 1}}` is AB|CD, `treeOfClusters {{0, 2}}` is AC|BD and
`treeOfClusters {{0, 3}}` is AD|BC (`treeOfClusters_side`).

## Main results

* `Coalescent.Induces`, `Coalescent.quartetProb`: a gene tree induces a quartet tree, and the
  probability of that event under the MSC.
* `Coalescent.quartetSpeciesTree`: the species tree that `σ` induces on four taxa, on `Fin 4`.
* `Coalescent.quartetProb_eq`: the probability that a gene tree induces the topology `s` on four
  taxa is the probability of the quartet tree `treeOfClusters {side s}` under the MSC on the
  quartet species tree.
* `Coalescent.induces_species_iff`, `Coalescent.existsUnique_species`: the species tree induces
  the topology `s` iff `side s` is the split of the quartet species tree; a binary species tree
  induces exactly one topology on four taxa.
* `Coalescent.quartetProb_species`, `Coalescent.quartetProb_other`: the probabilities
  `1 − (2/3) e^{−x}` and `(1/3) e^{−x}`, where `x > 0` is the length of the internal edge of the
  quartet species tree.
* `Coalescent.msc_pattern`: Section 3.3's description of the MSC.

## Proof

The paper cites the MSC for this description. The proof here uses Allman, Degnan and Rhodes. The
topology that a gene tree induces on four taxa depends only on its quartet tree on them, the
restriction of its splits to the four taxa (`induces_iff`). That quartet tree is distributed as the
gene tree of the MSC on the quartet species tree (`quartetSpeciesTree_unrootedDist`): this is
their Lemma 5 (marginalization), from ADR11's dropping of lineages
(`ADR11.SpeciesTree.unrootedDist_comp_embedding`) and pruning of the species tree
(`ADR11.SpeciesTree.rootedDist_restrict`), with a relabelling. The quartet species tree of a binary
species tree is binary (`ADR11.SpeciesTree.restrict_isBinary`), so its unrooted topology has one
nontrivial split, the topology of `σ` on the four taxa (`existsUnique_species`), and the formulas of
their Section 4.1 (`ADR11.four_unrootedDist_of_mem`, `ADR11.four_unrootedDist_of_ne_of_isBinary`)
give the probabilities `1 − (2/3) e^{−x}` for it and `(1/3) e^{−x}` for each other topology.
-/

@[expose] public section

namespace Camus

namespace Coalescent

open Finset ADR11 Real

variable {L : Finset ℕ}

/-- The labels of the taxa `L`: the inclusion `L ↪ ℕ`. -/
abbrev label (L : Finset ℕ) : L ↪ ℕ := Function.Embedding.subtype (· ∈ L)

/-- Section 3.3: the unrooted gene tree `T` on the taxa `L`, given as in ADR11 by the sides of its
splits, induces the quartet tree `q`: the taxa of `q` are taxa of `L`, and some side of a split of
`T` meets them in one side of `q` (`Quartet.cutBy`), so that deleting the edge of that split
separates the two sides of `q`. -/
def Induces (T : Finset (Finset L)) (q : Quartet) : Prop :=
  q.taxa ⊆ L ∧ ∃ A ∈ T, q.cutBy (A.map (label L)) = true

/-- Whether a gene tree induces a quartet tree is decidable. -/
instance (T : Finset (Finset L)) (q : Quartet) : Decidable (Induces T q) := by
  unfold Induces
  infer_instance

/-- Section 3.3: the probability that the unrooted gene tree of the multispecies coalescent on the
species tree `σ`, with one lineage per taxon, induces the quartet tree `q`. -/
noncomputable def quartetProb (σ : SpeciesTree L) (q : Quartet) : ℝ :=
  ∑ T, if Induces T q then σ.unrootedDist id T else 0

/-! ### The four taxa of a key -/

/-- The four taxa `{a, b, c, d}` of the key `k`. -/
def keyTaxa (k : QuartetKey) : Finset ℕ := {k.a, k.b, k.c, k.d}

/-- The three quartet trees on the key `k` have the four taxa of `k`. -/
theorem taxa_quartet (k : QuartetKey) (s : Fin 3) : (k.quartet s).taxa = keyTaxa k := rfl

/-- The labels `a, b, c, d` of the key `k`, in increasing order. -/
def keyLabel (k : QuartetKey) : Fin 4 → ℕ := ![k.a, k.b, k.c, k.d]

/-- The four labels of a key are distinct. -/
theorem keyLabel_injective (k : QuartetKey) : Function.Injective (keyLabel k) := by
  have hab := k.ab
  have hbc := k.bc
  have hcd := k.cd
  intro i j h
  fin_cases i <;> fin_cases j <;> simp [keyLabel] at h ⊢ <;> omega

/-- The labels of a key are its taxa. -/
theorem keyLabel_mem (k : QuartetKey) (i : Fin 4) : keyLabel k i ∈ keyTaxa k := by
  fin_cases i <;> simp [keyLabel, keyTaxa]

/-- The four taxa `a, b, c, d` of the key `k`, as taxa of `L`, indexed by `0, 1, 2, 3` in
increasing order of their labels. -/
def keyTaxon (k : QuartetKey) (hk : keyTaxa k ⊆ L) : Fin 4 ↪ L where
  toFun i := ⟨keyLabel k i, hk (keyLabel_mem k i)⟩
  inj' _ _ h := keyLabel_injective k (congrArg Subtype.val h)

/-- The four taxa of the key `k`, as a set of taxa of `L`. -/
def keySet (k : QuartetKey) (hk : keyTaxa k ⊆ L) : Finset L := univ.map (keyTaxon k hk)

/-- The four taxa of a key form a nonempty set. -/
theorem keySet_nonempty (k : QuartetKey) (hk : keyTaxa k ⊆ L) : (keySet k hk).Nonempty :=
  ⟨keyTaxon k hk 0, mem_map_of_mem _ (mem_univ 0)⟩

/-- The labelling `0, 1, 2, 3` of the four taxa of `k`. -/
noncomputable def keyEquiv (k : QuartetKey) (hk : keyTaxa k ⊆ L) : Fin 4 ≃ keySet k hk :=
  Equiv.ofBijective (fun i => ⟨keyTaxon k hk i, mem_map_of_mem _ (mem_univ i)⟩)
    ⟨fun _ _ h => (keyTaxon k hk).injective (congrArg Subtype.val h), fun ⟨y, hy⟩ => by
      obtain ⟨i, -, rfl⟩ := mem_map.1 hy
      exact ⟨i, rfl⟩⟩

/-- The taxon labelled `i` by `keyEquiv` is `keyTaxon k hk i`. -/
theorem keyEquiv_apply (k : QuartetKey) (hk : keyTaxa k ⊆ L) (i : Fin 4) :
    ((keyEquiv k hk i : keySet k hk) : L) = keyTaxon k hk i := rfl

/-! ### Quartet trees on `Fin 4` -/

/-- The side `{0, s + 1}` of the split of the topology `s` on the four taxa `0, 1, 2, 3`: the
topologies `0, 1, 2` of CAMUS are AB|CD, AC|BD and AD|BC. -/
def side (s : Fin 3) : Finset (Fin 4) := {0, s.succ}

/-- Each side has two of the four taxa. -/
theorem side_card : ∀ s : Fin 3, #(side s) = 2 := by decide

/-- Distinct topologies have distinct splits. -/
theorem side_ne : ∀ s s' : Fin 3, s ≠ s' → side s ≠ side s' ∧ side s ≠ (side s')ᶜ := by decide

/-- Every pair of the four taxa is a side of the split of one of the three topologies. -/
theorem exists_side : ∀ A : Finset (Fin 4), #A = 2 → ∃ s, A = side s ∨ A = (side s)ᶜ := by decide

/-- The two sides of each split are nonempty. -/
theorem side_nonempty : ∀ s : Fin 3, (side s).Nonempty ∧ (side s)ᶜ.Nonempty := by decide

/-- On `Fin 4`, the quartet tree `treeOfClusters {side s'}` has a side `side s` or its complement
iff `s = s'`. -/
theorem side_mem_treeOfClusters : ∀ s s' : Fin 3,
    side s ∈ treeOfClusters {side s'} ∨ (side s)ᶜ ∈ treeOfClusters {side s'} ↔ s = s' := by
  decide

/-- The three quartet trees of ADR11 on `Fin 4` are those of the three topologies. -/
theorem treeOfClusters_side : treeOfClusters {side 0} = treeOfClusters {{0, 1}} ∧
    treeOfClusters {side 1} = treeOfClusters {{0, 2}} ∧
    treeOfClusters {side 2} = treeOfClusters {{0, 3}} := by
  decide

/-! ### The quartet tree of a gene tree -/

section Bridge

variable (k : QuartetKey) (hk : keyTaxa k ⊆ L)

/-- The sides of the topology `s` on the taxa of `k` are the labels of `side s` and of its
complement. -/
theorem sides_quartet (s : Fin 3) :
    (k.quartet s).sides = ((side s).image (keyLabel k), (side s)ᶜ.image (keyLabel k)) := by
  have hc : ∀ s : Fin 3,
      (side s)ᶜ = if s = 0 then {2, 3} else if s = 1 then {1, 3} else {1, 2} := by
    decide
  rw [hc s]
  fin_cases s <;> simp [Quartet.sides, QuartetKey.quartet, side, keyLabel, Finset.image_insert]

/-- A taxon of `k` belongs to a set `A` of taxa iff its label belongs to the labels of `A`. -/
theorem keyLabel_mem_map_iff (A : Finset L) (i : Fin 4) :
    keyLabel k i ∈ A.map (label L) ↔ keyTaxon k hk i ∈ A := by
  rw [mem_map]
  constructor
  · rintro ⟨a, ha, h⟩
    have : a = keyTaxon k hk i := Subtype.ext h
    rwa [← this]
  · intro h
    exact ⟨_, h, rfl⟩

/-- The labels of the taxa `I` of `k` are labels of taxa of `A` iff `I` is contained in the pattern
of `A` on the four taxa, the set of the indices `i` with `keyTaxon k hk i ∈ A`. -/
theorem image_subset_map_iff (A : Finset L) (I : Finset (Fin 4)) :
    I.image (keyLabel k) ⊆ A.map (label L) ↔ I ⊆ univ.filter fun i => keyTaxon k hk i ∈ A := by
  rw [image_subset_iff]
  simp only [subset_iff, mem_filter, mem_univ, true_and, keyLabel_mem_map_iff k hk]

/-- The labels of the taxa `I` of `k` avoid the labels of the taxa of `A` iff `I` avoids the
pattern of `A` on the four taxa. -/
theorem disjoint_image_map_iff (A : Finset L) (I : Finset (Fin 4)) :
    Disjoint (I.image (keyLabel k)) (A.map (label L)) ↔
      Disjoint I (univ.filter fun i => keyTaxon k hk i ∈ A) := by
  simp only [disjoint_left, forall_mem_image, mem_filter, mem_univ, true_and,
    keyLabel_mem_map_iff k hk]

/-- `D` contains `C` and avoids its complement iff `D = C`. -/
theorem subset_and_disjoint_compl_iff {α : Type*} [Fintype α] [DecidableEq α] (C D : Finset α) :
    C ⊆ D ∧ Disjoint Cᶜ D ↔ D = C := by
  constructor
  · rintro ⟨h1, h2⟩
    refine Subset.antisymm (fun i hi => ?_) h1
    by_contra hc
    exact disjoint_left.1 h2 (mem_compl.2 hc) hi
  · rintro rfl
    exact ⟨Subset.rfl, disjoint_compl_left⟩

/-- `D` contains the complement of `C` and avoids `C` iff `D = Cᶜ`. -/
theorem compl_subset_and_disjoint_iff {α : Type*} [Fintype α] [DecidableEq α] (C D : Finset α) :
    Cᶜ ⊆ D ∧ Disjoint C D ↔ D = Cᶜ := by
  have h := subset_and_disjoint_compl_iff Cᶜ D
  rwa [compl_compl] at h

/-- A set `A` of taxa cuts the topology `s` on the four taxa of `k` iff its pattern on them, the set
of the indices `i` with `keyTaxon k hk i ∈ A`, is `side s` or its complement. -/
theorem cutBy_iff (A : Finset L) (s : Fin 3) :
    (k.quartet s).cutBy (A.map (label L)) = true ↔
      (univ.filter fun i => keyTaxon k hk i ∈ A) = side s ∨
        (univ.filter fun i => keyTaxon k hk i ∈ A) = (side s)ᶜ := by
  simp only [Quartet.cutBy, decide_eq_true_eq, sides_quartet, image_subset_map_iff k hk,
    disjoint_image_map_iff k hk, subset_and_disjoint_compl_iff, compl_subset_and_disjoint_iff]

/-- A side `C` of a split of `Fin 4` is in the quartet tree that `T` induces on the four taxa
(`restrictUnrooted`) iff it is the trace of a side of a split of `T`. -/
theorem mem_restrictUnrooted_iff (T : Finset (Finset L)) {C : Finset (Fin 4)}
    (hC : C.Nonempty) (hC' : Cᶜ.Nonempty) :
    C ∈ restrictUnrooted (keyTaxon k hk) T ↔
      ∃ A ∈ T, (univ.filter fun i => keyTaxon k hk i ∈ A) = C := by
  unfold restrictUnrooted
  simp only [mem_image, mem_filter]
  constructor
  · rintro ⟨A, ⟨hA, -⟩, hAC⟩
    exact ⟨A, hA, hAC⟩
  · rintro ⟨A, hA, hAC⟩
    refine ⟨A, ⟨hA, ?_, ?_⟩, hAC⟩
    · obtain ⟨i, hi⟩ := hC
      rw [← hAC, mem_filter] at hi
      exact ⟨i, hi.2⟩
    · obtain ⟨i, hi⟩ := hC'
      rw [← hAC, mem_compl, mem_filter] at hi
      exact ⟨i, fun h => hi ⟨mem_univ i, h⟩⟩

/-- The topology that a gene tree `T` induces on the four taxa of `k` depends only on its quartet
tree on them: `T` induces the topology `s` iff the restriction of `T` to the four taxa
(`restrictUnrooted`, on `Fin 4`) has the split `side s | (side s)ᶜ`. -/
theorem induces_iff (T : Finset (Finset L)) (s : Fin 3) :
    Induces T (k.quartet s) ↔
      side s ∈ restrictUnrooted (keyTaxon k hk) T ∨
        (side s)ᶜ ∈ restrictUnrooted (keyTaxon k hk) T := by
  obtain ⟨h1, h2⟩ := side_nonempty s
  rw [mem_restrictUnrooted_iff k hk T h1 h2,
    mem_restrictUnrooted_iff k hk T h2 (by rwa [compl_compl]), Induces, taxa_quartet]
  simp only [hk, true_and, cutBy_iff k hk]
  constructor
  · rintro ⟨A, hA, h | h⟩
    · exact Or.inl ⟨A, hA, h⟩
    · exact Or.inr ⟨A, hA, h⟩
  · rintro (⟨A, hA, h⟩ | ⟨A, hA, h⟩)
    · exact ⟨A, hA, Or.inl h⟩
    · exact ⟨A, hA, Or.inr h⟩

end Bridge

/-! ### The species tree induced on four taxa -/

/-- The quartet species tree of `σ` on the four taxa of `k`: the species tree `σ(S)` that `σ`
induces on `S = {a, b, c, d}` (ADR11's `SpeciesTree.restrict`: the clusters are the traces of
the clusters of `σ`, and each edge has the total length of the edges of `σ` with the same trace),
with `a, b, c, d` relabelled `0, 1, 2, 3`. -/
noncomputable def quartetSpeciesTree (σ : SpeciesTree L) (k : QuartetKey) (hk : keyTaxa k ⊆ L) :
    SpeciesTree (Fin 4) :=
  (σ.restrict (keySet k hk) (keySet_nonempty k hk)).relabel (keyEquiv k hk).symm

/-- The clusters of the quartet species tree are the traces of the clusters of `σ` on the four
taxa. -/
theorem quartetSpeciesTree_clusters (σ : SpeciesTree L) (k : QuartetKey) (hk : keyTaxa k ⊆ L) :
    (quartetSpeciesTree σ k hk).clusters = restrictForest (keyTaxon k hk) σ.clusters := by
  simp only [quartetSpeciesTree, SpeciesTree.relabel_clusters, SpeciesTree.restrict_clusters,
    relabelFamily, restrictClusters, restrictForest, image_image]
  have hfilter : σ.clusters.filter (fun A => (A ∩ keySet k hk).Nonempty) =
      σ.clusters.filter (fun A => ∃ l, keyTaxon k hk l ∈ A) := by
    refine filter_congr fun A _ => ?_
    constructor
    · rintro ⟨y, hy⟩
      rw [mem_inter] at hy
      obtain ⟨l, -, rfl⟩ := mem_map.1 hy.2
      exact ⟨l, hy.1⟩
    · rintro ⟨l, hl⟩
      exact ⟨keyTaxon k hk l, mem_inter.2 ⟨hl, mem_map_of_mem _ (mem_univ l)⟩⟩
  rw [hfilter]
  congr 1
  · funext A
    ext i
    simp only [Function.comp_apply, mem_map_equiv, Equiv.symm_symm, mem_subtype, mem_filter,
      mem_univ, true_and, keyEquiv_apply]
  · ext A
    simp only [mem_filter]

/-- The unrooted topology of the quartet species tree is the restriction of the unrooted topology
of `σ` to the four taxa. -/
theorem unroot_quartetSpeciesTree (σ : SpeciesTree L) (k : QuartetKey) (hk : keyTaxa k ⊆ L) :
    unroot (quartetSpeciesTree σ k hk).clusters =
      restrictUnrooted (keyTaxon k hk) (unroot σ.clusters) := by
  rw [quartetSpeciesTree_clusters]
  exact unroot_restrictForest _

/-- The rooted gene trees of the MSC on the quartet species tree are distributed as the rooted
gene trees of the MSC on `σ` with one lineage sampled from each of the four taxa: pruning the
species tree (`SpeciesTree.rootedDist_restrict`) and relabelling (`forestDist_relabel`). -/
theorem quartetSpeciesTree_rootedDist (σ : SpeciesTree L) (k : QuartetKey) (hk : keyTaxa k ⊆ L)
    (G : Finset (Finset (Fin 4))) :
    (quartetSpeciesTree σ k hk).rootedDist id G = σ.rootedDist (keyTaxon k hk) G := by
  have h := forestDist_relabel (keyEquiv k hk).symm (Equiv.refl (Fin 4))
    (σ.restrict (keySet k hk) (keySet_nonempty k hk)).clusters
    (len' := (quartetSpeciesTree σ k hk).length)
    (fun A => SpeciesTree.relabel_length_map _ (keyEquiv k hk).symm A)
    (s := keyEquiv k hk) (s' := id) (fun l => by simp) univ G
  rw [relabelFamily_refl, Finset.map_univ_equiv] at h
  calc (quartetSpeciesTree σ k hk).rootedDist id G
      = (σ.restrict (keySet k hk) (keySet_nonempty k hk)).rootedDist (keyEquiv k hk) G := h
    _ = σ.rootedDist (keyTaxon k hk) G := σ.rootedDist_restrict _ _ _ G

/-- Marginalization: the quartet tree that the gene tree of the MSC on `σ` induces on the four
taxa of `k` (`restrictUnrooted`) is distributed as the gene tree of the MSC on the quartet species
tree. This is Lemma 5 of Allman, Degnan and Rhodes, with the four taxa relabelled `0, 1, 2, 3`. -/
theorem quartetSpeciesTree_unrootedDist (σ : SpeciesTree L) (k : QuartetKey)
    (hk : keyTaxa k ⊆ L) (T' : Finset (Finset (Fin 4))) :
    (quartetSpeciesTree σ k hk).unrootedDist id T' =
      ∑ T, if restrictUnrooted (keyTaxon k hk) T = T' then σ.unrootedDist id T else 0 := by
  rw [← σ.unrootedDist_comp_embedding id (keyTaxon k hk) T']
  unfold SpeciesTree.unrootedDist
  simp_rw [quartetSpeciesTree_rootedDist]
  rfl

/-- The species tree induces the topology `s` on the four taxa of `k` iff `side s | (side s)ᶜ` is
the split of the quartet species tree. -/
theorem induces_species_iff (σ : SpeciesTree L) (k : QuartetKey) (hk : keyTaxa k ⊆ L)
    (s : Fin 3) :
    Induces (unroot σ.clusters) (k.quartet s) ↔
      side s ∈ unroot (quartetSpeciesTree σ k hk).clusters := by
  rw [induces_iff k hk, ← unroot_quartetSpeciesTree, compl_mem_unroot, or_self]

/-- The quartet species tree of a binary species tree is binary. -/
theorem quartetSpeciesTree_isBinary {σ : SpeciesTree L} (hσ : σ.IsBinary) (k : QuartetKey)
    (hk : keyTaxa k ⊆ L) : (quartetSpeciesTree σ k hk).IsBinary :=
  (SpeciesTree.isBinary_relabel_iff _ _).2 (SpeciesTree.restrict_isBinary hσ _ _)

/-! ### The probabilities of the three topologies -/

/-- Regrouping a sum over gene trees by their image under `R`. -/
theorem sum_ite_comp {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] (R : α → β)
    (P : β → Prop) [DecidablePred P] (μ : α → ℝ) :
    ∑ a, (if P (R a) then μ a else 0) =
      ∑ b, if P b then ∑ a, (if R a = b then μ a else 0) else 0 := by
  rw [← Finset.sum_fiberwise univ R]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_filter]
  split_ifs with hb
  · refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : R a = b
    · rw [ite_eq_left ha, ite_eq_left ha, ite_eq_left (ha ▸ hb)]
    · rw [ite_eq_right ha, ite_eq_right ha]
  · refine Finset.sum_eq_zero fun a _ => ?_
    by_cases ha : R a = b
    · rw [ite_eq_left ha, ite_eq_right (ha ▸ hb)]
    · rw [ite_eq_right ha]

/-- The bridge to the quartet trees of ADR11. The probability that the gene tree of the MSC on `σ`
induces the topology `s` on the four taxa `a < b < c < d` of `k` is the probability of the quartet
tree `treeOfClusters {side s}` (AB|CD, AC|BD, AD|BC for `s = 0, 1, 2`) under the MSC on the quartet
species tree. -/
theorem quartetProb_eq (σ : SpeciesTree L) (k : QuartetKey) (hk : keyTaxa k ⊆ L) (s : Fin 3) :
    quartetProb σ (k.quartet s) =
      (quartetSpeciesTree σ k hk).unrootedDist id (treeOfClusters {side s}) := by
  -- regroup the gene trees by their quartet tree on the four taxa (marginalization)
  have hregroup : quartetProb σ (k.quartet s) = ∑ T', if side s ∈ T' ∨ (side s)ᶜ ∈ T' then
      (quartetSpeciesTree σ k hk).unrootedDist id T' else 0 := by
    simp_rw [quartetSpeciesTree_unrootedDist]
    unfold quartetProb
    simp_rw [induces_iff k hk]
    exact sum_ite_comp (restrictUnrooted (keyTaxon k hk)) (fun T' => side s ∈ T' ∨ (side s)ᶜ ∈ T')
      (σ.unrootedDist id)
  rw [hregroup]
  -- only the three quartet trees have positive probability, and only one has the split of `s`
  refine (Finset.sum_eq_single (treeOfClusters {side s}) (fun T' _ hT' => ?_)
    (fun h => absurd (mem_univ _) h)).trans ?_
  · split_ifs with hP
    · have hne : ∀ s', T' ≠ treeOfClusters {side s'} := by
        rintro s' rfl
        exact hT' (by rw [(side_mem_treeOfClusters s s').1 hP])
      obtain ⟨e0, e1, e2⟩ := treeOfClusters_side
      exact unrootedDist_eq_zero_four _ T' ⟨e0 ▸ hne 0, e1 ▸ hne 1, e2 ▸ hne 2⟩
    · rfl
  · rw [ite_eq_left ((side_mem_treeOfClusters s s).2 rfl)]

/-! ### The pattern of the multispecies coalescent -/

/-- A binary species tree induces exactly one topology on every four of its taxa. -/
theorem existsUnique_species {σ : SpeciesTree L} (hσ : σ.IsBinary) (k : QuartetKey)
    (hk : keyTaxa k ⊆ L) : ∃! s, Induces (unroot σ.clusters) (k.quartet s) := by
  have hτ := quartetSpeciesTree_isBinary hσ k hk
  have hX : Fintype.card (Fin 4) = 4 := Fintype.card_fin 4
  -- the binary quartet species tree has a nontrivial split `A | Aᶜ` with `#A = 2`
  obtain ⟨A, hA, hA2⟩ := f1_exists_split_of_isBinary hX _ hτ
  obtain ⟨s, hs⟩ := exists_side A hA2
  have hside : side s ∈ unroot (quartetSpeciesTree σ k hk).clusters := by
    rcases hs with rfl | rfl
    · exact hA
    · exact compl_mem_unroot.1 hA
  refine ⟨s, (induces_species_iff σ k hk s).2 hside, fun s' hs' => ?_⟩
  -- and no other: a nontrivial split on four taxa is the only one
  by_contra hne
  have h := (f1_mem_unroot_iff_of_split hX _ hside (side_card s) (side s')).1
    ((induces_species_iff σ k hk s').1 hs')
  obtain ⟨h1, h2⟩ := side_ne s' s hne
  rcases h with h | h | h | h
  · rw [side_card] at h
    omega
  · rw [side_card] at h
    omega
  · exact h1 h
  · exact h2 h

/-- The internal edge of the quartet species tree, with the split of the topology `s` induced by
`σ`, has positive length. -/
theorem unrootedLength_side_pos (σ : SpeciesTree L) (k : QuartetKey) (hk : keyTaxa k ⊆ L)
    {s : Fin 3} (hs : Induces (unroot σ.clusters) (k.quartet s)) :
    0 < (quartetSpeciesTree σ k hk).unrootedLength (side s) :=
  four_unrootedLength_pos _ ((induces_species_iff σ k hk s).1 hs)

/-- Section 4.1 of Allman, Degnan and Rhodes, on four taxa of a binary species tree `σ`: the
topology `s` that `σ` induces on the four taxa of `k` has probability `1 − (2/3) e^{−x}`, where `x`
is the length of the internal edge of the quartet species tree. -/
theorem quartetProb_species {σ : SpeciesTree L} (hσ : σ.IsBinary) (k : QuartetKey)
    (hk : keyTaxa k ⊆ L) {s : Fin 3} (hs : Induces (unroot σ.clusters) (k.quartet s)) :
    quartetProb σ (k.quartet s) =
      1 - 2 / 3 * exp (-(quartetSpeciesTree σ k hk).unrootedLength (side s)) := by
  rw [quartetProb_eq σ k hk s]
  exact four_unrootedDist_of_mem (Fintype.card_fin 4) _ (quartetSpeciesTree_isBinary hσ k hk)
    ((induces_species_iff σ k hk s).1 hs) (side_card s)

/-- Section 4.1 of Allman, Degnan and Rhodes, on four taxa of a binary species tree `σ`: each of
the two other topologies on the four taxa of `k` has probability `(1/3) e^{−x}`, where `x` is the
length of the internal edge of the quartet species tree. -/
theorem quartetProb_other {σ : SpeciesTree L} (hσ : σ.IsBinary) (k : QuartetKey)
    (hk : keyTaxa k ⊆ L) {s s' : Fin 3} (hs : Induces (unroot σ.clusters) (k.quartet s))
    (hs' : s' ≠ s) :
    quartetProb σ (k.quartet s') =
      1 / 3 * exp (-(quartetSpeciesTree σ k hk).unrootedLength (side s)) := by
  rw [quartetProb_eq σ k hk s']
  obtain ⟨h1, h2⟩ := side_ne s' s hs'
  exact four_unrootedDist_of_ne_of_isBinary (Fintype.card_fin 4) _
    (quartetSpeciesTree_isBinary hσ k hk) ((induces_species_iff σ k hk s).1 hs) (side_card s)
    (side_card s') h1 h2

/-- The pattern of the MSC on four taxa, for the topology `s` induced by the binary species tree
`σ`: it is strictly the most probable topology, and the two others have the same positive
probability. -/
theorem msc_pattern_of_induces {σ : SpeciesTree L} (hσ : σ.IsBinary) (k : QuartetKey)
    (hk : keyTaxa k ⊆ L) {s : Fin 3} (hs : Induces (unroot σ.clusters) (k.quartet s)) :
    (∀ s', s' ≠ s → quartetProb σ (k.quartet s') < quartetProb σ (k.quartet s)) ∧
      (∀ s' s'', s' ≠ s → s'' ≠ s →
        quartetProb σ (k.quartet s') = quartetProb σ (k.quartet s'')) ∧
      ∀ s', s' ≠ s → 0 < quartetProb σ (k.quartet s') := by
  have hx := unrootedLength_side_pos σ k hk hs
  refine ⟨fun s' hs' => ?_, fun s' s'' hs' hs'' => ?_, fun s' hs' => ?_⟩
  · -- `(1/3) e^{−x} < 1 − (2/3) e^{−x}` since `e^{−x} < 1`
    rw [quartetProb_other hσ k hk hs hs', quartetProb_species hσ k hk hs]
    have : exp (-(quartetSpeciesTree σ k hk).unrootedLength (side s)) < 1 :=
      Real.exp_lt_one_iff.2 (neg_lt_zero.2 hx)
    linarith
  · rw [quartetProb_other hσ k hk hs hs', quartetProb_other hσ k hk hs hs'']
  · rw [quartetProb_other hσ k hk hs hs']
    positivity

/-- Section 3.3: "the multi-species coalescent (MSC) model (Takahata 1989) under which, for
every four species, the most probable quartet tree matches the species tree and the other two
quartet trees have the same lower probability". Under the MSC on a rooted binary species tree `σ`
(with positive edge lengths, as every `ADR11.SpeciesTree`), with one lineage per taxon, on every
four taxa `a < b < c < d` of `σ`, the topology `s` induced by `σ` is strictly the most probable one,
and the two others have the same probability. -/
theorem msc_pattern {σ : SpeciesTree L} (hσ : σ.IsBinary) (k : QuartetKey)
    (hk : keyTaxa k ⊆ L) :
    ∃ s, Induces (unroot σ.clusters) (k.quartet s) ∧
      (∀ s', s' ≠ s → quartetProb σ (k.quartet s') < quartetProb σ (k.quartet s)) ∧
      ∀ s' s'', s' ≠ s → s'' ≠ s →
        quartetProb σ (k.quartet s') = quartetProb σ (k.quartet s'') := by
  obtain ⟨s, hs, -⟩ := existsUnique_species hσ k hk
  obtain ⟨hlt, heq, -⟩ := msc_pattern_of_induces hσ k hk hs
  exact ⟨s, hs, hlt, heq⟩

end Coalescent

end Camus
