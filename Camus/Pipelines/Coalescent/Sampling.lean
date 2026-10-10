module

public import Camus.Pipelines.Astral
public import Camus.Pipelines.Coalescent
public import Mathlib.Probability.Independence.InfinitePi

/-!
# Section 3.4: independent gene trees under the multispecies coalescent exist

The theorems on Quartet Filtering under the multispecies coalescent (`Coalescent.msc_filterBlock`,
`Coalescent.msc_filterQuartets`, `Coalescent.msc_filterQuartets_induced`) assume gene trees
`G 0, G 1, …` that are independent (`hind`), identically distributed (`hid`), and distributed as
the unrooted gene tree of the MSC on the species tree `σ` (`hlaw`). This file shows that these
hypotheses can hold together, so that the theorems are not vacuous. The distribution
`σ.unrootedDist id` is a probability measure on the unrooted gene trees (`Coalescent.geneLaw`),
as lean4-adr11 proves (`Coalescent.geneDist_nonneg`, `Coalescent.geneDist_sum`); on the space of
sequences of gene trees with the product law (`Coalescent.genes`, `Measure.infinitePi`), the
coordinates are independent and have that law (`Coalescent.genes_iIndepFun`,
`Coalescent.genes_identDistrib`, `Coalescent.genes_law`). Every well-labelled tree of CAMUS is the
rooted topology of some species tree (`Coalescent.exists_hasTopology`), so the hypothesis
`HasTopology` of `Coalescent.msc_filterQuartets_induced` can be met too
(`Coalescent.msc_filterQuartets_genes`).

## Main results

* `Coalescent.geneLaw`: the law of an unrooted gene tree under the MSC.
* `Coalescent.genes`, `Coalescent.genes_iIndepFun`, `Coalescent.genes_identDistrib`,
  `Coalescent.genes_law`: independent gene trees with that law.
* `Coalescent.exists_hasTopology`: every well-labelled tree is the topology of a species tree.
* `Coalescent.msc_filterQuartets_genes`: Quartet Filtering under the MSC, for these gene trees.
-/

@[expose] public section

namespace Camus

namespace Coalescent

open Finset Filter Topology MeasureTheory ProbabilityTheory ADR11 Algorithm1

variable {L : Finset ℕ}

/-- The probabilities of the unrooted gene trees of the MSC are nonnegative (lean4-adr11's
`ADR11.unrootedDist_nonneg`, with one lineage per taxon). -/
theorem geneDist_nonneg (σ : SpeciesTree L) (T : Finset (Finset L)) :
    0 ≤ σ.unrootedDist id T :=
  unrootedDistOf_nonneg σ.isHierarchy (fun A hA hAu => (σ.length_pos A hA hAu).le) id T

/-- The probabilities of the unrooted gene trees of the MSC sum to 1 (lean4-adr11's
`ADR11.unrootedDist_sum`, with one lineage per taxon). -/
theorem geneDist_sum (σ : SpeciesTree L) : ∑ T, σ.unrootedDist id T = 1 :=
  unrootedDistOf_sum σ.isHierarchy σ.length id

variable [MeasurableSpace (Finset (Finset L))]

/-- The law of the unrooted gene tree of the multispecies coalescent on `σ`, with one lineage per
taxon: the probability measure on the unrooted trees (split sets) with masses
`σ.unrootedDist id`. -/
noncomputable def geneLaw (σ : SpeciesTree L) : Measure (Finset (Finset L)) :=
  (PMF.ofFintype (fun T => ENNReal.ofReal (σ.unrootedDist id T)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg fun T _ => geneDist_nonneg σ T, geneDist_sum σ,
      ENNReal.ofReal_one])).toMeasure

/-- The law of a gene tree is a probability measure. -/
instance (σ : SpeciesTree L) : IsProbabilityMeasure (geneLaw σ) := by
  unfold geneLaw
  infer_instance

/-- Under `geneLaw σ`, the unrooted tree `T` has probability `σ.unrootedDist id T`. -/
theorem geneLaw_real_singleton [MeasurableSingletonClass (Finset (Finset L))]
    (σ : SpeciesTree L) (T : Finset (Finset L)) :
    (geneLaw σ).real {T} = σ.unrootedDist id T := by
  rw [measureReal_def, geneLaw, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton T),
    PMF.ofFintype_apply, ENNReal.toReal_ofReal (geneDist_nonneg σ T)]

/-- Independent gene trees under the MSC on `σ`: the product law on the sequences of unrooted
gene trees (`Measure.infinitePi`), under which the coordinates are the gene trees. -/
noncomputable def genes (σ : SpeciesTree L) : Measure (ℕ → Finset (Finset L)) :=
  Measure.infinitePi fun _ => geneLaw σ

/-- The law of independent gene trees is a probability measure. -/
instance (σ : SpeciesTree L) : IsProbabilityMeasure (genes σ) := by
  unfold genes
  infer_instance

/-- Under `genes σ`, the gene trees are independent. -/
theorem genes_iIndepFun (σ : SpeciesTree L) :
    iIndepFun (fun n (ω : ℕ → Finset (Finset L)) => ω n) (genes σ) :=
  iIndepFun_infinitePi (P := fun _ => geneLaw σ) (X := fun _ => id) fun _ => measurable_id

/-- Under `genes σ`, each gene tree has the law `geneLaw σ`. -/
theorem genes_map (σ : SpeciesTree L) (n : ℕ) :
    (genes σ).map (fun ω => ω n) = geneLaw σ :=
  Measure.infinitePi_map_eval _ n

/-- Under `genes σ`, the gene trees are identically distributed. -/
theorem genes_identDistrib (σ : SpeciesTree L) (n : ℕ) :
    IdentDistrib (fun ω : ℕ → Finset (Finset L) => ω n) (fun ω => ω 0) (genes σ) (genes σ) where
  aemeasurable_fst := (measurable_pi_apply n).aemeasurable
  aemeasurable_snd := (measurable_pi_apply 0).aemeasurable
  map_eq := by rw [genes_map, genes_map]

/-- Under `genes σ`, the first gene tree has the law of the MSC on `σ`: the hypothesis `hlaw` of
`Coalescent.msc_filterQuartets`. -/
theorem genes_law [MeasurableSingletonClass (Finset (Finset L))] (σ : SpeciesTree L)
    (T : Finset (Finset L)) :
    (genes σ).real ((fun ω : ℕ → Finset (Finset L) => ω 0) ⁻¹' {T}) = σ.unrootedDist id T := by
  rw [measureReal_def, ← Measure.map_apply (measurable_pi_apply 0) (measurableSet_singleton T),
    genes_map, ← measureReal_def, geneLaw_real_singleton]

end Coalescent

namespace PhyloTree

/-- Every taxon of `t` is a clade of `t`: the clade of its leaf. -/
theorem singleton_mem_clades (t : PhyloTree) {a : ℕ} (ha : a ∈ t.taxa) : {a} ∈ t.clades := by
  induction t with
  | leaf b =>
    simp only [taxa, labels, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
      Finset.mem_singleton] at ha
    subst ha
    simp [clades]
  | fork l r ihl ihr =>
    simp only [taxa, labels, List.toFinset_append, Finset.mem_union] at ha
    simp only [clades, List.mem_cons, List.mem_append]
    rcases ha with ha | ha
    · exact Or.inr (Or.inl (ihl (List.mem_toFinset.mpr (List.mem_toFinset.mp ha))))
    · exact Or.inr (Or.inr (ihr (List.mem_toFinset.mpr (List.mem_toFinset.mp ha))))

/-- The clades of `t` are nonempty. -/
theorem clade_nonempty (t : PhyloTree) : ∀ C ∈ t.clades, C.Nonempty := by
  induction t with
  | leaf b =>
    intro C hC
    simp only [clades, List.mem_singleton] at hC
    subst hC
    exact Finset.singleton_nonempty b
  | fork l r ihl ihr =>
    intro C hC
    simp only [clades, List.mem_cons, List.mem_append] at hC
    rcases hC with rfl | hC | hC
    · obtain ⟨a, ha⟩ := ihl l.taxa (taxa_mem_clades l)
      exact ⟨a, Finset.mem_union_left _ ha⟩
    · exact ihl C hC
    · exact ihr C hC

end PhyloTree

namespace Coalescent

open Finset Filter Topology MeasureTheory ADR11 Algorithm1

/-- The species tree whose clusters are the clades of the well-labelled tree `t`, as sets of taxa
of `t`, with all edge lengths 1. -/
noncomputable def speciesTreeOf (t : PhyloTree) (ht : t.WellLabelled) : SpeciesTree t.taxa where
  clusters := (t.clades.map fun C => C.subtype (· ∈ t.taxa)).toFinset
  univ_mem := by
    refine List.mem_toFinset.mpr (List.mem_map.mpr ⟨t.taxa, t.taxa_mem_clades, ?_⟩)
    ext x
    simp
  singleton_mem x := by
    refine List.mem_toFinset.mpr (List.mem_map.mpr ⟨{x.1}, t.singleton_mem_clades x.2, ?_⟩)
    ext y
    rw [Finset.mem_subtype, Finset.mem_singleton, Finset.mem_singleton, Subtype.ext_iff]
  nonempty_of_mem A hA := by
    obtain ⟨C, hC, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hA)
    obtain ⟨a, ha⟩ := t.clade_nonempty C hC
    exact ⟨⟨a, t.clade_subset_taxa C hC ha⟩, by simpa using ha⟩
  laminar A hA B hB := by
    obtain ⟨C, hC, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hA)
    obtain ⟨D, hD, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hB)
    rcases t.clades_laminar ht C hC D hD with h | h | h
    · exact Or.inl (Finset.subtype_mono h)
    · exact Or.inr (Or.inl (Finset.subtype_mono h))
    · refine Or.inr (Or.inr (Finset.disjoint_left.mpr fun x hx hx' => ?_))
      exact Finset.disjoint_left.mp h (Finset.mem_subtype.mp hx) (Finset.mem_subtype.mp hx')
  length _ := 1
  length_pos _ _ _ := one_pos

/-- Every well-labelled tree of CAMUS is the rooted topology of a species tree: of
`speciesTreeOf t`, whose clusters are its clades. So the hypothesis `HasTopology` of
`Coalescent.msc_filterQuartets_induced` can be met. -/
theorem exists_hasTopology (t : PhyloTree) (ht : t.WellLabelled) :
    ∃ σ : SpeciesTree t.taxa, HasTopology σ t := by
  refine ⟨speciesTreeOf t ht, fun C => ⟨fun hC => ?_, ?_⟩⟩
  · refine ⟨C.subtype (· ∈ t.taxa), List.mem_toFinset.mpr (List.mem_map.mpr ⟨C, hC, rfl⟩), ?_⟩
    exact Finset.subtype_map_of_mem fun x hx => t.clade_subset_taxa C hC hx
  · rintro ⟨A, hA, rfl⟩
    obtain ⟨D, hD, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hA)
    rwa [Finset.subtype_map_of_mem fun x hx => t.clade_subset_taxa D hD hx]

/-- Section 3.4, Quartet Filtering under the MSC, for gene trees that exist: for every
well-labelled tree `t` there is a species tree with rooted topology `t` such that, for independent
gene trees with the law of the MSC on it (`genes`), for every threshold `τ > 0`, almost surely, for
all large numbers `n` of genes, Algorithm 1 applied to the quartet trees of the first `n` gene
trees returns exactly those in Q(t). The hypotheses of `Coalescent.msc_filterQuartets_induced` hold
together. -/
theorem msc_filterQuartets_genes (t : PhyloTree) (ht : t.WellLabelled)
    [MeasurableSpace (Finset (Finset t.taxa))] [MeasurableSingletonClass (Finset (Finset t.taxa))]
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ σ : SpeciesTree t.taxa, HasTopology σ t ∧
      ∀ᵐ ω ∂(genes σ), ∀ᶠ n in atTop,
        filterQuartets τ (geneQuartets (fun i => ω i) n) =
          (geneQuartets (fun i => ω i) n).filter fun q => q.induced t = true := by
  obtain ⟨σ, hσ⟩ := exists_hasTopology t ht
  have h := msc_filterQuartets_induced hσ
    (fun n (ω : ℕ → Finset (Finset t.taxa)) => ω n) (genes_iIndepFun σ) (genes_identDistrib σ)
    (genes_law σ) hτ
  exact ⟨σ, hσ, h⟩

end Coalescent

end Camus
