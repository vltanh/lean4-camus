module

public import Camus.Pipelines.Coalescent.Quartets

/-!
# The species tree as a tree of CAMUS

A species tree of lean4-adr11 (`ADR11.SpeciesTree L`) carries a rooted topology, its clusters,
and edge lengths. A rooted binary tree of CAMUS (`PhyloTree`) carries a rooted topology, its
clades. This file relates the two: when the clades of `tree` are the clusters of `σ` as sets of
labels (`HasTopology σ tree`), the quartet trees induced by the unrooted topology of `σ`
(`Coalescent.Induces (unroot σ.clusters)`) are the quartet trees of Q(tree) (`Quartet.induced`,
Definition 1), and `σ` is binary.

## Main results

* `Coalescent.HasTopology`: the rooted topology of `σ` is `tree`.
* `Coalescent.induces_iff_induced`: `σ` induces `q` iff `q ∈ Q(tree)`.
* `Coalescent.isBinary_of_hasTopology`: a species tree whose topology is a tree of CAMUS is
  binary.
* `Coalescent.msc_pattern_induced`: Section 3.3's description of the MSC, with Q(tree).
-/

@[expose] public section

namespace Camus

namespace Coalescent

open Finset ADR11

variable {L : Finset ℕ}

/-- The rooted topology of the species tree `σ` is the tree `tree` of CAMUS: the clades of `tree`
are the clusters of `σ`, as sets of labels. -/
def HasTopology (σ : SpeciesTree L) (tree : PhyloTree) : Prop :=
  ∀ C : Finset ℕ, C ∈ tree.clades ↔ ∃ A ∈ σ.clusters, A.map (label L) = C

/-- The taxa of a tree are its first clade. -/
theorem taxa_mem_clades (tree : PhyloTree) : tree.taxa ∈ tree.clades := by
  cases tree with
  | leaf a => simp [PhyloTree.clades, PhyloTree.taxa, PhyloTree.labels]
  | fork l r =>
    simp [PhyloTree.clades, PhyloTree.taxa, PhyloTree.labels, List.toFinset_append]

/-- The clades of a tree are sets of its taxa. -/
theorem subset_taxa_of_mem_clades {tree : PhyloTree} {C : Finset ℕ} (h : C ∈ tree.clades) :
    C ⊆ tree.taxa := by
  induction tree with
  | leaf a =>
    simp only [PhyloTree.clades, List.mem_singleton] at h
    simp [h, PhyloTree.taxa, PhyloTree.labels]
  | fork l r ihl ihr =>
    simp only [PhyloTree.clades, List.mem_cons, List.mem_append] at h
    have htaxa : (PhyloTree.fork l r).taxa = l.taxa ∪ r.taxa := by
      simp [PhyloTree.taxa, PhyloTree.labels, List.toFinset_append]
    rw [htaxa]
    rcases h with rfl | h | h
    · exact Subset.rfl
    · exact (ihl h).trans subset_union_left
    · exact (ihr h).trans subset_union_right

/-- The taxa of the topology of `σ` are the taxa `L` of `σ`. -/
theorem taxa_eq_of_hasTopology {σ : SpeciesTree L} {tree : PhyloTree} (h : HasTopology σ tree) :
    tree.taxa = L := by
  apply Subset.antisymm
  · obtain ⟨A, -, hA⟩ := (h tree.taxa).1 (taxa_mem_clades tree)
    rw [← hA]
    intro n hn
    obtain ⟨a, -, rfl⟩ := mem_map.1 hn
    exact a.2
  · have hu := (h _).2 ⟨univ, σ.univ_mem, rfl⟩
    intro n hn
    exact subset_taxa_of_mem_clades hu (mem_map.2 ⟨⟨n, hn⟩, mem_univ _, rfl⟩)

/-- The pattern of the complement of `A` on the four taxa of `k` is the complement of the pattern
of `A`. -/
theorem pattern_compl (k : QuartetKey) (hk : keyTaxa k ⊆ L) (A : Finset L) :
    (univ.filter fun i => keyTaxon k hk i ∈ Aᶜ) = (univ.filter fun i => keyTaxon k hk i ∈ A)ᶜ := by
  ext i
  simp

/-- A set of taxa and its complement cut the same quartet trees. -/
theorem cutBy_compl_iff (k : QuartetKey) (hk : keyTaxa k ⊆ L) (A : Finset L) (s : Fin 3) :
    (k.quartet s).cutBy (Aᶜ.map (label L)) = true ↔
      (k.quartet s).cutBy (A.map (label L)) = true := by
  rw [cutBy_iff k hk, cutBy_iff k hk, pattern_compl, compl_inj_iff, compl_eq_comm, eq_comm,
    or_comm]

/-- No split has a side containing all four taxa. -/
theorem univ_ne_side : ∀ s : Fin 3, (univ : Finset (Fin 4)) ≠ side s ∧ univ ≠ (side s)ᶜ := by
  decide

/-- The set of all taxa cuts no quartet tree. -/
theorem not_cutBy_univ (k : QuartetKey) (hk : keyTaxa k ⊆ L) (s : Fin 3) :
    (k.quartet s).cutBy ((univ : Finset L).map (label L)) ≠ true := by
  rw [Ne, cutBy_iff k hk]
  have h : (univ.filter fun i => keyTaxon k hk i ∈ (univ : Finset L)) = univ := by
    ext i
    simp
  rw [h]
  exact fun h' => h'.elim (univ_ne_side s).1 (univ_ne_side s).2

/-- The bridge to Definition 1. If the rooted topology of the species tree `σ` is the tree `tree`
of CAMUS, `σ` induces the quartet tree `q` iff `q ∈ Q(tree)`: the splits of the unrooted topology
of `σ` are its non-root clusters and their complements, a set of taxa and its complement cut the
same quartet trees, and the root cluster cuts none. -/
theorem induces_iff_induced {σ : SpeciesTree L} {tree : PhyloTree} (h : HasTopology σ tree)
    (q : Quartet) : Induces (unroot σ.clusters) q ↔ q.induced tree = true := by
  have htaxa := taxa_eq_of_hasTopology h
  simp only [Quartet.induced, Bool.and_eq_true, decide_eq_true_eq, htaxa, List.any_eq_true]
  by_cases hq : q.taxa ⊆ L
  · simp only [Induces, hq, true_and]
    have hk : keyTaxa q.key ⊆ L := hq
    have hqk : q.key.quartet q.split = q := rfl
    constructor
    · -- a side of a split of `σ` cutting `q` is a non-root cluster or the complement of one
      rintro ⟨A, hA, hcut⟩
      rcases mem_unroot.1 hA with ⟨hA, -⟩ | ⟨hA, -⟩
      · exact ⟨_, (h _).2 ⟨A, hA, rfl⟩, hcut⟩
      · refine ⟨_, (h _).2 ⟨Aᶜ, hA, rfl⟩, ?_⟩
        rw [← hqk] at hcut ⊢
        exact (cutBy_compl_iff q.key hk A q.split).2 hcut
    · -- a clade cutting `q` is a non-root cluster
      rintro ⟨C, hC, hcut⟩
      obtain ⟨A, hA, rfl⟩ := (h C).1 hC
      refine ⟨A, mem_unroot.2 (Or.inl ⟨hA, fun hAu => ?_⟩), hcut⟩
      rw [hAu, ← hqk] at hcut
      exact not_cutBy_univ q.key hk q.split hcut
  · simp only [Induces, hq, false_and]

/-- Every clade with at least two taxa of a tree whose clades are nested or disjoint is the
disjoint union of two clades. -/
theorem exists_disjoint_clades (tree : PhyloTree)
    (hlam : ∀ X ∈ tree.clades, ∀ Y ∈ tree.clades, X ⊆ Y ∨ Y ⊆ X ∨ Disjoint X Y)
    {X : Finset ℕ} (hX : X ∈ tree.clades) (h2 : 2 ≤ #X) :
    ∃ B ∈ tree.clades, ∃ C ∈ tree.clades, Disjoint B C ∧ B ∪ C = X := by
  induction tree generalizing X with
  | leaf a =>
    simp only [PhyloTree.clades, List.mem_singleton] at hX
    rw [hX, card_singleton] at h2
    omega
  | fork l r ihl ihr =>
    have hsub : ∀ Y, Y ∈ l.clades ∨ Y ∈ r.clades → Y ∈ (PhyloTree.fork l r).clades := by
      intro Y hY
      simp only [PhyloTree.clades, List.mem_cons, List.mem_append]
      exact Or.inr hY
    have hlaml : ∀ X ∈ l.clades, ∀ Y ∈ l.clades, X ⊆ Y ∨ Y ⊆ X ∨ Disjoint X Y :=
      fun X hX Y hY => hlam X (hsub X (Or.inl hX)) Y (hsub Y (Or.inl hY))
    have hlamr : ∀ X ∈ r.clades, ∀ Y ∈ r.clades, X ⊆ Y ∨ Y ⊆ X ∨ Disjoint X Y :=
      fun X hX Y hY => hlam X (hsub X (Or.inr hX)) Y (hsub Y (Or.inr hY))
    have hl : l.taxa ∈ (PhyloTree.fork l r).clades := hsub _ (Or.inl (taxa_mem_clades l))
    have hr : r.taxa ∈ (PhyloTree.fork l r).clades := hsub _ (Or.inr (taxa_mem_clades r))
    simp only [PhyloTree.clades, List.mem_cons, List.mem_append] at hX
    rcases hX with rfl | hX | hX
    · -- the root clade: its two children are disjoint, or one contains the other
      rcases hlam _ hl _ hr with hlr | hrl | hdisj
      · rw [union_eq_right.2 hlr] at h2 ⊢
        obtain ⟨B, hB, C, hC, hBC⟩ := ihr hlamr (taxa_mem_clades r) h2
        exact ⟨B, hsub B (Or.inr hB), C, hsub C (Or.inr hC), hBC⟩
      · rw [union_eq_left.2 hrl] at h2 ⊢
        obtain ⟨B, hB, C, hC, hBC⟩ := ihl hlaml (taxa_mem_clades l) h2
        exact ⟨B, hsub B (Or.inl hB), C, hsub C (Or.inl hC), hBC⟩
      · exact ⟨_, hl, _, hr, hdisj, rfl⟩
    · obtain ⟨B, hB, C, hC, hBC⟩ := ihl hlaml hX h2
      exact ⟨B, hsub B (Or.inl hB), C, hsub C (Or.inl hC), hBC⟩
    · obtain ⟨B, hB, C, hC, hBC⟩ := ihr hlamr hX h2
      exact ⟨B, hsub B (Or.inr hB), C, hsub C (Or.inr hC), hBC⟩

/-- A species tree whose rooted topology is a tree of CAMUS is binary. -/
theorem isBinary_of_hasTopology {σ : SpeciesTree L} {tree : PhyloTree} (h : HasTopology σ tree) :
    σ.IsBinary := by
  have hinj : Function.Injective fun A : Finset L => A.map (label L) := map_injective _
  -- the clades are nested or disjoint, as the clusters are
  have hlam : ∀ X ∈ tree.clades, ∀ Y ∈ tree.clades, X ⊆ Y ∨ Y ⊆ X ∨ Disjoint X Y := by
    intro X hX Y hY
    obtain ⟨A, hA, rfl⟩ := (h X).1 hX
    obtain ⟨B, hB, rfl⟩ := (h Y).1 hY
    rcases σ.laminar A hA B hB with hAB | hBA | hAB
    · exact Or.inl (map_subset_map.2 hAB)
    · exact Or.inr (Or.inl (map_subset_map.2 hBA))
    · exact Or.inr (Or.inr ((disjoint_map _).2 hAB))
  intro A hA hA2
  obtain ⟨B', hB', C', hC', hdisj, hunion⟩ :=
    exists_disjoint_clades tree hlam ((h _).2 ⟨A, hA, rfl⟩) (by rwa [card_map])
  obtain ⟨B, hB, rfl⟩ := (h B').1 hB'
  obtain ⟨C, hC, rfl⟩ := (h C').1 hC'
  refine ⟨B, hB, C, hC, (disjoint_map _).1 hdisj, hinj ?_⟩
  simpa only [map_union] using hunion

/-- Section 3.3, with the species tree as a tree of CAMUS: under the MSC on a species tree `σ`
whose rooted topology is the tree `tree`, on every four taxa `a < b < c < d` of `σ`, the quartet
tree in Q(tree) is strictly the most probable quartet tree of a gene tree, and the two others
have the same probability. -/
theorem msc_pattern_induced {σ : SpeciesTree L} {tree : PhyloTree} (h : HasTopology σ tree)
    (k : QuartetKey) (hk : keyTaxa k ⊆ L) :
    ∃ s, (k.quartet s).induced tree = true ∧
      (∀ s', s' ≠ s → quartetProb σ (k.quartet s') < quartetProb σ (k.quartet s)) ∧
      ∀ s' s'', s' ≠ s → s'' ≠ s →
        quartetProb σ (k.quartet s') = quartetProb σ (k.quartet s'') := by
  obtain ⟨s, hs, hlt, heq⟩ := msc_pattern (isBinary_of_hasTopology h) k hk
  exact ⟨s, (induces_iff_induced h _).1 hs, hlt, heq⟩

end Coalescent

end Camus
