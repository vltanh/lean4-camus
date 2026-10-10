module

public import Camus.External.NMSC.Cycle

/-!
# The displayed trees of a network

CAMUS's Definition 1 defines the trees displayed by a rooted level-1 network (delete one of the two
edges into each reticulation, in every possible way, and clean up) and the set Q(N_r) of their
quartets. This file defines them for the networks `Brooqs.Net` of the network multispecies
coalescent: `Brooqs.Net.displayed N` lists the displayed trees of `N`, each given by its clusters
(a rooted tree is determined by its clusters), and `Brooqs.Net.Displays N a b c e` says that one of
them displays the quartet `ab|ce` (`Brooqs.geneTreeDisplays`: some cluster contains `a` and `b` but
neither `c` nor `e`, or contains `c` and `e` but neither `a` nor `b`).

At a cycle, the network below the hybrid node (the hybrid component) hangs from the bottom of the
side `S₁` or from the bottom of the side `S₂`. Along a side, the node of each pendant network has
the cluster of the taxa of that network, of the networks hanging below it on the side, and of the
hybrid component when it hangs from this side (`Brooqs.Side.displayed`).

## Main results

* `Brooqs.Net.displayed`, `Brooqs.Side.displayed`, `Brooqs.Net.Displays`: the displayed trees and
  the displayed quartets.
* `Brooqs.Net.taxa_mem_of_mem_subnets`: the taxa of a subnetwork form a cluster of every displayed
  tree.
* `Brooqs.Net.compatible_of_mem_subnets`: every cluster of a displayed tree is nested with the taxa
  of a subnetwork or disjoint from them.
* `Brooqs.Net.displays_of_subnet`: if a subnetwork contains exactly two of four taxa, `x` and `y`,
  the network displays `xy|zw` and neither `xz|yw` nor `xw|yz`.
-/

@[expose] public section

namespace Brooqs

open Finset

universe u

variable {X : Type u} [DecidableEq X]

/-- The taxa below a side: the labels of the leaves of the networks hanging from its nodes. -/
def Side.taxa (S : Side X) : Finset X := S.leaves.toFinset

mutual
/-- The displayed trees of `N` (CAMUS's Definition 1), each given by its clusters, with repetitions:
* a leaf `x` displays the tree with the one cluster `{x}`;
* a tree node joins a displayed tree of each child under the cluster of all their taxa;
* at the top node of a cycle, the hybrid component, with one of its displayed trees, hangs from the
  bottom of the side `S₁` (the hybrid edge of `S₂` is deleted) or from the bottom of the side `S₂`;
  the top node has the cluster of all the taxa of the cycle. -/
def Net.displayed : Net X → List (Finset (Finset X))
  | .leaf x => [{{x}}]
  | .tree _ N₁ _ N₂ =>
      N₁.displayed.flatMap fun K₁ => N₂.displayed.map fun K₂ =>
        insert (N₁.taxa ∪ N₂.taxa) (K₁ ∪ K₂)
  | .cycle _ S₁ S₂ _ N =>
      N.displayed.flatMap fun K =>
        ((S₁.displayed N.taxa).flatMap fun K₁ => (S₂.displayed ∅).map fun K₂ =>
            insert (S₁.taxa ∪ S₂.taxa ∪ N.taxa) (K ∪ K₁ ∪ K₂)) ++
        ((S₁.displayed ∅).flatMap fun K₁ => (S₂.displayed N.taxa).map fun K₂ =>
            insert (S₁.taxa ∪ S₂.taxa ∪ N.taxa) (K ∪ K₁ ∪ K₂))

/-- The clusters of the displayed trees along a side, when the taxa `T` hang below its hybrid edge
(`T = ∅` when the hybrid edge of the side is deleted): each node of the side has the cluster of the
taxa of its pendant network, of the networks hanging below it on the side, and of `T`; the clusters
of a displayed tree of each pendant network are added. -/
def Side.displayed : Side X → Finset X → List (Finset (Finset X))
  | .hyb _, _ => [∅]
  | .node _ _ M S, T => (S.displayed T).flatMap fun K => M.displayed.map fun K' =>
        insert (T ∪ S.taxa ∪ M.taxa) (K ∪ K')
end

theorem Net.taxa_leaf (x : X) : (Net.leaf x).taxa = {x} := by
  simp [Net.taxa, Net.leaves]

theorem Net.taxa_tree (ℓ₁ ℓ₂ : ℝ) (N₁ N₂ : Net X) :
    (Net.tree ℓ₁ N₁ ℓ₂ N₂).taxa = N₁.taxa ∪ N₂.taxa := by
  simp [Net.taxa, Net.leaves, List.toFinset_append]

theorem Net.taxa_cycle (γ ℓ : ℝ) (S₁ S₂ : Side X) (N : Net X) :
    (Net.cycle γ S₁ S₂ ℓ N).taxa = S₁.taxa ∪ S₂.taxa ∪ N.taxa := by
  simp [Net.taxa, Side.taxa, Net.leaves, List.toFinset_append]

theorem Side.taxa_hyb (ℓ : ℝ) : (Side.hyb ℓ : Side X).taxa = ∅ := by
  simp [Side.taxa, Side.leaves]

theorem Side.taxa_node (ℓ b : ℝ) (M : Net X) (S : Side X) :
    (Side.node ℓ b M S).taxa = M.taxa ∪ S.taxa := by
  simp [Side.taxa, Net.taxa, Side.leaves, List.toFinset_append]

mutual
/-- The clusters of a displayed tree are sets of taxa of the network. -/
theorem Net.subset_taxa_of_mem_displayed :
    ∀ {N : Net X} {K : Finset (Finset X)}, K ∈ N.displayed → ∀ A ∈ K, A ⊆ N.taxa
  | .leaf x, K, hK, A, hA => by
      simp only [Net.displayed, List.mem_singleton] at hK
      subst hK
      rw [mem_singleton] at hA
      subst hA
      rw [Net.taxa_leaf]
  | .tree ℓ₁ N₁ ℓ₂ N₂, K, hK, A, hA => by
      simp only [Net.displayed, List.mem_flatMap, List.mem_map] at hK
      obtain ⟨K₁, hK₁, K₂, hK₂, rfl⟩ := hK
      rw [Net.taxa_tree]
      rcases mem_insert.1 hA with rfl | hA
      · exact subset_rfl
      rcases mem_union.1 hA with hA | hA
      · exact (Net.subset_taxa_of_mem_displayed hK₁ A hA).trans subset_union_left
      · exact (Net.subset_taxa_of_mem_displayed hK₂ A hA).trans subset_union_right
  | .cycle γ S₁ S₂ ℓ N, K, hK, A, hA => by
      simp only [Net.displayed, List.mem_flatMap, List.mem_append, List.mem_map] at hK
      rw [Net.taxa_cycle]
      obtain ⟨K₀, hK₀, ⟨K₁, hK₁, K₂, hK₂, rfl⟩ | ⟨K₁, hK₁, K₂, hK₂, rfl⟩⟩ := hK
      all_goals
        rcases mem_insert.1 hA with rfl | hA
        · exact subset_rfl
        rcases mem_union.1 hA with hA | hA
        · rcases mem_union.1 hA with hA | hA
          · exact (Net.subset_taxa_of_mem_displayed hK₀ A hA).trans subset_union_right
          · rcases Side.cluster_cases hK₁ A hA with h | ⟨-, h⟩
            · exact h.trans (subset_union_left.trans subset_union_left)
            · refine h.trans (union_subset ?_ (subset_union_left.trans subset_union_left))
              first
                | exact empty_subset _
                | exact subset_union_right
        · rcases Side.cluster_cases hK₂ A hA with h | ⟨-, h⟩
          · exact h.trans (subset_union_right.trans subset_union_left)
          · refine h.trans (union_subset ?_ (subset_union_right.trans subset_union_left))
            first
              | exact empty_subset _
              | exact subset_union_right

/-- A cluster along a side lies below the pendant networks, or contains the taxa `T` hanging
below the hybrid edge and lies below the side. -/
theorem Side.cluster_cases :
    ∀ {S : Side X} {T : Finset X} {K : Finset (Finset X)}, K ∈ S.displayed T → ∀ A ∈ K,
      A ⊆ S.taxa ∨ (T ⊆ A ∧ A ⊆ T ∪ S.taxa)
  | .hyb _, T, K, hK, A, hA => by
      simp only [Side.displayed, List.mem_singleton] at hK
      subst hK
      exact absurd hA (notMem_empty A)
  | .node ℓ b M S, T, K, hK, A, hA => by
      simp only [Side.displayed, List.mem_flatMap, List.mem_map] at hK
      obtain ⟨K₁, hK₁, K₂, hK₂, rfl⟩ := hK
      rw [Side.taxa_node]
      rcases mem_insert.1 hA with rfl | hA
      · refine Or.inr ⟨subset_union_left.trans subset_union_left, ?_⟩
        intro x hx
        simp only [mem_union] at hx ⊢
        tauto
      rcases mem_union.1 hA with hA | hA
      · rcases Side.cluster_cases hK₁ A hA with h | ⟨h₁, h₂⟩
        · exact Or.inl (h.trans subset_union_right)
        · refine Or.inr ⟨h₁, h₂.trans ?_⟩
          intro x hx
          simp only [mem_union] at hx ⊢
          tauto
      · exact Or.inl ((Net.subset_taxa_of_mem_displayed hK₂ A hA).trans subset_union_left)
end

mutual
/-- A network displays at least one tree. -/
theorem Net.displayed_ne_nil : ∀ N : Net X, N.displayed ≠ []
  | .leaf _ => by simp [Net.displayed]
  | .tree ℓ₁ N₁ ℓ₂ N₂ => by
      obtain ⟨K₁, hK₁⟩ := List.exists_mem_of_ne_nil _ (Net.displayed_ne_nil N₁)
      obtain ⟨K₂, hK₂⟩ := List.exists_mem_of_ne_nil _ (Net.displayed_ne_nil N₂)
      refine List.ne_nil_of_mem (a := insert (N₁.taxa ∪ N₂.taxa) (K₁ ∪ K₂)) ?_
      simp only [Net.displayed, List.mem_flatMap, List.mem_map]
      exact ⟨K₁, hK₁, K₂, hK₂, rfl⟩
  | .cycle γ S₁ S₂ ℓ N => by
      obtain ⟨K₀, hK₀⟩ := List.exists_mem_of_ne_nil _ (Net.displayed_ne_nil N)
      obtain ⟨K₁, hK₁⟩ := List.exists_mem_of_ne_nil _ (Side.displayed_ne_nil S₁ N.taxa)
      obtain ⟨K₂, hK₂⟩ := List.exists_mem_of_ne_nil _ (Side.displayed_ne_nil S₂ ∅)
      refine List.ne_nil_of_mem
        (a := insert (S₁.taxa ∪ S₂.taxa ∪ N.taxa) (K₀ ∪ K₁ ∪ K₂)) ?_
      simp only [Net.displayed, List.mem_flatMap, List.mem_append, List.mem_map]
      exact ⟨K₀, hK₀, Or.inl ⟨K₁, hK₁, K₂, hK₂, rfl⟩⟩

theorem Side.displayed_ne_nil : ∀ (S : Side X) (T : Finset X), S.displayed T ≠ []
  | .hyb _, _ => by simp [Side.displayed]
  | .node ℓ b M S, T => by
      obtain ⟨K₁, hK₁⟩ := List.exists_mem_of_ne_nil _ (Side.displayed_ne_nil S T)
      obtain ⟨K₂, hK₂⟩ := List.exists_mem_of_ne_nil _ (Net.displayed_ne_nil M)
      refine List.ne_nil_of_mem (a := insert (T ∪ S.taxa ∪ M.taxa) (K₁ ∪ K₂)) ?_
      simp only [Side.displayed, List.mem_flatMap, List.mem_map]
      exact ⟨K₁, hK₁, K₂, hK₂, rfl⟩
end

mutual
/-- The taxa of a subnetwork form a cluster of every displayed tree: the subnetwork hangs from a
cut edge. -/
theorem Net.taxa_mem_of_mem_subnets :
    ∀ {N M : Net X}, M ∈ N.subnets → ∀ K ∈ N.displayed, M.taxa ∈ K
  | .leaf x, M, hM, K, hK => by
      simp only [Net.subnets, List.mem_singleton] at hM
      subst hM
      simp only [Net.displayed, List.mem_singleton] at hK
      subst hK
      rw [Net.taxa_leaf]
      exact mem_singleton_self _
  | .tree ℓ₁ N₁ ℓ₂ N₂, M, hM, K, hK => by
      simp only [Net.displayed, List.mem_flatMap, List.mem_map] at hK
      obtain ⟨K₁, hK₁, K₂, hK₂, rfl⟩ := hK
      simp only [Net.subnets, List.mem_cons, List.mem_append] at hM
      rcases hM with rfl | hM | hM
      · rw [Net.taxa_tree]
        exact mem_insert_self _ _
      · exact mem_insert_of_mem (mem_union_left _ (Net.taxa_mem_of_mem_subnets hM K₁ hK₁))
      · exact mem_insert_of_mem (mem_union_right _ (Net.taxa_mem_of_mem_subnets hM K₂ hK₂))
  | .cycle γ S₁ S₂ ℓ N, M, hM, K, hK => by
      simp only [Net.displayed, List.mem_flatMap, List.mem_append, List.mem_map] at hK
      simp only [Net.subnets, List.mem_cons, List.mem_append] at hM
      obtain ⟨K₀, hK₀, ⟨K₁, hK₁, K₂, hK₂, rfl⟩ | ⟨K₁, hK₁, K₂, hK₂, rfl⟩⟩ := hK
      all_goals
        rcases hM with rfl | (hM | hM) | hM
        · rw [Net.taxa_cycle]
          exact mem_insert_self _ _
        · exact mem_insert_of_mem (mem_union_left _
            (mem_union_right _ (Side.taxa_mem_of_mem_subnets hM _ K₁ hK₁)))
        · exact mem_insert_of_mem (mem_union_right _ (Side.taxa_mem_of_mem_subnets hM _ K₂ hK₂))
        · exact mem_insert_of_mem (mem_union_left _
            (mem_union_left _ (Net.taxa_mem_of_mem_subnets hM K₀ hK₀)))

/-- The same for the networks hanging from a side. -/
theorem Side.taxa_mem_of_mem_subnets :
    ∀ {S : Side X} {M : Net X}, M ∈ S.subnets → ∀ T, ∀ K ∈ S.displayed T, M.taxa ∈ K
  | .hyb _, M, hM, _, _, _ => by simp [Side.subnets] at hM
  | .node ℓ b P S, M, hM, T, K, hK => by
      simp only [Side.displayed, List.mem_flatMap, List.mem_map] at hK
      obtain ⟨K₁, hK₁, K₂, hK₂, rfl⟩ := hK
      simp only [Side.subnets, List.mem_append] at hM
      rcases hM with hM | hM
      · exact mem_insert_of_mem (mem_union_right _ (Net.taxa_mem_of_mem_subnets hM K₂ hK₂))
      · exact mem_insert_of_mem (mem_union_left _ (Side.taxa_mem_of_mem_subnets hM T K₁ hK₁))
end

omit [DecidableEq X] in
private theorem dd_nodup_left {l₁ l₂ : List X} (h : (l₁ ++ l₂).Nodup) : l₁.Nodup :=
  (List.nodup_append.1 h).1

omit [DecidableEq X] in
private theorem dd_nodup_right {l₁ l₂ : List X} (h : (l₁ ++ l₂).Nodup) : l₂.Nodup :=
  (List.nodup_append.1 h).2.1

private theorem dd_disjoint {l₁ l₂ : List X} (h : (l₁ ++ l₂).Nodup) :
    Disjoint l₁.toFinset l₂.toFinset := by
  rw [disjoint_left]
  intro a ha hb
  exact (List.nodup_append.1 h).2.2 a (List.mem_toFinset.1 ha) a (List.mem_toFinset.1 hb) rfl

theorem Net.taxa_subset_of_mem_subnets {N M : Net X} (h : M ∈ N.subnets) : M.taxa ⊆ N.taxa :=
  fun _ hx => List.mem_toFinset.2
    ((Net.leaves_sublist_of_mem_subnets h).subset (List.mem_toFinset.1 hx))

theorem Side.taxa_subset_of_mem_subnets {S : Side X} {M : Net X} (h : M ∈ S.subnets) :
    M.taxa ⊆ S.taxa :=
  fun _ hx => List.mem_toFinset.2
    ((Side.leaves_sublist_of_mem_subnets h).subset (List.mem_toFinset.1 hx))

mutual
/-- Every cluster of a displayed tree is compatible with the taxa of a subnetwork: nested or
disjoint. -/
theorem Net.compatible_of_mem_subnets :
    ∀ {N M : Net X}, N.leaves.Nodup → M ∈ N.subnets → ∀ K ∈ N.displayed, ∀ A ∈ K,
      A ⊆ M.taxa ∨ M.taxa ⊆ A ∨ Disjoint A M.taxa
  | .leaf _, M, _, hM, K, hK, A, hA => by
      simp only [Net.subnets, List.mem_singleton] at hM
      subst hM
      exact Or.inl (Net.subset_taxa_of_mem_displayed hK A hA)
  | .tree ℓ₁ N₁ ℓ₂ N₂, M, hN, hM, K, hK, A, hA => by
      have hN' : (N₁.leaves ++ N₂.leaves).Nodup := hN
      have hd : Disjoint N₁.taxa N₂.taxa := dd_disjoint hN'
      simp only [Net.subnets, List.mem_cons, List.mem_append] at hM
      rcases hM with rfl | hM | hM
      · exact Or.inl (Net.subset_taxa_of_mem_displayed hK A hA)
      all_goals
        simp only [Net.displayed, List.mem_flatMap, List.mem_map] at hK
        obtain ⟨K₁, hK₁, K₂, hK₂, rfl⟩ := hK
        have hMt := Net.taxa_subset_of_mem_subnets hM
        rcases mem_insert.1 hA with rfl | hA
        · refine Or.inr (Or.inl (hMt.trans ?_))
          first
            | exact subset_union_left
            | exact subset_union_right
        rcases mem_union.1 hA with hA | hA
      · exact Net.compatible_of_mem_subnets (dd_nodup_left hN') hM K₁ hK₁ A hA
      · exact Or.inr (Or.inr ((hd.symm.mono_left
          (Net.subset_taxa_of_mem_displayed hK₂ A hA)).mono_right hMt))
      · exact Or.inr (Or.inr ((hd.mono_left
          (Net.subset_taxa_of_mem_displayed hK₁ A hA)).mono_right hMt))
      · exact Net.compatible_of_mem_subnets (dd_nodup_right hN') hM K₂ hK₂ A hA
  | .cycle γ S₁ S₂ ℓ N, M, hN, hM, K, hK, A, hA => by
      have hN' : (S₁.leaves ++ S₂.leaves ++ N.leaves).Nodup := hN
      have h12 : (S₁.leaves ++ S₂.leaves).Nodup := dd_nodup_left hN'
      have hS₁ : S₁.leaves.Nodup := dd_nodup_left h12
      have hS₂ : S₂.leaves.Nodup := dd_nodup_right h12
      have hN₀ : N.leaves.Nodup := dd_nodup_right hN'
      have d12 : Disjoint S₁.taxa S₂.taxa := dd_disjoint h12
      have d3 : Disjoint (S₁.taxa ∪ S₂.taxa) N.taxa := by
        have := dd_disjoint hN'
        rwa [List.toFinset_append] at this
      have d13 : Disjoint S₁.taxa N.taxa := d3.mono_left subset_union_left
      have d23 : Disjoint S₂.taxa N.taxa := d3.mono_left subset_union_right
      simp only [Net.subnets, List.mem_cons, List.mem_append] at hM
      rcases hM with rfl | (hM | hM) | hM
      · exact Or.inl (Net.subset_taxa_of_mem_displayed hK A hA)
      · -- `M` hangs from the side `S₁`
        have hMt := Side.taxa_subset_of_mem_subnets hM
        simp only [Net.displayed, List.mem_flatMap, List.mem_append, List.mem_map] at hK
        obtain ⟨K₀, hK₀, ⟨K₁, hK₁, K₂, hK₂, rfl⟩ | ⟨K₁, hK₁, K₂, hK₂, rfl⟩⟩ := hK
        all_goals
          rcases mem_insert.1 hA with rfl | hA
          · refine Or.inr (Or.inl (hMt.trans (subset_union_left.trans subset_union_left)))
          rcases mem_union.1 hA with hA | hA
          · rcases mem_union.1 hA with hA | hA
            · exact Or.inr (Or.inr ((d13.symm.mono_left
                (Net.subset_taxa_of_mem_displayed hK₀ A hA)).mono_right hMt))
            · exact Side.compatible_of_mem_subnets hS₁ hM _
                (by first | exact d13.symm | exact disjoint_empty_left _) K₁ hK₁ A hA
          · refine Or.inr (Or.inr (Disjoint.mono_right hMt ?_))
            rcases Side.cluster_cases hK₂ A hA with h | ⟨-, h⟩
            · exact d12.symm.mono_left h
            · refine Disjoint.mono_left h (disjoint_union_left.2 ⟨?_, d12.symm⟩)
              first | exact disjoint_empty_left _ | exact d13.symm
      · -- `M` hangs from the side `S₂`
        have hMt := Side.taxa_subset_of_mem_subnets hM
        simp only [Net.displayed, List.mem_flatMap, List.mem_append, List.mem_map] at hK
        obtain ⟨K₀, hK₀, ⟨K₁, hK₁, K₂, hK₂, rfl⟩ | ⟨K₁, hK₁, K₂, hK₂, rfl⟩⟩ := hK
        all_goals
          rcases mem_insert.1 hA with rfl | hA
          · refine Or.inr (Or.inl (hMt.trans (subset_union_right.trans subset_union_left)))
          rcases mem_union.1 hA with hA | hA
          · rcases mem_union.1 hA with hA | hA
            · exact Or.inr (Or.inr ((d23.symm.mono_left
                (Net.subset_taxa_of_mem_displayed hK₀ A hA)).mono_right hMt))
            · refine Or.inr (Or.inr (Disjoint.mono_right hMt ?_))
              rcases Side.cluster_cases hK₁ A hA with h | ⟨-, h⟩
              · exact d12.mono_left h
              · refine Disjoint.mono_left h (disjoint_union_left.2 ⟨?_, d12⟩)
                first | exact disjoint_empty_left _ | exact d23.symm
          · exact Side.compatible_of_mem_subnets hS₂ hM _
              (by first | exact d23.symm | exact disjoint_empty_left _) K₂ hK₂ A hA
      · -- `M` lies below the hybrid node
        have hMt := Net.taxa_subset_of_mem_subnets hM
        simp only [Net.displayed, List.mem_flatMap, List.mem_append, List.mem_map] at hK
        obtain ⟨K₀, hK₀, ⟨K₁, hK₁, K₂, hK₂, rfl⟩ | ⟨K₁, hK₁, K₂, hK₂, rfl⟩⟩ := hK
        all_goals
          rcases mem_insert.1 hA with rfl | hA
          · exact Or.inr (Or.inl (hMt.trans subset_union_right))
          rcases mem_union.1 hA with hA | hA
          · rcases mem_union.1 hA with hA | hA
            · exact Net.compatible_of_mem_subnets hN₀ hM K₀ hK₀ A hA
            · rcases Side.cluster_cases hK₁ A hA with h | ⟨h₁, h₂⟩
              · exact Or.inr (Or.inr ((d13.mono_left h).mono_right hMt))
              · first
                  | exact Or.inr (Or.inl (hMt.trans h₁))
                  | exact Or.inr (Or.inr ((d13.mono_left
                      (h₂.trans (by rw [empty_union]))).mono_right hMt))
          · rcases Side.cluster_cases hK₂ A hA with h | ⟨h₁, h₂⟩
            · exact Or.inr (Or.inr ((d23.mono_left h).mono_right hMt))
            · first
                | exact Or.inr (Or.inl (hMt.trans h₁))
                | exact Or.inr (Or.inr ((d23.mono_left
                    (h₂.trans (by rw [empty_union]))).mono_right hMt))

/-- The same for the networks hanging from a side, when the taxa `T` below its hybrid edge are
not below the side. -/
theorem Side.compatible_of_mem_subnets :
    ∀ {S : Side X} {M : Net X}, S.leaves.Nodup → M ∈ S.subnets → ∀ T, Disjoint T S.taxa →
      ∀ K ∈ S.displayed T, ∀ A ∈ K, A ⊆ M.taxa ∨ M.taxa ⊆ A ∨ Disjoint A M.taxa
  | .hyb _, M, _, hM, _, _, _, _, _, _ => by simp [Side.subnets] at hM
  | .node ℓ b P S, M, hS, hM, T, hT, K, hK, A, hA => by
      have hS' : (P.leaves ++ S.leaves).Nodup := hS
      have hd : Disjoint P.taxa S.taxa := dd_disjoint hS'
      rw [Side.taxa_node] at hT
      have hTP : Disjoint T P.taxa := hT.mono_right subset_union_left
      have hTS : Disjoint T S.taxa := hT.mono_right subset_union_right
      simp only [Side.displayed, List.mem_flatMap, List.mem_map] at hK
      obtain ⟨K₁, hK₁, K₂, hK₂, rfl⟩ := hK
      simp only [Side.subnets, List.mem_append] at hM
      rcases hM with hM | hM
      · have hMt := Net.taxa_subset_of_mem_subnets hM
        rcases mem_insert.1 hA with rfl | hA
        · exact Or.inr (Or.inl (hMt.trans subset_union_right))
        rcases mem_union.1 hA with hA | hA
        · refine Or.inr (Or.inr (Disjoint.mono_right hMt ?_))
          rcases Side.cluster_cases hK₁ A hA with h | ⟨-, h⟩
          · exact hd.symm.mono_left h
          · exact Disjoint.mono_left h (disjoint_union_left.2 ⟨hTP, hd.symm⟩)
        · exact Net.compatible_of_mem_subnets (dd_nodup_left hS') hM K₂ hK₂ A hA
      · have hMt := Side.taxa_subset_of_mem_subnets hM
        rcases mem_insert.1 hA with rfl | hA
        · exact Or.inr (Or.inl (hMt.trans (subset_union_right.trans subset_union_left)))
        rcases mem_union.1 hA with hA | hA
        · exact Side.compatible_of_mem_subnets (dd_nodup_right hS') hM T hTS K₁ hK₁ A hA
        · exact Or.inr (Or.inr ((hd.mono_left
            (Net.subset_taxa_of_mem_displayed hK₂ A hA)).mono_right hMt))
end

/-! ### Displayed quartets -/

/-- `N` displays the quartet `ab|ce`: some displayed tree of `N` has a cluster that contains `a`
and `b` but neither `c` nor `e`, or contains `c` and `e` but neither `a` nor `b`. -/
def Net.Displays (N : Net X) (a b c e : X) : Prop :=
  ∃ K ∈ N.displayed, geneTreeDisplays K a b c e = true

theorem geneTreeDisplays_swap_left (K : Finset (Finset X)) (a b c e : X) :
    geneTreeDisplays K b a c e = geneTreeDisplays K a b c e := by
  unfold geneTreeDisplays
  congr 1
  apply propext
  constructor <;> rintro ⟨C, hC, h⟩ <;> exact ⟨C, hC, by tauto⟩

theorem geneTreeDisplays_swap_right (K : Finset (Finset X)) (a b c e : X) :
    geneTreeDisplays K a b e c = geneTreeDisplays K a b c e := by
  unfold geneTreeDisplays
  congr 1
  apply propext
  constructor <;> rintro ⟨C, hC, h⟩ <;> exact ⟨C, hC, by tauto⟩

theorem geneTreeDisplays_swap_pairs (K : Finset (Finset X)) (a b c e : X) :
    geneTreeDisplays K c e a b = geneTreeDisplays K a b c e := by
  unfold geneTreeDisplays
  congr 1
  apply propext
  constructor <;> rintro ⟨C, hC, h⟩ <;> exact ⟨C, hC, by tauto⟩

theorem Net.displays_swap_left (N : Net X) (a b c e : X) :
    N.Displays b a c e ↔ N.Displays a b c e := by
  simp only [Net.Displays, geneTreeDisplays_swap_left]

theorem Net.displays_swap_right (N : Net X) (a b c e : X) :
    N.Displays a b e c ↔ N.Displays a b c e := by
  simp only [Net.Displays, geneTreeDisplays_swap_right]

theorem Net.displays_swap_pairs (N : Net X) (a b c e : X) :
    N.Displays c e a b ↔ N.Displays a b c e := by
  simp only [Net.Displays, geneTreeDisplays_swap_pairs]

/-- **A pair below a cut edge.** If a subnetwork `M` of `N` contains exactly the taxa `x` and `y`
of the four taxa `x, y, z, w`, every displayed tree of `N` displays `xy|zw` (the taxa of `M` form a
cluster), and none displays `xz|yw` or `xw|yz` (every cluster is nested with the taxa of `M` or
disjoint from them). -/
theorem Net.displays_of_subnet {N M : Net X} (hN : N.leaves.Nodup) (hM : M ∈ N.subnets)
    {x y z w : X} (hx : x ∈ M.taxa) (hy : y ∈ M.taxa) (hz : z ∉ M.taxa) (hw : w ∉ M.taxa) :
    N.Displays x y z w ∧ ¬ N.Displays x z y w ∧ ¬ N.Displays x w y z := by
  obtain ⟨K, hK⟩ := List.exists_mem_of_ne_nil _ (Net.displayed_ne_nil N)
  refine ⟨⟨K, hK, ?_⟩, ?_, ?_⟩
  · unfold geneTreeDisplays
    exact decide_eq_true ⟨M.taxa, Net.taxa_mem_of_mem_subnets hM K hK, Or.inl ⟨hx, hy, hz, hw⟩⟩
  all_goals
    rintro ⟨K, hK, h⟩
    unfold geneTreeDisplays at h
    obtain ⟨A, hA, h⟩ := of_decide_eq_true h
    rcases Net.compatible_of_mem_subnets hN hM K hK A hA with hsub | hsup | hdis
    · have h1 : z ∉ A := fun h' => hz (hsub h')
      have h2 : w ∉ A := fun h' => hw (hsub h')
      tauto
    · have h1 : x ∈ A := hsup hx
      have h2 : y ∈ A := hsup hy
      tauto
    · have h1 : x ∉ A := fun h' => disjoint_left.1 hdis h' hx
      have h2 : y ∉ A := fun h' => disjoint_left.1 hdis h' hy
      tauto

end Brooqs
