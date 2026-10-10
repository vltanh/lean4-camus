module

public import Camus.Network.TreeBased.Branch
public import Camus.Network.TreeBased.Glue
public import Camus.DP.Definition1

/-!
# Every rooted binary level-1 network is tree-based

Section 2.1: "Each rooted binary level-1 phylogenetic network N induces a set 𝒯 of rooted binary
trees formed by deleting one incoming edge into each reticulation node ... in each of the possible
ways. Thus, N can be constructed by taking one of the trees t∈𝒯 and adding reticulations (edges)
to t. For this reason, N is said to be tree-based". This file proves that every switching `S` of a
rooted binary level-1 network `N` (one incoming edge kept at every vertex other than the root,
`RootedNetwork.Switching`) is a subdivision of a well-labelled tree `t` on the taxa of `N`, the tree
obtained from `S` by suppressing the vertices with one child: `N` is built on `t` in the sense of
Definition 1, through `S` (`RootedNetwork.exists_displayedSubdivision`). So every such network is
tree-based (`RootedNetwork.treeBased`; Section 3.2: "the network N is tree-based (which follows
directly from being level-1)"), and Section 2.4's "it is known that a level-1 phylogenetic network
on n leaves will not have more than n−1 reticulations" holds for every rooted binary level-1
network (`RootedNetwork.reticulationCount_le`, in `Camus/Network/TreeBased/Root.lean`).

## Main results

* `RootedNetwork.exists_branch_subdivision`: the part of `S` below each vertex is a subdivision of
  a well-labelled tree.
* `RootedNetwork.exists_displayedSubdivision`: every switching is a subdivision of a well-labelled
  tree on the taxa of `N`, below a directed path from the root of `N` (Definition 1).
* `RootedNetwork.builtOn_of_switching`, `RootedNetwork.treeBased`: `N` is built on the tree of
  each of its switchings, in the sense of Definition 1.

## Proof

The tree of `S` below a vertex `v` is built by strong induction on the number of vertices below `v`
in `S` (`RootedNetwork.below`), with the part of `N` below `v` as the network
(`RootedNetwork.branch`):
1. `v` has no child in `S`: it is the leaf of a taxon `a`
   (`RootedNetwork.switching_leaf_of_childless`), and the tree is `leaf a`
   (`DisplayedSubdivision.single`);
2. `v` has one child `c`: the tree below `c`, whose root wire is preceded by `v`
   (`DisplayedSubdivision.extendRoot`); the vertex `v` is suppressed;
3. `v` has two children `c₁` and `c₂`: the parts below them are disjoint
   (`RootedNetwork.below_disjoint`), and the tree is `fork t₁ t₂` of the trees below them, with root
   `v` (`DisplayedSubdivision.join`).
At the root of `N`, the part below the root is `N` with the edges of `S`
(`RootedNetwork.below_root`, `RootedNetwork.belowEdges_root`, `RootedNetwork.cladeBelow_root`).
-/

@[expose] public section

namespace Camus

namespace RootedNetwork

variable {N : RootedNetwork} {S : Finset (ℕ × ℕ)}

/-- The part of a switching `S` of `N` below a vertex `v` of `N` is a subdivision of a well-labelled
tree: the tree of `S` below `v`, with the vertices with one child suppressed. -/
theorem exists_branch_subdivision (hN : N.RootedBinaryLevelOne) (hS : N.Switching S) {v : ℕ}
    (hv : v ∈ N.vertices) :
    ∃ t : PhyloTree, t.WellLabelled ∧
      Nonempty (DisplayedSubdivision t (N.branch S v) (N.belowEdges S v)) := by
  suffices h : ∀ n, ∀ v ∈ N.vertices, (N.below S v).card = n → ∃ t : PhyloTree,
      t.WellLabelled ∧ Nonempty (DisplayedSubdivision t (N.branch S v) (N.belowEdges S v)) from
    h _ v hv rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro v hv hn
  rcases children_cases hN hS hv with hchild | ⟨c, hc, hout⟩ | ⟨c₁, c₂, hne, h₁, h₂, hout⟩
  -- 1. no child: a labelled leaf
  · obtain ⟨a, ha, hleaf⟩ := switching_leaf_of_childless hN hS hv hchild
    exact ⟨.leaf a, List.nodup_singleton a, ⟨DisplayedSubdivision.single a
      (below_eq_singleton_of_childless hv hchild) (belowEdges_eq_empty_of_childless hv hchild)
      (cladeBelow_eq_singleton_of_childless hN hchild ha hleaf) hleaf
      (branch_switching hN hS v)⟩⟩
  -- 2. one child `c`: the tree below `c`, with `v` added to its root wire
  · have hvc := not_mem_below_of_edge hN hS hc
    obtain ⟨t, ht, ⟨H⟩⟩ := ih _ (hn ▸ below_card_lt hv hc hvc) c (hN.2.1 _ (hS.1 hc)).2 rfl
    have hout' : ∀ w, (v, w) ∈ S → w = c ∨ w = c := fun w hw => Or.inl (hout w hw)
    refine ⟨t, ht, ⟨H.extendRoot hvc ?_ ?_ ?_ (fun _ => rfl) (branch_switching hN hS v)⟩⟩
    · have h := below_eq_of_children hv hc hc hout'
      rwa [Finset.union_self] at h
    · have h := belowEdges_eq_of_children hv hc hc hout'
      rwa [Finset.union_self, Finset.insert_idem] at h
    · have h := cladeBelow_eq_of_children hN hS hc hc hout'
      rwa [Finset.union_self] at h
  -- 3. two children: the fork of the trees below them, with root `v`
  · have hv₁ := not_mem_below_of_edge hN hS h₁
    have hv₂ := not_mem_below_of_edge hN hS h₂
    have hdisj := below_disjoint hN hS h₁ h₂ hne
    obtain ⟨t₁, ht₁, ⟨H₁⟩⟩ := ih _ (hn ▸ below_card_lt hv h₁ hv₁) c₁ (hN.2.1 _ (hS.1 h₁)).2 rfl
    obtain ⟨t₂, ht₂, ⟨H₂⟩⟩ := ih _ (hn ▸ below_card_lt hv h₂ hv₂) c₂ (hN.2.1 _ (hS.1 h₂)).2 rfl
    refine ⟨.fork t₁ t₂, ?_, ⟨DisplayedSubdivision.join H₁ H₂ hdisj hv₁ hv₂
      (below_eq_of_children hv h₁ h₂ hout) (belowEdges_eq_of_children hv h₁ h₂ hout)
      (cladeBelow_eq_of_children hN hS h₁ h₂ hout) (fun _ => rfl) (fun _ => rfl)
      (branch_switching hN hS v)⟩⟩
    -- the taxa of `t₁` and `t₂` have their leaves below `c₁` and `c₂`, which are disjoint
    refine List.nodup_append.mpr ⟨ht₁, ht₂, fun a ha b hb hab => ?_⟩
    have ha' : a ∈ N.cladeBelow S c₁ := by
      change a ∈ (N.branch S c₁).taxa
      rw [H₁.taxa_preserved]
      exact List.mem_toFinset.mpr ha
    have hb' : b ∈ N.cladeBelow S c₂ := by
      change b ∈ (N.branch S c₂).taxa
      rw [H₂.taxa_preserved]
      exact List.mem_toFinset.mpr hb
    rw [hab] at ha'
    exact Finset.disjoint_left.mp hdisj (leaf_mem_below hN ha') (leaf_mem_below hN hb')

/-- Section 2.1: every switching `S` of a rooted binary level-1 network `N` gives a tree of `N`
on which `N` is built (Definition 1): `S` is a subdivision of a well-labelled tree `t` on the taxa
of `N`, below a directed path from the root of `N` to the root of `t`. The tree `t` is obtained
from `S` by suppressing the vertices with one child; `S` has no unlabelled leaf
(`RootedNetwork.switching_leaf_of_childless`). -/
theorem exists_displayedSubdivision (hN : N.RootedBinaryLevelOne) (hS : N.Switching S) :
    ∃ t : PhyloTree, t.WellLabelled ∧ t.taxa = N.taxa ∧ Nonempty (DisplayedSubdivision t N S) := by
  obtain ⟨t, ht, ⟨H⟩⟩ := exists_branch_subdivision hN hS hN.1
  let H' := H.congr (below_root hN hS) rfl (cladeBelow_root hN hS) (fun _ => rfl)
    (belowEdges_root hN hS) hS
  exact ⟨t, ht, H'.taxa_preserved.symm, ⟨H'⟩⟩

/-- Section 2.1: "N can be constructed by taking one of the trees t∈𝒯 and adding reticulations
(edges) to t". For every switching `S` of a rooted binary level-1 network `N`, `N` is built, in the
sense of Definition 1, on a well-labelled tree `t` on its taxa through `S`: `t` is the tree of `S`,
of which `S` is a subdivision (`RootedNetwork.exists_displayedSubdivision`). -/
theorem builtOn_of_switching (hN : N.RootedBinaryLevelOne) (hS : N.Switching S) :
    ∃ t : PhyloTree, t.WellLabelled ∧ t.taxa = N.taxa ∧ N.BuiltOn t ∧
      Nonempty (DisplayedSubdivision t N S) := by
  obtain ⟨t, ht, htaxa, hH⟩ := exists_displayedSubdivision hN hS
  exact ⟨t, ht, htaxa, ⟨hN, S, hH⟩, hH⟩

/-- Section 2.1: every rooted binary level-1 network is tree-based. It is built, in the sense of
Definition 1, on a well-labelled tree on its taxa. -/
theorem treeBased (hN : N.RootedBinaryLevelOne) :
    ∃ t : PhyloTree, t.WellLabelled ∧ t.taxa = N.taxa ∧ N.BuiltOn t := by
  obtain ⟨S, hS⟩ := exists_switching hN
  obtain ⟨t, ht, htaxa, hbuilt, -⟩ := builtOn_of_switching hN hS
  exact ⟨t, ht, htaxa, hbuilt⟩

/-- A rooted binary level-1 network has a taxon: it is built on a tree, which has a leaf. -/
theorem taxa_nonempty (hN : N.RootedBinaryLevelOne) : N.taxa.Nonempty := by
  obtain ⟨t, -, htaxa, -⟩ := treeBased hN
  rw [← htaxa]
  obtain ⟨a, ha⟩ := List.exists_mem_of_length_pos t.labels_nonempty
  exact ⟨a, List.mem_toFinset.mpr ha⟩

end RootedNetwork

end Camus
