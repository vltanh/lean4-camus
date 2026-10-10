module

public import Camus.Pipelines.NMSC.BaseTree
public import Camus.Network.RootAbove.Display
public import Camus.Network.Reticulations

/-!
# A level-1 network of the NMSC and its graph display the same quartet trees

Section 3.2 works with the true network `N` as a rooted binary level-1 network built on the
constraint tree `T`, and with the set Q(N_r) of the quartet trees that it displays
(Definition 1). For a network `N : Brooqs.Net L` of the network multispecies coalescent, this file
shows that the graph `Realization.graph (baseTree N) (pairs N)` of CAMUS, obtained from the base
tree of `N` by adding an edge above each pair of `NMSC.pairs N` (Definition 3), displays exactly
the quartet trees that `N` displays (`NMSC.graph_displaysQuartet_iff`), and that it is a rooted
binary level-1 network built on the base tree (`NMSC.graph_anchoredExtension`), a displayed tree
of `N` (`NMSC.displaysTree_baseTree`).

## Main results

* `NMSC.clusters`, `NMSC.mem_clusters_iff`: the clusters of the displayed trees of `N`.
* `NMSC.cutSets`, `NMSC.cutSets_baseTree`: the clusters of the trees displayed by the graph
  through at most one added edge, and their equality with the clusters of the displayed trees
  of `N`.
* `NMSC.graph_displaysQuartet_iff`: the graph of `N` displays the quartet trees that `N` displays.
* `NMSC.graph_anchoredExtension`: the graph of `N` is built on the base tree of `N`.
* `NMSC.baseClusters`, `NMSC.displaysTree_baseTree`: the base tree is a displayed tree of `N`.
* `NMSC.cycleCount`, `NMSC.graph_reticulationCount`: the graph of `N` has one reticulation for each
  cycle of `N`.

## Proof

By `Realization.graph_displays_iff_cuts` (Lemma 1 of CAMUS and the quartets displayed by `T + e`),
the graph displays the quartet trees on its taxa cut by a clade of the base tree or by a clade of
the tree displayed through one added edge (`EdgeAbove.switchedClades`); `N` displays those cut by
a cluster of one of its displayed trees. The two families of clusters are equal
(`NMSC.cutSets_baseTree`), by induction on `N`: a tree node joins the clusters of its two children
(`NMSC.cutSets_fork`), and at a cycle, the tree displayed through the added edge of the cycle has
the clusters of the nodes of the two sides with the hybrid component moved to the other side
(`NMSC.cutSets_cycle`); the clusters of a node depend only on the choice of the side of the
hybrid component at the cycle of the node.
-/

@[expose] public section

namespace Camus

namespace NMSC

open Finset

variable {L : Finset ℕ}

/-! ### The clusters of the displayed trees of `N` -/

/-- The clusters of the nodes of a side, without the taxa below its hybrid edge: for each node,
the taxa of its pendant network and of the networks hanging below it on the side. -/
def spine : Brooqs.Side L → Finset (Finset L)
  | .hyb _ => ∅
  | .node ℓ b M S => insert (Brooqs.Side.node ℓ b M S).taxa (spine S)

mutual
/-- The clusters of the displayed trees of `N`: at a tree node, the taxa below it and the clusters
of its children; at a cycle, the taxa of the cycle, the clusters of the hybrid component and of
the pendant networks, and the clusters of the nodes of the two sides, with or without the taxa of
the hybrid component. -/
def clusters : Brooqs.Net L → Finset (Finset L)
  | .leaf x => {{x}}
  | .tree _ N₁ _ N₂ => insert (N₁.taxa ∪ N₂.taxa) (clusters N₁ ∪ clusters N₂)
  | .cycle _ S₁ S₂ _ H => insert (S₁.taxa ∪ S₂.taxa ∪ H.taxa)
      (clusters H ∪ pendantClusters S₁ ∪ pendantClusters S₂ ∪ spine S₁ ∪ spine S₂ ∪
        (spine S₁).image (H.taxa ∪ ·) ∪ (spine S₂).image (H.taxa ∪ ·))

/-- The clusters of the displayed trees of the networks hanging from the nodes of a side. -/
def pendantClusters : Brooqs.Side L → Finset (Finset L)
  | .hyb _ => ∅
  | .node _ _ M S => clusters M ∪ pendantClusters S
end

/-- A cluster of a displayed tree of a cycle: the taxa of the cycle, or a cluster of a displayed
tree of the hybrid component, or a cluster along a side, with or without the hybrid component. -/
theorem mem_displayed_cycle_iff (γ ℓ : ℝ) (S₁ S₂ : Brooqs.Side L) (H : Brooqs.Net L)
    (C : Finset L) :
    (∃ K ∈ (Brooqs.Net.cycle γ S₁ S₂ ℓ H).displayed, C ∈ K) ↔
      C = S₁.taxa ∪ S₂.taxa ∪ H.taxa ∨ (∃ K ∈ H.displayed, C ∈ K) ∨
        (∃ K ∈ S₁.displayed H.taxa, C ∈ K) ∨ (∃ K ∈ S₂.displayed ∅, C ∈ K) ∨
        (∃ K ∈ S₁.displayed ∅, C ∈ K) ∨ (∃ K ∈ S₂.displayed H.taxa, C ∈ K) := by
  obtain ⟨K₀, hK₀⟩ := List.exists_mem_of_ne_nil _ (Brooqs.Net.displayed_ne_nil H)
  obtain ⟨K₁, hK₁⟩ := List.exists_mem_of_ne_nil _ (Brooqs.Side.displayed_ne_nil S₁ H.taxa)
  obtain ⟨K₂, hK₂⟩ := List.exists_mem_of_ne_nil _ (Brooqs.Side.displayed_ne_nil S₂ ∅)
  obtain ⟨K₃, hK₃⟩ := List.exists_mem_of_ne_nil _ (Brooqs.Side.displayed_ne_nil S₁ ∅)
  obtain ⟨K₄, hK₄⟩ := List.exists_mem_of_ne_nil _ (Brooqs.Side.displayed_ne_nil S₂ H.taxa)
  simp only [Brooqs.Net.displayed, List.mem_flatMap, List.mem_append, List.mem_map]
  constructor
  · rintro ⟨_, ⟨K, hK, ⟨A, hA, B, hB, rfl⟩ | ⟨A, hA, B, hB, rfl⟩⟩, hC⟩ <;>
    rcases mem_insert.1 hC with rfl | hC
    · exact Or.inl rfl
    · rcases mem_union.1 hC with hC | hC
      · rcases mem_union.1 hC with hC | hC
        · exact Or.inr (Or.inl ⟨K, hK, hC⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨A, hA, hC⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨B, hB, hC⟩)))
    · exact Or.inl rfl
    · rcases mem_union.1 hC with hC | hC
      · rcases mem_union.1 hC with hC | hC
        · exact Or.inr (Or.inl ⟨K, hK, hC⟩)
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨A, hA, hC⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨B, hB, hC⟩))))
  · rintro (rfl | ⟨K, hK, hC⟩ | ⟨K, hK, hC⟩ | ⟨K, hK, hC⟩ | ⟨K, hK, hC⟩ | ⟨K, hK, hC⟩)
    · exact ⟨_, ⟨K₀, hK₀, Or.inl ⟨K₁, hK₁, K₂, hK₂, rfl⟩⟩, mem_insert_self _ _⟩
    · exact ⟨_, ⟨K, hK, Or.inl ⟨K₁, hK₁, K₂, hK₂, rfl⟩⟩,
        mem_insert_of_mem (mem_union_left _ (mem_union_left _ hC))⟩
    · exact ⟨_, ⟨K₀, hK₀, Or.inl ⟨K, hK, K₂, hK₂, rfl⟩⟩,
        mem_insert_of_mem (mem_union_left _ (mem_union_right _ hC))⟩
    · exact ⟨_, ⟨K₀, hK₀, Or.inl ⟨K₁, hK₁, K, hK, rfl⟩⟩, mem_insert_of_mem (mem_union_right _ hC)⟩
    · exact ⟨_, ⟨K₀, hK₀, Or.inr ⟨K, hK, K₄, hK₄, rfl⟩⟩,
        mem_insert_of_mem (mem_union_left _ (mem_union_right _ hC))⟩
    · exact ⟨_, ⟨K₀, hK₀, Or.inr ⟨K₃, hK₃, K, hK, rfl⟩⟩, mem_insert_of_mem (mem_union_right _ hC)⟩

mutual
/-- The clusters of the displayed trees of `N` are `NMSC.clusters N`. -/
theorem mem_clusters_iff :
    ∀ (N : Brooqs.Net L) (C : Finset L), C ∈ clusters N ↔ ∃ K ∈ N.displayed, C ∈ K
  | .leaf x, C => by simp [clusters, Brooqs.Net.displayed]
  | .tree _ N₁ _ N₂, C => by
      obtain ⟨K₁, hK₁⟩ := List.exists_mem_of_ne_nil _ (Brooqs.Net.displayed_ne_nil N₁)
      obtain ⟨K₂, hK₂⟩ := List.exists_mem_of_ne_nil _ (Brooqs.Net.displayed_ne_nil N₂)
      simp only [clusters, mem_insert, mem_union, Brooqs.Net.displayed, List.mem_flatMap,
        List.mem_map, mem_clusters_iff N₁, mem_clusters_iff N₂]
      constructor
      · rintro (rfl | ⟨K, hK, hC⟩ | ⟨K, hK, hC⟩)
        · exact ⟨_, ⟨K₁, hK₁, K₂, hK₂, rfl⟩, mem_insert_self _ _⟩
        · exact ⟨_, ⟨K, hK, K₂, hK₂, rfl⟩, mem_insert_of_mem (mem_union_left _ hC)⟩
        · exact ⟨_, ⟨K₁, hK₁, K, hK, rfl⟩, mem_insert_of_mem (mem_union_right _ hC)⟩
      · rintro ⟨_, ⟨K, hK, K', hK', rfl⟩, hC⟩
        rcases mem_insert.1 hC with rfl | hC
        · exact Or.inl rfl
        rcases mem_union.1 hC with hC | hC
        · exact Or.inr (Or.inl ⟨K, hK, hC⟩)
        · exact Or.inr (Or.inr ⟨K', hK', hC⟩)
  | .cycle γ S₁ S₂ ℓ H, C => by
      rw [mem_displayed_cycle_iff, ← mem_clusters_iff H C, ← mem_side_iff S₁ H.taxa C,
        ← mem_side_iff S₂ ∅ C, ← mem_side_iff S₁ ∅ C, ← mem_side_iff S₂ H.taxa C]
      simp only [clusters, mem_insert, mem_union, mem_image, empty_union, exists_eq_right]
      generalize (∃ a ∈ spine S₁, H.taxa ∪ a = C) = p₁
      generalize (∃ a ∈ spine S₂, H.taxa ∪ a = C) = p₂
      tauto

/-- The clusters along a side with the taxa `T` below its hybrid edge, in the displayed trees:
the clusters `T ∪ U` of its nodes and the clusters of the displayed trees of its pendant
networks. -/
theorem mem_side_iff : ∀ (S : Brooqs.Side L) (T C : Finset L),
    (∃ U ∈ spine S, T ∪ U = C) ∨ C ∈ pendantClusters S ↔ ∃ K ∈ S.displayed T, C ∈ K
  | .hyb _, T, C => by simp [Brooqs.Side.displayed, spine, pendantClusters]
  | .node ℓ b M S, T, C => by
      obtain ⟨K₁, hK₁⟩ := List.exists_mem_of_ne_nil _ (Brooqs.Side.displayed_ne_nil S T)
      obtain ⟨K₂, hK₂⟩ := List.exists_mem_of_ne_nil _ (Brooqs.Net.displayed_ne_nil M)
      have htop : T ∪ (Brooqs.Side.node ℓ b M S).taxa = T ∪ S.taxa ∪ M.taxa := by
        rw [Brooqs.Side.taxa_node, union_assoc, union_comm M.taxa]
      have IH := mem_side_iff S T C
      have IHM := mem_clusters_iff M C
      simp only [spine, pendantClusters, mem_insert, mem_union, exists_eq_or_imp, htop,
        Brooqs.Side.displayed, List.mem_flatMap, List.mem_map]
      constructor
      · rintro ((rfl | ⟨U, hU, rfl⟩) | hC | hC)
        · exact ⟨_, ⟨K₁, hK₁, K₂, hK₂, rfl⟩, mem_insert_self _ _⟩
        · obtain ⟨K, hK, hC⟩ := IH.1 (Or.inl ⟨U, hU, rfl⟩)
          exact ⟨_, ⟨K, hK, K₂, hK₂, rfl⟩, mem_insert_of_mem (mem_union_left _ hC)⟩
        · obtain ⟨K, hK, hC⟩ := IHM.1 hC
          exact ⟨_, ⟨K₁, hK₁, K, hK, rfl⟩, mem_insert_of_mem (mem_union_right _ hC)⟩
        · obtain ⟨K, hK, hC⟩ := IH.1 (Or.inr hC)
          exact ⟨_, ⟨K, hK, K₂, hK₂, rfl⟩, mem_insert_of_mem (mem_union_left _ hC)⟩
      · rintro ⟨_, ⟨K, hK, K', hK', rfl⟩, hC⟩
        rcases mem_insert.1 hC with h | hC
        · exact Or.inl (Or.inl h.symm)
        rcases mem_union.1 hC with hC | hC
        · rcases IH.2 ⟨K, hK, hC⟩ with ⟨U, hU, rfl⟩ | hC
          · exact Or.inl (Or.inr ⟨U, hU, rfl⟩)
          · exact Or.inr (Or.inr hC)
        · exact Or.inr (Or.inl (IHM.2 ⟨K', hK', hC⟩))
end

/-! ### The clusters of the trees displayed through at most one added edge -/

/-- The clusters of the trees displayed by `Realization.graph t E` through at most one added
edge: the clades of `t`, and the clades of the tree displayed through each added edge
(`EdgeAbove.switchedClades`). -/
def cutSets (t : PhyloTree) (E : Finset (Address × Address)) : Finset (Finset ℕ) :=
  t.clades.toFinset ∪ E.biUnion (EdgeAbove.switchedClades t)

theorem taxaAt_cons {t s : PhyloTree} {b : Bool} (h : t.nodeAt [b] = some s) (y : Address) :
    t.taxaAt (b :: y) = s.taxaAt y := by
  unfold PhyloTree.taxaAt
  rw [show b :: y = [b] ++ y from rfl, PhyloTree.nodeAt_append, h]
  rfl

theorem taxaAt_mem_clades {t : PhyloTree} {y : Address} (hy : y ∈ t.nodes) :
    t.taxaAt y ∈ t.clades := by
  obtain ⟨s, hs⟩ := (PhyloTree.mem_nodes_iff t y).1 hy
  rw [PhyloTree.taxaAt_eq hs]
  exact (PhyloTree.clades_mem_iff t _).2 ⟨y, s, hs, rfl⟩

theorem exists_of_mem_clades {t : PhyloTree} {C : Finset ℕ} (hC : C ∈ t.clades) :
    ∃ y ∈ t.nodes, C = t.taxaAt y := by
  obtain ⟨y, s, hs, rfl⟩ := (PhyloTree.clades_mem_iff t C).1 hC
  exact ⟨y, (PhyloTree.mem_nodes_iff t y).2 ⟨s, hs⟩, (PhyloTree.taxaAt_eq hs).symm⟩

theorem taxa_fork (l r : PhyloTree) : (PhyloTree.fork l r).taxa = l.taxa ∪ r.taxa := by
  simp [PhyloTree.taxa, PhyloTree.labels, List.toFinset_append]

theorem nodeAt_fork_false (l r : PhyloTree) : (PhyloTree.fork l r).nodeAt [false] = some l := by
  simp [PhyloTree.nodeAt]

theorem nodeAt_fork_true (l r : PhyloTree) : (PhyloTree.fork l r).nodeAt [true] = some r := by
  simp [PhyloTree.nodeAt]

/-- At a vertex in the child `b` of the root, the clade of the tree displayed through a pair of
that child is the clade in the child. -/
theorem switchedClade_cons_same {t s : PhyloTree} {b : Bool} (h : t.nodeAt [b] = some s)
    (e : Address × Address) (y : Address) :
    EdgeAbove.switchedClade t (b :: e.1, b :: e.2) (b :: y) = EdgeAbove.switchedClade s e y := by
  simp only [EdgeAbove.switchedClade, taxaAt_cons h, List.cons_prefix_cons, true_and, ne_eq,
    List.cons.injEq]

/-- At a vertex in the other child of the root, the clade of the tree displayed through a pair of
the child `b` is the clade in `t`. -/
theorem switchedClade_cons_other {t : PhyloTree} {b c : Bool} (hbc : c ≠ b)
    (e : Address × Address) (y : Address) :
    EdgeAbove.switchedClade t (b :: e.1, b :: e.2) (c :: y) = t.taxaAt (c :: y) := by
  simp [EdgeAbove.switchedClade, List.cons_prefix_cons, hbc]

/-- At the root, the clade of the tree displayed through a pair of non-root vertices is the set of
all taxa. -/
theorem switchedClade_nil (t : PhyloTree) {e : Address × Address} (h1 : e.1 ≠ [])
    (h2 : e.2 ≠ []) : EdgeAbove.switchedClade t e [] = t.taxa := by
  simp only [EdgeAbove.switchedClade, List.nil_prefix, true_and, ne_eq]
  rw [ite_eq_left (Ne.symm h2), ite_eq_left (Ne.symm h1), PhyloTree.taxaAt_nil]
  exact sdiff_union_of_subset (PhyloTree.taxaAt_subset t _)

theorem mem_nodes_fork {l r : PhyloTree} {x : Address} :
    x ∈ (PhyloTree.fork l r).nodes ↔
      x = [] ∨ (∃ y ∈ l.nodes, x = false :: y) ∨ ∃ y ∈ r.nodes, x = true :: y := by
  simp only [PhyloTree.nodes, mem_insert, mem_union, mem_image]
  constructor
  · rintro (h | ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨y, hy, rfl⟩)
    · exact Or.inr (Or.inr ⟨y, hy, rfl⟩)
  · rintro (h | ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨y, hy, rfl⟩)
    · exact Or.inr (Or.inr ⟨y, hy, rfl⟩)

theorem clades_fork (l r : PhyloTree) (C : Finset ℕ) :
    C ∈ (PhyloTree.fork l r).clades ↔ C = l.taxa ∪ r.taxa ∨ C ∈ l.clades ∨ C ∈ r.clades := by
  simp [PhyloTree.clades]

/-- The clades of the tree displayed through a pair of the child `b` of the root: the set of all
taxa, the clades of the tree displayed in the child through the pair, and the clades of the other
child. -/
theorem mem_switchedClades_lift {l r s o : PhyloTree} {b : Bool}
    (hs : (PhyloTree.fork l r).nodeAt [b] = some s)
    (ho : (PhyloTree.fork l r).nodeAt [!b] = some o) (e : Address × Address) (C : Finset ℕ) :
    C ∈ EdgeAbove.switchedClades (.fork l r) (b :: e.1, b :: e.2) ↔
      C = l.taxa ∪ r.taxa ∨ C ∈ EdgeAbove.switchedClades s e ∨ C ∈ o.clades := by
  have hcases : ∀ x, x ∈ (PhyloTree.fork l r).nodes →
      x = [] ∨ (∃ y ∈ s.nodes, x = b :: y) ∨ ∃ y ∈ o.nodes, x = (!b) :: y := by
    intro x hx
    rcases x with _ | ⟨c, y⟩
    · exact Or.inl rfl
    · by_cases hc : c = b
      · subst hc
        exact Or.inr (Or.inl ⟨y, (mem_nodes_cons hs y).1 hx, rfl⟩)
      · have hc' : c = !b := by cases b <;> cases c <;> simp_all
        subst hc'
        exact Or.inr (Or.inr ⟨y, (mem_nodes_cons ho y).1 hx, rfl⟩)
  have hne : (!b) ≠ b := by cases b <;> simp
  simp only [EdgeAbove.switchedClades, mem_insert, mem_image]
  rw [switchedClade_cons_same hs, taxaAt_cons hs]
  constructor
  · rintro (h | h | ⟨x, hx, rfl⟩)
    · exact Or.inr (Or.inl (Or.inl h))
    · exact Or.inr (Or.inl (Or.inr (Or.inl h)))
    · rcases hcases x hx with rfl | ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
      · left
        rw [switchedClade_nil _ (List.cons_ne_nil _ _) (List.cons_ne_nil _ _), taxa_fork]
      · exact Or.inr (Or.inl (Or.inr (Or.inr ⟨y, hy, (switchedClade_cons_same hs e y).symm⟩)))
      · right; right
        rw [switchedClade_cons_other hne, taxaAt_cons ho]
        exact taxaAt_mem_clades hy
  · rintro (rfl | (h | h | ⟨y, hy, rfl⟩) | h)
    · refine Or.inr (Or.inr ⟨[], PhyloTree.root_mem_nodes _, ?_⟩)
      rw [switchedClade_nil _ (List.cons_ne_nil _ _) (List.cons_ne_nil _ _), taxa_fork]
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨b :: y, (mem_nodes_cons hs y).2 hy, switchedClade_cons_same hs e y⟩)
    · obtain ⟨y, hy, rfl⟩ := exists_of_mem_clades h
      refine Or.inr (Or.inr ⟨(!b) :: y, (mem_nodes_cons ho y).2 hy, ?_⟩)
      rw [switchedClade_cons_other hne, taxaAt_cons ho]

/-- The clusters of the trees displayed through at most one added edge, for the pairs of the two
children of the root: the set of all taxa and the clusters for each child. -/
theorem cutSets_fork (l r : PhyloTree) (E F : Finset (Address × Address)) :
    cutSets (.fork l r) (liftPairs false E ∪ liftPairs true F) =
      insert (l.taxa ∪ r.taxa) (cutSets l E ∪ cutSets r F) := by
  have hl := nodeAt_fork_false l r
  have hr := nodeAt_fork_true l r
  ext C
  simp only [cutSets, mem_union, mem_insert, List.mem_toFinset, mem_biUnion, clades_fork]
  constructor
  · rintro ((h | h | h) | ⟨e, he, hC⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl (Or.inl h))
    · exact Or.inr (Or.inr (Or.inl h))
    · rcases he with he | he <;> obtain ⟨f, hf, rfl⟩ := mem_liftPairs.1 he
      · rcases (mem_switchedClades_lift hl hr f C).1 hC with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl (Or.inr ⟨f, hf, h⟩))
        · exact Or.inr (Or.inr (Or.inl h))
      · rcases (mem_switchedClades_lift hr hl f C).1 hC with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inr ⟨f, hf, h⟩))
        · exact Or.inr (Or.inl (Or.inl h))
  · rintro (h | (h | ⟨f, hf, h⟩) | (h | ⟨f, hf, h⟩))
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inr ⟨_, Or.inl (mem_liftPairs.2 ⟨f, hf, rfl⟩),
        (mem_switchedClades_lift hl hr f C).2 (Or.inr (Or.inl h))⟩
    · exact Or.inl (Or.inr (Or.inr h))
    · exact Or.inr ⟨_, Or.inr (mem_liftPairs.2 ⟨f, hf, rfl⟩),
        (mem_switchedClades_lift hr hl f C).2 (Or.inr (Or.inl h))⟩

/-! ### The paths of the sides in the base tree -/

/-- The clusters of the nodes of a side are sets of taxa below the side. -/
theorem spine_subset : ∀ (S : Brooqs.Side L), ∀ U ∈ spine S, U ⊆ S.taxa
  | .hyb _, U, hU => by simp [spine] at hU
  | .node ℓ b M S, U, hU => by
      rcases mem_insert.1 hU with rfl | hU
      · exact subset_rfl
      · rw [Brooqs.Side.taxa_node]
        exact (spine_subset S U hU).trans subset_union_right

/-- A vertex of the tree of a side with `X` attached that lies strictly above `X` is a node of the
side, with the cluster `U ∪ X` for a cluster `U` of `NMSC.spine`. -/
theorem taxaAt_attach_path : ∀ (S : Brooqs.Side L) (X : PhyloTree), S.IsMetric →
    ∀ y ∈ (attachTree S X).nodes, y <+: hangAddr S → y ≠ hangAddr S →
      ∃ U ∈ spine S, (attachTree S X).taxaAt y = U.map (Coalescent.label L) ∪ X.taxa
  | .hyb _, X, _, y, _, h1, h2 => by
      simp only [hangAddr, Brooqs.Side.nodes, List.length_nil, List.replicate_zero,
        List.prefix_nil] at h1 h2
      exact absurd h1 h2
  | .node ℓ b M S, X, hS, y, hy, h1, h2 => by
      rw [hangAddr_node] at h1 h2
      rcases y with _ | ⟨c, y⟩
      · exact ⟨_, mem_insert_self _ _, by rw [PhyloTree.taxaAt_nil]; exact taxa_attachTree hS X⟩
      · obtain ⟨rfl, h1'⟩ := List.cons_prefix_cons.1 h1
        have hr : (attachTree (.node ℓ b M S) X).nodeAt [true] = some (attachTree S X) :=
          nodeAt_fork_true _ _
        obtain ⟨U, hU, hUy⟩ := taxaAt_attach_path S X hS.2.2.2 y ((mem_nodes_cons hr y).1 hy)
          h1' fun h => h2 (by rw [h])
        exact ⟨U, mem_insert_of_mem hU, by rw [taxaAt_cons hr]; exact hUy⟩

/-- Each cluster `U` of `NMSC.spine` gives the cluster `U ∪ X` of a vertex strictly above `X` in
the tree of the side with `X` attached. -/
theorem exists_attach_path : ∀ (S : Brooqs.Side L) (X : PhyloTree), S.IsMetric →
    ∀ U ∈ spine S, ∃ y ∈ (attachTree S X).nodes, y <+: hangAddr S ∧ y ≠ hangAddr S ∧
      (attachTree S X).taxaAt y = U.map (Coalescent.label L) ∪ X.taxa
  | .hyb _, X, _, U, hU => by simp [spine] at hU
  | .node ℓ b M S, X, hS, U, hU => by
      rw [hangAddr_node]
      have hr : (attachTree (.node ℓ b M S) X).nodeAt [true] = some (attachTree S X) :=
        nodeAt_fork_true _ _
      rcases mem_insert.1 hU with rfl | hU
      · exact ⟨[], PhyloTree.root_mem_nodes _, List.nil_prefix, (List.cons_ne_nil _ _).symm,
          by rw [PhyloTree.taxaAt_nil]; exact taxa_attachTree hS X⟩
      · obtain ⟨y, hy, h1, h2, h3⟩ := exists_attach_path S X hS.2.2.2 U hU
        exact ⟨true :: y, (mem_nodes_cons hr y).2 hy, List.cons_prefix_cons.2 ⟨rfl, h1⟩,
          fun h => h2 (List.cons.inj h).2, by rw [taxaAt_cons hr]; exact h3⟩

/-- A vertex of the tree of a side with its hybrid edge deleted that lies on the path to the last
pendant network is a node of the side, with a cluster of `NMSC.spine`. -/
theorem taxaAt_detach_path : ∀ (S : Brooqs.Side L), S.IsMetric → hasNode S →
    ∀ y ∈ (detachTree S).nodes, y <+: lastAddr S →
      ∃ U ∈ spine S, (detachTree S).taxaAt y = U.map (Coalescent.label L)
  | .hyb _, _, h, _, _, _ => by simp at h
  | .node ℓ b M (.hyb ℓ'), hS, _, y, _, h1 => by
      rw [lastAddr_single, List.prefix_nil] at h1
      subst h1
      exact ⟨_, mem_insert_self _ _, by
        rw [PhyloTree.taxaAt_nil]; exact taxa_detachTree hS (by simp [Brooqs.Side.nodes])⟩
  | .node ℓ b M (.node ℓ' b' M' S), hS, _, y, hy, h1 => by
      rw [lastAddr_node] at h1
      rcases y with _ | ⟨c, y⟩
      · exact ⟨_, mem_insert_self _ _, by
          rw [PhyloTree.taxaAt_nil]; exact taxa_detachTree hS (by simp [Brooqs.Side.nodes])⟩
      · obtain ⟨rfl, h1'⟩ := List.cons_prefix_cons.1 h1
        have hr : (detachTree (.node ℓ b M (.node ℓ' b' M' S))).nodeAt [true] =
            some (detachTree (.node ℓ' b' M' S)) := nodeAt_fork_true _ _
        obtain ⟨U, hU, hUy⟩ := taxaAt_detach_path _ hS.2.2.2 rfl y ((mem_nodes_cons hr y).1 hy)
          h1'
        exact ⟨U, mem_insert_of_mem hU, by rw [taxaAt_cons hr]; exact hUy⟩

/-- Each cluster of `NMSC.spine` is the cluster of a vertex on the path to the last pendant
network in the tree of the side with its hybrid edge deleted. -/
theorem exists_detach_path : ∀ (S : Brooqs.Side L), S.IsMetric →
    ∀ U ∈ spine S, ∃ y ∈ (detachTree S).nodes, y <+: lastAddr S ∧
      (detachTree S).taxaAt y = U.map (Coalescent.label L)
  | .hyb _, _, U, hU => by simp [spine] at hU
  | .node ℓ b M (.hyb ℓ'), hS, U, hU => by
      simp only [spine, mem_insert, notMem_empty, or_false] at hU
      subst hU
      exact ⟨[], PhyloTree.root_mem_nodes _, List.nil_prefix, by
        rw [PhyloTree.taxaAt_nil]; exact taxa_detachTree hS (by simp [Brooqs.Side.nodes])⟩
  | .node ℓ b M (.node ℓ' b' M' S), hS, U, hU => by
      rw [lastAddr_node]
      have hr : (detachTree (.node ℓ b M (.node ℓ' b' M' S))).nodeAt [true] =
          some (detachTree (.node ℓ' b' M' S)) := nodeAt_fork_true _ _
      rcases mem_insert.1 hU with rfl | hU
      · exact ⟨[], PhyloTree.root_mem_nodes _, List.nil_prefix, by
          rw [PhyloTree.taxaAt_nil]; exact taxa_detachTree hS (by simp [Brooqs.Side.nodes])⟩
      · obtain ⟨y, hy, h1, h2⟩ := exists_detach_path _ hS.2.2.2 U hU
        exact ⟨true :: y, (mem_nodes_cons hr y).2 hy, List.cons_prefix_cons.2 ⟨rfl, h1⟩,
          by rw [taxaAt_cons hr]; exact h2⟩

/-! ### The tree displayed through the added edge of a cycle -/

section Cross

variable (l r : PhyloTree) (u w : Address)

theorem switchedClade_cross_left (y : Address) :
    EdgeAbove.switchedClade (.fork l r) (true :: u, false :: w) (false :: y) =
      if y <+: w ∧ y ≠ w then l.taxaAt y \ l.taxaAt w else l.taxaAt y := by
  simp [EdgeAbove.switchedClade, taxaAt_cons (nodeAt_fork_false l r)]

theorem switchedClade_cross_right (y : Address) :
    EdgeAbove.switchedClade (.fork l r) (true :: u, false :: w) (true :: y) =
      r.taxaAt y ∪ if y <+: u ∧ y ≠ u then l.taxaAt w else ∅ := by
  simp [EdgeAbove.switchedClade, taxaAt_cons (nodeAt_fork_true l r),
    taxaAt_cons (nodeAt_fork_false l r)]

variable {l r u w}

/-- The clades of the tree displayed through a pair `(true :: u, false :: w)` of vertices in the
two children of the root: clades of `t`, clades of the vertices `y` on the path to `u` with the
clade of `w` added, and clades of the vertices strictly above `w` with the clade of `w`
removed. -/
theorem mem_switchedClades_cross (hu : u ∈ r.nodes) (hw : w ∈ l.nodes) {C : Finset ℕ}
    (hC : C ∈ EdgeAbove.switchedClades (.fork l r) (true :: u, false :: w)) :
    C ∈ (PhyloTree.fork l r).clades ∨ (∃ y ∈ r.nodes, y <+: u ∧ C = r.taxaAt y ∪ l.taxaAt w) ∨
      ∃ y ∈ l.nodes, y <+: w ∧ y ≠ w ∧ C = l.taxaAt y \ l.taxaAt w := by
  have hl := nodeAt_fork_false l r
  have hr := nodeAt_fork_true l r
  simp only [EdgeAbove.switchedClades, mem_insert, mem_image] at hC
  rcases hC with rfl | rfl | ⟨x, hx, rfl⟩
  · refine Or.inr (Or.inl ⟨u, hu, List.prefix_refl _, ?_⟩)
    rw [switchedClade_cross_right, ite_eq_right (by simp), union_empty, taxaAt_cons hl]
  · left
    exact taxaAt_mem_clades ((mem_nodes_cons hl w).2 hw)
  · rcases mem_nodes_fork.1 hx with rfl | ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
    · left
      rw [switchedClade_nil _ (List.cons_ne_nil _ _) (List.cons_ne_nil _ _),
        ← PhyloTree.taxaAt_nil]
      exact taxaAt_mem_clades (PhyloTree.root_mem_nodes _)
    · rw [switchedClade_cross_left]
      by_cases h : y <+: w ∧ y ≠ w
      · exact Or.inr (Or.inr ⟨y, hy, h.1, h.2, by rw [ite_eq_left h]⟩)
      · left
        rw [ite_eq_right h, ← taxaAt_cons hl]
        exact taxaAt_mem_clades hx
    · rw [switchedClade_cross_right]
      by_cases h : y <+: u ∧ y ≠ u
      · exact Or.inr (Or.inl ⟨y, hy, h.1, by rw [ite_eq_left h]⟩)
      · left
        rw [ite_eq_right h, union_empty, ← taxaAt_cons hr]
        exact taxaAt_mem_clades hx

/-- A vertex `y` on the path to `u` gives the clade of `y` with the clade of `w` added. -/
theorem union_mem_switchedClades_cross (hu : u ∈ r.nodes) {y : Address} (hy : y ∈ r.nodes)
    (hyu : y <+: u) :
    r.taxaAt y ∪ l.taxaAt w ∈ EdgeAbove.switchedClades (.fork l r) (true :: u, false :: w) := by
  have hl := nodeAt_fork_false l r
  have hr := nodeAt_fork_true l r
  simp only [EdgeAbove.switchedClades, mem_insert, mem_image]
  by_cases h : y = u
  · subst h
    left
    rw [switchedClade_cross_right, ite_eq_right (by simp), union_empty, taxaAt_cons hl]
  · right; right
    exact ⟨true :: y, (mem_nodes_cons hr y).2 hy, by
      rw [switchedClade_cross_right, ite_eq_left ⟨hyu, h⟩]⟩

/-- A vertex `y` strictly above `w` gives the clade of `y` with the clade of `w` removed. -/
theorem sdiff_mem_switchedClades_cross {y : Address} (hy : y ∈ l.nodes) (hyw : y <+: w)
    (hne : y ≠ w) :
    l.taxaAt y \ l.taxaAt w ∈ EdgeAbove.switchedClades (.fork l r) (true :: u, false :: w) := by
  simp only [EdgeAbove.switchedClades, mem_insert, mem_image]
  right; right
  exact ⟨false :: y, (mem_nodes_cons (nodeAt_fork_false l r) y).2 hy, by
    rw [switchedClade_cross_left, ite_eq_left ⟨hyw, hne⟩]⟩

end Cross

theorem clades_subset_cutSets {t : PhyloTree} {E : Finset (Address × Address)} {C : Finset ℕ}
    (hC : C ∈ t.clades) : C ∈ cutSets t E :=
  mem_union_left _ (List.mem_toFinset.2 hC)

theorem cutSets_insert (t : PhyloTree) (e : Address × Address)
    (E : Finset (Address × Address)) :
    cutSets t (insert e E) = cutSets t E ∪ EdgeAbove.switchedClades t e := by
  ext C
  simp only [cutSets, biUnion_insert, mem_union]
  tauto

/-- The clusters of the trees displayed through at most one added edge, at a cycle: the side `Sa`
with the tree `X` of the hybrid component attached on the left, the side `Sd` with its hybrid edge
deleted on the right, and the added edge of the cycle. Besides the clusters for the two sides, the
tree displayed through the added edge has the clusters of the nodes of `Sa` without `X`, and those
of the nodes of `Sd` with `X`. -/
theorem cutSets_cycle {Sa Sd : Brooqs.Side L} {X : PhyloTree} {P : Finset (Address × Address)}
    (hSa : Sa.IsMetric) (hSd : Sd.IsMetric) (hd : hasNode Sd)
    (hdisj : Disjoint (Sa.taxa.map (Coalescent.label L)) X.taxa) :
    cutSets (.fork (attachTree Sa X) (detachTree Sd))
        (insert (true :: lastAddr Sd, false :: hangAddr Sa)
          (liftPairs false (attachPairs Sa P) ∪ liftPairs true (detachPairs Sd))) =
      insert ((attachTree Sa X).taxa ∪ (detachTree Sd).taxa)
          (cutSets (attachTree Sa X) (attachPairs Sa P) ∪
            cutSets (detachTree Sd) (detachPairs Sd)) ∪
        ((spine Sa).image (Finset.map (Coalescent.label L)) ∪
          (spine Sd).image fun U => U.map (Coalescent.label L) ∪ X.taxa) := by
  have hu : lastAddr Sd ∈ (detachTree Sd).nodes := lastAddr_mem_nodes Sd
  have hwA : (attachTree Sa X).nodeAt (hangAddr Sa) = some X := nodeAt_hangAddr Sa X
  have hw : hangAddr Sa ∈ (attachTree Sa X).nodes := (PhyloTree.mem_nodes_iff _ _).2 ⟨X, hwA⟩
  have hW : (attachTree Sa X).taxaAt (hangAddr Sa) = X.taxa := PhyloTree.taxaAt_eq hwA
  have hsdiff : ∀ U ∈ spine Sa,
      (U.map (Coalescent.label L) ∪ X.taxa) \ X.taxa = U.map (Coalescent.label L) := by
    intro U hU
    rw [union_sdiff_right, sdiff_eq_self_of_disjoint
      (hdisj.mono_left (map_subset_map.2 (spine_subset Sa U hU)))]
  rw [cutSets_insert, cutSets_fork]
  ext C
  simp only [mem_union, mem_insert, mem_image]
  constructor
  · rintro (h | hC)
    · exact Or.inl h
    rcases mem_switchedClades_cross hu hw hC with h | ⟨y, hy, hyu, rfl⟩ | ⟨y, hy, hyw, hne, rfl⟩
    · rcases (clades_fork _ _ C).1 h with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr (Or.inl (clades_subset_cutSets h)))
      · exact Or.inl (Or.inr (Or.inr (clades_subset_cutSets h)))
    · obtain ⟨U, hU, hUy⟩ := taxaAt_detach_path Sd hSd hd y hy hyu
      exact Or.inr (Or.inr ⟨U, hU, by rw [hUy, hW]⟩)
    · obtain ⟨U, hU, hUy⟩ := taxaAt_attach_path Sa X hSa y hy hyw hne
      exact Or.inr (Or.inl ⟨U, hU, by rw [hUy, hW, hsdiff U hU]⟩)
  · rintro (h | ⟨U, hU, rfl⟩ | ⟨U, hU, rfl⟩)
    · exact Or.inl h
    · obtain ⟨y, hy, hyw, hne, hUy⟩ := exists_attach_path Sa X hSa U hU
      have h := sdiff_mem_switchedClades_cross (r := detachTree Sd) (u := lastAddr Sd) hy hyw
        hne
      rw [hUy, hW, hsdiff U hU] at h
      exact Or.inr h
    · obtain ⟨y, hy, hyu, hUy⟩ := exists_detach_path Sd hSd U hU
      have h := union_mem_switchedClades_cross (l := attachTree Sa X) (w := hangAddr Sa) hu hy
        hyu
      rw [hUy, hW] at h
      exact Or.inr h

/-! ### The two families of clusters are equal -/

/-- The taxa of `N` form a cluster of its displayed trees: the cluster of the root. -/
theorem taxa_mem_clusters : ∀ N : Brooqs.Net L, N.taxa ∈ clusters N
  | .leaf x => by simp [clusters, Brooqs.Net.taxa_leaf]
  | .tree _ N₁ _ N₂ => by rw [Brooqs.Net.taxa_tree]; exact mem_insert_self _ _
  | .cycle _ S₁ S₂ _ H => by rw [Brooqs.Net.taxa_cycle]; exact mem_insert_self _ _

theorem nodup_cycle {γ ℓ : ℝ} {S₁ S₂ : Brooqs.Side L} {H : Brooqs.Net L}
    (h : (Brooqs.Net.cycle γ S₁ S₂ ℓ H).leaves.Nodup) :
    S₁.leaves.Nodup ∧ S₂.leaves.Nodup ∧ H.leaves.Nodup ∧ Disjoint S₁.taxa H.taxa ∧
      Disjoint S₂.taxa H.taxa := by
  simp only [Brooqs.Net.leaves, List.nodup_append] at h
  obtain ⟨⟨h1, h2, h12⟩, h3, h123⟩ := h
  refine ⟨h1, h2, h3, ?_, ?_⟩ <;> rw [disjoint_left] <;> intro a ha hb
  · exact h123 a (List.mem_append_left _ (List.mem_toFinset.1 ha)) a
      (List.mem_toFinset.1 hb) rfl
  · exact h123 a (List.mem_append_right _ (List.mem_toFinset.1 ha)) a
      (List.mem_toFinset.1 hb) rfl

theorem nodup_node {ℓ b : ℝ} {M : Brooqs.Net L} {S : Brooqs.Side L}
    (h : (Brooqs.Side.node ℓ b M S).leaves.Nodup) : M.leaves.Nodup ∧ S.leaves.Nodup := by
  simp only [Brooqs.Side.leaves, List.nodup_append] at h
  exact ⟨h.1, h.2.1⟩

theorem image_image_union (s : Finset (Finset L)) (T : Finset L) :
    (s.image (T ∪ ·)).image (Finset.map (Coalescent.label L)) =
      s.image fun U => U.map (Coalescent.label L) ∪ T.map (Coalescent.label L) := by
  rw [image_image]
  exact image_congr fun U _ => by simp only [Function.comp_apply, map_union, union_comm]

mutual
/-- The clusters of the trees displayed by the graph of `N` through at most one added edge are
the clusters of the displayed trees of `N`, as sets of natural numbers. -/
theorem cutSets_baseTree : ∀ N : Brooqs.Net L, N.WellFormed →
    cutSets (baseTree N) (pairs N) = (clusters N).image (Finset.map (Coalescent.label L))
  | .leaf x, _ => by
      simp [cutSets, baseTree, pairs, clusters, PhyloTree.clades]
  | .tree _ N₁ _ N₂, h => by
      have h₁ : N₁.WellFormed := ⟨h.1.2.2.1, (List.nodup_append.1 h.2).1⟩
      have h₂ : N₂.WellFormed := ⟨h.1.2.2.2, (List.nodup_append.1 h.2).2.1⟩
      change cutSets (.fork (baseTree N₁) (baseTree N₂))
        (liftPairs false (pairs N₁) ∪ liftPairs true (pairs N₂)) = _
      rw [cutSets_fork, cutSets_baseTree N₁ h₁, cutSets_baseTree N₂ h₂, taxa_baseTree h₁.1,
        taxa_baseTree h₂.1]
      simp only [clusters, image_insert, image_union, map_union]
  | .cycle _ S₁ (.hyb ℓ') _ H, h => by
      have hS₁ : S₁.IsMetric := h.1.2.2.2.1
      have hS₂ : (Brooqs.Side.hyb ℓ' : Brooqs.Side L).IsMetric := h.1.2.2.2.2.1
      have hH : H.IsMetric := h.1.2.2.2.2.2.1
      obtain ⟨hn₁, hn₂, hnH, -, -⟩ := nodup_cycle h.2
      have h1 : S₁.nodes ≠ [] := h.1.2.2.2.2.2.2.resolve_right (by simp [Brooqs.Side.nodes])
      have hd : hasNode S₁ := by
        cases S₁ with
        | hyb _ => simp [Brooqs.Side.nodes] at h1
        | node _ _ _ _ => rfl
      rw [baseTree_cycle_hyb, pairs_cycle_hyb,
        cutSets_cycle hS₂ hS₁ hd (by simp [Brooqs.Side.taxa_hyb]),
        cutSets_attachTree _ _ _ hS₂ hn₂, cutSets_detachTree S₁ hS₁ hn₁ hd,
        cutSets_baseTree H ⟨hH, hnH⟩, taxa_attachTree hS₂, taxa_detachTree hS₁ h1,
        taxa_baseTree hH]
      simp only [clusters, spine, pendantClusters, image_insert, image_union, image_empty,
        image_image_union, empty_union, union_empty, Brooqs.Side.taxa_hyb, map_empty]
      rw [show H.taxa.map (Coalescent.label L) ∪ S₁.taxa.map (Coalescent.label L) =
        (S₁.taxa ∪ H.taxa).map (Coalescent.label L) by rw [map_union, union_comm]]
      ext C
      simp only [mem_union, mem_insert]
      tauto
  | .cycle _ S₁ (.node ℓ' b' M S) _ H, h => by
      have hS₁ : S₁.IsMetric := h.1.2.2.2.1
      have hS₂ : (Brooqs.Side.node ℓ' b' M S).IsMetric := h.1.2.2.2.2.1
      have hH : H.IsMetric := h.1.2.2.2.2.2.1
      obtain ⟨hn₁, hn₂, hnH, hdisj, -⟩ := nodup_cycle h.2
      have hdisj' : Disjoint (S₁.taxa.map (Coalescent.label L)) (baseTree H).taxa := by
        rw [taxa_baseTree hH, disjoint_map]
        exact hdisj
      rw [baseTree_cycle_node, pairs_cycle_node, cutSets_cycle hS₁ hS₂ rfl hdisj',
        cutSets_attachTree S₁ _ _ hS₁ hn₁, cutSets_detachTree _ hS₂ hn₂ rfl,
        cutSets_baseTree H ⟨hH, hnH⟩, taxa_attachTree hS₁,
        taxa_detachTree hS₂ (by simp [Brooqs.Side.nodes]), taxa_baseTree hH]
      simp only [clusters, image_insert, image_union, image_image_union]
      rw [show S₁.taxa.map (Coalescent.label L) ∪ H.taxa.map (Coalescent.label L) ∪
          (Brooqs.Side.node ℓ' b' M S).taxa.map (Coalescent.label L) =
        (S₁.taxa ∪ (Brooqs.Side.node ℓ' b' M S).taxa ∪ H.taxa).map (Coalescent.label L) by
          rw [map_union, map_union, union_assoc, union_assoc, union_comm (H.taxa.map _)]]
      ext C
      simp only [mem_union, mem_insert]
      tauto

/-- The clusters of the trees displayed through at most one added edge in the tree of a side with
`X` attached: the clusters `U ∪ X` of the nodes of the side, the clusters of the pendant networks,
and those of `X`. -/
theorem cutSets_attachTree : ∀ (S : Brooqs.Side L) (X : PhyloTree)
    (P : Finset (Address × Address)), S.IsMetric → S.leaves.Nodup →
    cutSets (attachTree S X) (attachPairs S P) =
      (spine S).image (fun U => U.map (Coalescent.label L) ∪ X.taxa) ∪
        (pendantClusters S).image (Finset.map (Coalescent.label L)) ∪ cutSets X P
  | .hyb _, X, P, _, _ => by simp [attachTree, attachPairs, spine, pendantClusters]
  | .node ℓ b M S, X, P, hS, hnd => by
      obtain ⟨hnM, hnS⟩ := nodup_node hnd
      change cutSets (.fork (baseTree M) (attachTree S X))
        (liftPairs false (pairs M) ∪ liftPairs true (attachPairs S P)) = _
      rw [cutSets_fork, cutSets_baseTree M ⟨hS.2.2.1, hnM⟩, cutSets_attachTree S X P hS.2.2.2 hnS,
        taxa_baseTree hS.2.2.1, taxa_attachTree hS.2.2.2]
      simp only [spine, pendantClusters, image_insert, image_union, Brooqs.Side.taxa_node,
        map_union, union_assoc]
      ext C
      simp only [mem_union, mem_insert]
      tauto

/-- The clusters of the trees displayed through at most one added edge in the tree of a side with
a node whose hybrid edge is deleted: the clusters of the nodes of the side and the clusters of
the pendant networks. -/
theorem cutSets_detachTree : ∀ (S : Brooqs.Side L), S.IsMetric → S.leaves.Nodup → hasNode S →
    cutSets (detachTree S) (detachPairs S) =
      (spine S).image (Finset.map (Coalescent.label L)) ∪
        (pendantClusters S).image (Finset.map (Coalescent.label L))
  | .hyb _, _, _, h => by simp at h
  | .node ℓ b M (.hyb ℓ'), hS, hnd, _ => by
      obtain ⟨hnM, -⟩ := nodup_node hnd
      rw [detachTree_single, detachPairs_single, cutSets_baseTree M ⟨hS.2.2.1, hnM⟩]
      have hM : (Brooqs.Side.node ℓ b M (.hyb ℓ')).taxa = M.taxa := by
        rw [Brooqs.Side.taxa_node, Brooqs.Side.taxa_hyb, union_empty]
      simp only [spine, pendantClusters, hM, insert_empty_eq, image_singleton, union_empty]
      rw [union_eq_right.2 (singleton_subset_iff.2 (mem_image_of_mem _ (taxa_mem_clusters M)))]
  | .node ℓ b M (.node ℓ' b' M' S), hS, hnd, _ => by
      obtain ⟨hnM, hnS⟩ := nodup_node hnd
      rw [detachTree_node, detachPairs_node, cutSets_fork, cutSets_baseTree M ⟨hS.2.2.1, hnM⟩,
        cutSets_detachTree _ hS.2.2.2 hnS rfl, taxa_baseTree hS.2.2.1,
        taxa_detachTree hS.2.2.2 (by simp [Brooqs.Side.nodes])]
      simp only [spine, pendantClusters, image_insert, image_union, Brooqs.Side.taxa_node,
        map_union]
      ext C
      simp only [mem_union, mem_insert]
      tauto
end

/-! ### The base tree is a displayed tree of `N` -/

mutual
/-- The clusters of the displayed tree of `N` that, at each cycle, deletes the hybrid edge of the
side `S₂` if `S₂` has a node, and the hybrid edge of `S₁` otherwise: the tree `NMSC.baseTree N`. -/
def baseClusters : Brooqs.Net L → Finset (Finset L)
  | .leaf x => {{x}}
  | .tree _ N₁ _ N₂ => insert (N₁.taxa ∪ N₂.taxa) (baseClusters N₁ ∪ baseClusters N₂)
  | .cycle _ S₁ S₂ _ H =>
      if hasNode S₂ then
        insert (S₁.taxa ∪ S₂.taxa ∪ H.taxa)
          (baseClusters H ∪ sideBaseClusters S₁ H.taxa ∪ sideBaseClusters S₂ ∅)
      else
        insert (S₁.taxa ∪ S₂.taxa ∪ H.taxa)
          (baseClusters H ∪ sideBaseClusters S₁ ∅ ∪ sideBaseClusters S₂ H.taxa)

/-- The clusters along a side in the displayed tree `NMSC.baseClusters`, with the taxa `T` below
its hybrid edge. -/
def sideBaseClusters : Brooqs.Side L → Finset L → Finset (Finset L)
  | .hyb _, _ => ∅
  | .node _ _ M S, T => insert (T ∪ S.taxa ∪ M.taxa) (sideBaseClusters S T ∪ baseClusters M)
end

mutual
/-- `NMSC.baseClusters N` is a displayed tree of `N`. -/
theorem baseClusters_mem_displayed : ∀ N : Brooqs.Net L, baseClusters N ∈ N.displayed
  | .leaf x => by simp [baseClusters, Brooqs.Net.displayed]
  | .tree _ N₁ _ N₂ => by
      simp only [baseClusters, Brooqs.Net.displayed, List.mem_flatMap, List.mem_map]
      exact ⟨_, baseClusters_mem_displayed N₁, _, baseClusters_mem_displayed N₂, rfl⟩
  | .cycle _ S₁ (.hyb ℓ') _ H => by
      simp only [baseClusters, hasNode_hyb, Bool.false_eq_true, ↓reduceIte,
        Brooqs.Net.displayed, List.mem_flatMap, List.mem_append, List.mem_map]
      exact ⟨_, baseClusters_mem_displayed H, Or.inr ⟨_, sideBaseClusters_mem_displayed S₁ ∅,
        _, sideBaseClusters_mem_displayed _ H.taxa, rfl⟩⟩
  | .cycle _ S₁ (.node ℓ' b M S) _ H => by
      simp only [baseClusters, hasNode_node, ↓reduceIte, Brooqs.Net.displayed,
        List.mem_flatMap, List.mem_append, List.mem_map]
      exact ⟨_, baseClusters_mem_displayed H, Or.inl ⟨_, sideBaseClusters_mem_displayed S₁ H.taxa,
        _, sideBaseClusters_mem_displayed _ ∅, rfl⟩⟩

/-- `NMSC.sideBaseClusters S T` is among the clusters along the side `S` of the displayed
trees. -/
theorem sideBaseClusters_mem_displayed :
    ∀ (S : Brooqs.Side L) (T : Finset L), sideBaseClusters S T ∈ S.displayed T
  | .hyb _, T => by simp [sideBaseClusters, Brooqs.Side.displayed]
  | .node _ _ M S, T => by
      simp only [sideBaseClusters, Brooqs.Side.displayed, List.mem_flatMap, List.mem_map]
      exact ⟨_, sideBaseClusters_mem_displayed S T, _, baseClusters_mem_displayed M, rfl⟩
end

/-- The taxa of `N` form a cluster of its displayed tree `NMSC.baseClusters N`. -/
theorem taxa_mem_baseClusters : ∀ N : Brooqs.Net L, N.taxa ∈ baseClusters N
  | .leaf x => by simp [baseClusters, Brooqs.Net.taxa_leaf]
  | .tree _ N₁ _ N₂ => by rw [Brooqs.Net.taxa_tree]; exact mem_insert_self _ _
  | .cycle _ S₁ S₂ _ H => by
      rw [Brooqs.Net.taxa_cycle]
      unfold baseClusters
      split <;> exact mem_insert_self _ _

theorem clades_toFinset_fork (l r : PhyloTree) :
    (PhyloTree.fork l r).clades.toFinset =
      insert (l.taxa ∪ r.taxa) (l.clades.toFinset ∪ r.clades.toFinset) := by
  ext C
  simp only [List.mem_toFinset, clades_fork, mem_insert, mem_union]

mutual
/-- The clades of the base tree of `N` are the clusters of the displayed tree
`NMSC.baseClusters N`, as sets of natural numbers. -/
theorem clades_baseTree : ∀ N : Brooqs.Net L, N.WellFormed →
    (baseTree N).clades.toFinset = (baseClusters N).image (Finset.map (Coalescent.label L))
  | .leaf x, _ => by simp [baseTree, baseClusters, PhyloTree.clades]
  | .tree _ N₁ _ N₂, h => by
      have h₁ : N₁.WellFormed := ⟨h.1.2.2.1, (List.nodup_append.1 h.2).1⟩
      have h₂ : N₂.WellFormed := ⟨h.1.2.2.2, (List.nodup_append.1 h.2).2.1⟩
      change (PhyloTree.fork (baseTree N₁) (baseTree N₂)).clades.toFinset = _
      rw [clades_toFinset_fork, clades_baseTree N₁ h₁, clades_baseTree N₂ h₂,
        taxa_baseTree h₁.1, taxa_baseTree h₂.1]
      simp only [baseClusters, image_insert, image_union, map_union]
  | .cycle _ S₁ (.hyb ℓ') _ H, h => by
      have hS₁ : S₁.IsMetric := h.1.2.2.2.1
      have hS₂ : (Brooqs.Side.hyb ℓ' : Brooqs.Side L).IsMetric := h.1.2.2.2.2.1
      have hH : H.IsMetric := h.1.2.2.2.2.2.1
      obtain ⟨hn₁, hn₂, hnH, -, -⟩ := nodup_cycle h.2
      have h1 : S₁.nodes ≠ [] := h.1.2.2.2.2.2.2.resolve_right (by simp [Brooqs.Side.nodes])
      have hd : hasNode S₁ := by
        cases S₁ with
        | hyb _ => simp [Brooqs.Side.nodes] at h1
        | node _ _ _ _ => rfl
      rw [baseTree_cycle_hyb, clades_toFinset_fork,
        clades_attachTree _ _ H.taxa hS₂ hn₂ (taxa_baseTree hH),
        clades_detachTree S₁ hS₁ hn₁ hd, clades_baseTree H ⟨hH, hnH⟩, taxa_attachTree hS₂,
        taxa_detachTree hS₁ h1, taxa_baseTree hH]
      simp only [baseClusters, hasNode_hyb, Bool.false_eq_true, ↓reduceIte, sideBaseClusters,
        image_insert, image_union, image_empty, empty_union, union_empty, Brooqs.Side.taxa_hyb,
        map_empty, map_union]
      ext C
      simp only [mem_union, mem_insert]
      rw [show S₁.taxa.map (Coalescent.label L) ∪ H.taxa.map (Coalescent.label L) =
        H.taxa.map (Coalescent.label L) ∪ S₁.taxa.map (Coalescent.label L) from union_comm _ _]
  | .cycle _ S₁ (.node ℓ' b' M S) _ H, h => by
      have hS₁ : S₁.IsMetric := h.1.2.2.2.1
      have hS₂ : (Brooqs.Side.node ℓ' b' M S).IsMetric := h.1.2.2.2.2.1
      have hH : H.IsMetric := h.1.2.2.2.2.2.1
      obtain ⟨hn₁, hn₂, hnH, -, -⟩ := nodup_cycle h.2
      rw [baseTree_cycle_node, clades_toFinset_fork,
        clades_attachTree S₁ _ H.taxa hS₁ hn₁ (taxa_baseTree hH),
        clades_detachTree _ hS₂ hn₂ rfl, clades_baseTree H ⟨hH, hnH⟩, taxa_attachTree hS₁,
        taxa_detachTree hS₂ (by simp [Brooqs.Side.nodes]), taxa_baseTree hH]
      simp only [baseClusters, hasNode_node, ↓reduceIte, image_insert, image_union, map_union]
      ext C
      simp only [mem_union, mem_insert]
      rw [show S₁.taxa.map (Coalescent.label L) ∪ H.taxa.map (Coalescent.label L) ∪
          (Brooqs.Side.node ℓ' b' M S).taxa.map (Coalescent.label L) =
        S₁.taxa.map (Coalescent.label L) ∪ (Brooqs.Side.node ℓ' b' M S).taxa.map
          (Coalescent.label L) ∪ H.taxa.map (Coalescent.label L) by
          rw [union_assoc, union_assoc, union_comm (H.taxa.map _)]]
      tauto

/-- The clades of the tree of a side with `X` attached, for `X` with the taxa `T`: the clusters
along the side in `NMSC.sideBaseClusters S T`, and the clades of `X`. -/
theorem clades_attachTree : ∀ (S : Brooqs.Side L) (X : PhyloTree) (T : Finset L), S.IsMetric →
    S.leaves.Nodup → X.taxa = T.map (Coalescent.label L) →
    (attachTree S X).clades.toFinset =
      (sideBaseClusters S T).image (Finset.map (Coalescent.label L)) ∪ X.clades.toFinset
  | .hyb _, X, T, _, _, _ => by simp [attachTree, sideBaseClusters]
  | .node ℓ b M S, X, T, hS, hnd, hX => by
      obtain ⟨hnM, hnS⟩ := nodup_node hnd
      change (PhyloTree.fork (baseTree M) (attachTree S X)).clades.toFinset = _
      rw [clades_toFinset_fork, clades_baseTree M ⟨hS.2.2.1, hnM⟩,
        clades_attachTree S X T hS.2.2.2 hnS hX, taxa_baseTree hS.2.2.1,
        taxa_attachTree hS.2.2.2, hX]
      simp only [sideBaseClusters, image_insert, image_union, map_union]
      rw [show M.taxa.map (Coalescent.label L) ∪ (S.taxa.map (Coalescent.label L) ∪
          T.map (Coalescent.label L)) = T.map (Coalescent.label L) ∪
          S.taxa.map (Coalescent.label L) ∪ M.taxa.map (Coalescent.label L) by
        rw [union_comm, union_comm (S.taxa.map _)]]
      ext C
      simp only [mem_union, mem_insert]
      tauto

/-- The clades of the tree of a side with a node whose hybrid edge is deleted: the clusters along
the side in `NMSC.sideBaseClusters S ∅`. -/
theorem clades_detachTree : ∀ (S : Brooqs.Side L), S.IsMetric → S.leaves.Nodup → hasNode S →
    (detachTree S).clades.toFinset =
      (sideBaseClusters S ∅).image (Finset.map (Coalescent.label L))
  | .hyb _, _, _, h => by simp at h
  | .node ℓ b M (.hyb ℓ'), hS, hnd, _ => by
      obtain ⟨hnM, -⟩ := nodup_node hnd
      rw [detachTree_single, clades_baseTree M ⟨hS.2.2.1, hnM⟩]
      simp only [sideBaseClusters, Brooqs.Side.taxa_hyb, empty_union, union_empty]
      rw [insert_eq_of_mem (taxa_mem_baseClusters M)]
  | .node ℓ b M (.node ℓ' b' M' S), hS, hnd, _ => by
      obtain ⟨hnM, hnS⟩ := nodup_node hnd
      rw [detachTree_node, clades_toFinset_fork, clades_baseTree M ⟨hS.2.2.1, hnM⟩,
        clades_detachTree _ hS.2.2.2 hnS rfl, taxa_baseTree hS.2.2.1,
        taxa_detachTree hS.2.2.2 (by simp [Brooqs.Side.nodes])]
      simp only [sideBaseClusters, image_insert, image_union, map_union, empty_union]
      rw [show M.taxa.map (Coalescent.label L) ∪ (Brooqs.Side.node ℓ' b' M' S).taxa.map
          (Coalescent.label L) = (Brooqs.Side.node ℓ' b' M' S).taxa.map (Coalescent.label L) ∪
          M.taxa.map (Coalescent.label L) from union_comm _ _]
      ext C
      simp only [mem_union, mem_insert]
      tauto
end

/-! ### The graph of `N` -/

theorem induced_iff_clades (q : Quartet) (t : PhyloTree) :
    q.induced t = true ↔ q.taxa ⊆ t.taxa ∧ ∃ C ∈ t.clades, q.cutBy C = true := by
  simp [Quartet.induced, List.any_eq_true]

/-- The taxa of the base tree of a network with all the taxa of `L` are the taxa `L`. -/
theorem taxa_baseTree_eq {N : Brooqs.Net L} (hN : N.IsMetric) (htaxa : ∀ x : L, x ∈ N.taxa) :
    (baseTree N).taxa = L := by
  rw [taxa_baseTree hN]
  ext a
  simp only [mem_map, Coalescent.label, Function.Embedding.subtype_apply]
  constructor
  · rintro ⟨x, -, rfl⟩
    exact x.2
  · intro ha
    exact ⟨⟨a, ha⟩, htaxa _, rfl⟩

/-- **Section 3.2: the graph of a network of the NMSC.** For a metric level-1 network `N` with
distinct leaf labels on the taxa `L`, the network `Realization.graph (baseTree N) (pairs N)` of
CAMUS, obtained from the base tree of `N` by adding an edge above each pair of `NMSC.pairs N`,
displays exactly the quartet trees that `N` displays: Q(N_r) is the same in the two
representations. -/
theorem graph_displaysQuartet_iff {N : Brooqs.Net L} (hN : N.WellFormed)
    (htaxa : ∀ x : L, x ∈ N.taxa) (q : Quartet) :
    (Realization.graph (baseTree N) (pairs N)).DisplaysQuartet q ↔ DisplaysQuartet N q := by
  rw [Realization.graph_displays_iff_cuts (wellLabelled_baseTree hN) (separated_pairs N),
    induced_iff_clades, taxa_baseTree_eq hN.1 htaxa]
  have hcut : ((∃ C ∈ (baseTree N).clades, q.cutBy C = true) ∨
      ∃ e ∈ pairs N, ∃ C ∈ EdgeAbove.switchedClades (baseTree N) e, q.cutBy C = true) ↔
      ∃ C ∈ cutSets (baseTree N) (pairs N), q.cutBy C = true := by
    simp only [cutSets, mem_union, List.mem_toFinset, mem_biUnion]
    constructor
    · rintro (⟨C, hC, h⟩ | ⟨e, he, C, hC, h⟩)
      · exact ⟨C, Or.inl hC, h⟩
      · exact ⟨C, Or.inr ⟨e, he, hC⟩, h⟩
    · rintro ⟨C, hC | ⟨e, he, hC⟩, h⟩
      · exact Or.inl ⟨C, hC, h⟩
      · exact Or.inr ⟨e, he, C, hC, h⟩
  obtain ⟨K₀, hK₀⟩ := List.exists_mem_of_ne_nil _ (Brooqs.Net.displayed_ne_nil N)
  rw [cutSets_baseTree N hN] at hcut
  simp only [DisplaysQuartet, Coalescent.Induces]
  constructor
  · rintro ⟨hq, h | h⟩
    · obtain ⟨C, hC, hcutC⟩ := hcut.1 (Or.inl h.2)
      obtain ⟨A, hA, rfl⟩ := mem_image.1 hC
      obtain ⟨K, hK, hAK⟩ := (mem_clusters_iff N A).1 hA
      exact ⟨K, hK, hq, A, hAK, hcutC⟩
    · obtain ⟨C, hC, hcutC⟩ := hcut.1 (Or.inr h)
      obtain ⟨A, hA, rfl⟩ := mem_image.1 hC
      obtain ⟨K, hK, hAK⟩ := (mem_clusters_iff N A).1 hA
      exact ⟨K, hK, hq, A, hAK, hcutC⟩
  · rintro ⟨K, hK, hq, A, hAK, hcutA⟩
    have h := hcut.2 ⟨_, mem_image_of_mem _ ((mem_clusters_iff N A).2 ⟨K, hK, hAK⟩), hcutA⟩
    rcases h with h | h
    · exact ⟨hq, Or.inl ⟨hq, h⟩⟩
    · exact ⟨hq, Or.inr h⟩

/-- **Section 3.2: the graph of a network of the NMSC is built on its base tree.** For a metric
level-1 network `N` with distinct leaf labels, `Realization.graph (baseTree N) (pairs N)` is a
rooted binary level-1 network built on the base tree of `N`, with the root kept
(`Realization.levelOne`, `Realization.support`). -/
theorem graph_anchoredExtension {N : Brooqs.Net L} (hN : N.WellFormed) :
    (Realization.graph (baseTree N) (pairs N)).AnchoredExtension (baseTree N) :=
  ⟨Realization.levelOne _ (wellLabelled_baseTree hN) _ (separated_pairs N),
    Realization.supportEdges _ _,
    ⟨Realization.support _ (wellLabelled_baseTree hN) _ (separated_pairs N)⟩⟩

/-- **Section 3.2: the base tree is a displayed tree of `N`.** For a metric level-1 network `N`
with distinct leaf labels on the taxa `L`, the base tree of `N` is in T(N) (`NMSC.DisplaysTree`):
the displayed tree `NMSC.baseClusters N` of `N` induces exactly the quartet trees that the base tree
induces. -/
theorem displaysTree_baseTree {N : Brooqs.Net L} (hN : N.WellFormed)
    (htaxa : ∀ x : L, x ∈ N.taxa) : DisplaysTree N (baseTree N) := by
  refine ⟨baseClusters N, baseClusters_mem_displayed N, fun q => ?_⟩
  rw [induced_iff_clades, taxa_baseTree_eq hN.1 htaxa]
  simp only [Coalescent.Induces]
  refine and_congr_right fun _ => ?_
  constructor
  · rintro ⟨A, hA, h⟩
    refine ⟨A.map (Coalescent.label L), ?_, h⟩
    rw [← List.mem_toFinset, clades_baseTree N hN]
    exact mem_image_of_mem _ hA
  · rintro ⟨C, hC, h⟩
    rw [← List.mem_toFinset, clades_baseTree N hN] at hC
    obtain ⟨A, hA, rfl⟩ := mem_image.1 hC
    exact ⟨A, hA, h⟩

/-! ### Reticulations -/

mutual
/-- The number of cycles of `N`. -/
def cycleCount : Brooqs.Net L → ℕ
  | .leaf _ => 0
  | .tree _ N₁ _ N₂ => cycleCount N₁ + cycleCount N₂
  | .cycle _ S₁ S₂ _ H => cycleCount H + sideCycleCount S₁ + sideCycleCount S₂ + 1

/-- The number of cycles in the networks hanging from the nodes of a side. -/
def sideCycleCount : Brooqs.Side L → ℕ
  | .hyb _ => 0
  | .node _ _ M S => cycleCount M + sideCycleCount S
end

theorem card_liftPairs (b : Bool) (E : Finset (Address × Address)) :
    #(liftPairs b E) = #E :=
  card_image_of_injective _ fun e f h => by
    simp only [Prod.mk.injEq, List.cons.injEq, true_and] at h
    exact Prod.ext h.1 h.2

theorem card_fork_pairs (E F : Finset (Address × Address)) :
    #(liftPairs false E ∪ liftPairs true F) = #E + #F := by
  have hdisj : Disjoint (liftPairs false E) (liftPairs true F) := by
    rw [disjoint_left]
    intro e he hf
    obtain ⟨f, -, rfl⟩ := mem_liftPairs.1 he
    obtain ⟨g, -, hg⟩ := mem_liftPairs.1 hf
    simp at hg
  rw [card_union_of_disjoint hdisj, card_liftPairs, card_liftPairs]

theorem cycle_pair_notMem (u w : Address) (E F : Finset (Address × Address)) :
    (true :: u, false :: w) ∉ liftPairs false E ∪ liftPairs true F := by
  intro h
  rcases mem_union.1 h with h | h <;> obtain ⟨f, -, hf⟩ := mem_liftPairs.1 h <;> simp at hf

mutual
/-- There is one pair for each cycle of `N`. -/
theorem card_pairs : ∀ N : Brooqs.Net L, #(pairs N) = cycleCount N
  | .leaf _ => rfl
  | .tree _ N₁ _ N₂ => by
      change #(liftPairs false (pairs N₁) ∪ liftPairs true (pairs N₂)) = _
      rw [card_fork_pairs, card_pairs N₁, card_pairs N₂]
      rfl
  | .cycle _ S₁ (.hyb ℓ') _ H => by
      rw [pairs_cycle_hyb, card_insert_of_notMem (cycle_pair_notMem _ _ _ _), card_fork_pairs,
        card_attachPairs, card_detachPairs, card_pairs H]
      simp only [cycleCount, sideCycleCount]
      omega
  | .cycle _ S₁ (.node ℓ' b M S) _ H => by
      rw [pairs_cycle_node, card_insert_of_notMem (cycle_pair_notMem _ _ _ _), card_fork_pairs,
        card_attachPairs, card_detachPairs, card_pairs H]
      simp only [cycleCount]
      omega

/-- The pairs below a side, with the pairs `P` of the attached tree. -/
theorem card_attachPairs : ∀ (S : Brooqs.Side L) (P : Finset (Address × Address)),
    #(attachPairs S P) = sideCycleCount S + #P
  | .hyb _, P => by simp [attachPairs, sideCycleCount]
  | .node _ _ M S, P => by
      change #(liftPairs false (pairs M) ∪ liftPairs true (attachPairs S P)) = _
      rw [card_fork_pairs, card_pairs M, card_attachPairs S P]
      simp only [sideCycleCount]
      omega

/-- The pairs below a side whose hybrid edge is deleted. -/
theorem card_detachPairs : ∀ S : Brooqs.Side L, #(detachPairs S) = sideCycleCount S
  | .hyb _ => rfl
  | .node _ _ M (.hyb _) => by
      rw [detachPairs_single, card_pairs M]
      simp [sideCycleCount]
  | .node _ _ M (.node ℓ b M' S) => by
      rw [detachPairs_node, card_fork_pairs, card_pairs M, card_detachPairs]
      rfl
end

/-- The graph of `N` has one reticulation for each cycle of `N`
(`Realization.reticulationCount_eq_card`). -/
theorem graph_reticulationCount (N : Brooqs.Net L) :
    (Realization.graph (baseTree N) (pairs N)).reticulationCount = cycleCount N := by
  rw [Realization.reticulationCount_eq_card _ _ (separated_pairs N), card_pairs]

end NMSC

end Camus
