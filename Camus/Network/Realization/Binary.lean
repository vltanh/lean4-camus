module

public import Camus.Network.Realization.DAG
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

@[expose] public section

namespace Camus.Realization

theorem graph_leaf_injective (t : PhyloTree) (E : Finset Pair) :
    Set.InjOn (graph t E).leaf (graph t E).taxa := by
  intro a ha b hb h
  have heq := Address.code_injective h
  have hnodea := leafAddress_nodeAt ha
  have hnodeb := leafAddress_nodeAt hb
  rw [heq] at hnodea
  have hleaves := Option.some.inj (hnodea.symm.trans hnodeb)
  exact PhyloTree.leaf.inj hleaves

theorem graph_leaf_laws (t : PhyloTree) (E : Finset Pair)
    (hE : E ⊆ EdgeAbove.candidates t) {a : ℕ} (ha : a ∈ (graph t E).taxa) :
    (graph t E).leaf a ∈ (graph t E).vertices ∧
    (graph t E).indegree ((graph t E).leaf a) =
      (if (graph t E).leaf a = (graph t E).root then 0 else 1) ∧
    (graph t E).outdegree ((graph t E).leaf a) = 0 := by
  classical
  have hp := leafAddress_mem_nodes ha
  refine ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨_, hp, rfl⟩), ?_, ?_⟩
  · change (graph t E).indegree (Address.code (leafAddress t a)) = _
    by_cases hroot : (graph t E).leaf a = (graph t E).root
    · have hr : Address.code (leafAddress t a) = (graph t E).root := hroot
      rw [hr]
      simpa [hroot] using graph_root_indegree t E
    · rw [ite_eq_right hroot]
      exact graph_indegree_code t E hE hp (fun h => hroot (congrArg Address.code h))
  · exact graph_outdegree_leaf hE (leafAddress_nodeAt ha)

theorem graph_leaf_characterization (t : PhyloTree) (ht : t.WellLabelled) (E : Finset Pair)
    (hE : E ⊆ EdgeAbove.candidates t) {v : ℕ} (hv : v ∈ (graph t E).vertices) :
    (graph t E).outdegree v = 0 ↔ ∃ a ∈ (graph t E).taxa, (graph t E).leaf a = v := by
  classical
  constructor
  · intro hz
    rcases Finset.mem_union.mp hv with horiginal | hadded
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp horiginal
      obtain ⟨s, hs⟩ := (t.mem_nodes_iff p).mp hp
      cases s with
      | leaf a =>
        have ha : a ∈ (graph t E).taxa := List.mem_toFinset.mpr (PhyloTree.leaf_label_mem hs)
        exact ⟨a, ha, congrArg Address.code (leafAddress_eq ht hs)⟩
      | fork l r =>
        rw [graph_outdegree_fork hE hs] at hz
        omega
    · obtain ⟨e, he, hv⟩ := Finset.mem_biUnion.mp hadded
      rcases Finset.mem_insert.mp hv with rfl | hr
      · rw [(endpoint_degrees t E hE he).2.1] at hz
        omega
      · have heq := Finset.mem_singleton.mp hr
        rw [heq, (endpoint_degrees t E hE he).2.2.2] at hz
        omega
  · rintro ⟨a, ha, rfl⟩
    exact (graph_leaf_laws t E hE ha).2.2

theorem graph_nonroot_binary (t : PhyloTree) (E : Finset Pair)
    (hE : E ⊆ EdgeAbove.candidates t) {v : ℕ}
    (hv : v ∈ (graph t E).vertices) (hvroot : v ≠ (graph t E).root) :
    ((graph t E).indegree v = 1 ∧ (graph t E).outdegree v = 0) ∨
    ((graph t E).indegree v = 1 ∧ (graph t E).outdegree v = 2) ∨
    ((graph t E).indegree v = 2 ∧ (graph t E).outdegree v = 1) := by
  classical
  rcases Finset.mem_union.mp hv with horiginal | hadded
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp horiginal
    have hpin := graph_indegree_code t E hE hp (fun h => hvroot (congrArg Address.code h))
    obtain ⟨s, hs⟩ := (t.mem_nodes_iff p).mp hp
    cases s with
    | leaf a => exact Or.inl ⟨hpin, graph_outdegree_leaf hE hs⟩
    | fork l r => exact Or.inr (Or.inl ⟨hpin, graph_outdegree_fork hE hs⟩)
  · obtain ⟨e, he, hv⟩ := Finset.mem_biUnion.mp hadded
    rcases Finset.mem_insert.mp hv with rfl | hr
    · exact Or.inr (Or.inl ⟨(endpoint_degrees t E hE he).1,
        (endpoint_degrees t E hE he).2.1⟩)
    · rw [Finset.mem_singleton.mp hr]
      exact Or.inr (Or.inr (endpoint_degrees t E hE he).2.2)

/-- All directed, binary and labelling obligations are proved independently
of the undirected cycle classification. The final cycle condition is supplied
by the separately proved construction theorem. -/
theorem levelOne_of_cycle_disjoint (t : PhyloTree) (ht : t.WellLabelled)
    (E : Finset Pair) (hE : EdgeAbove.CycleSeparated t E)
    (hcycles : ∀ v w (c : (graph t E).underlying.Walk v v)
      (d : (graph t E).underlying.Walk w w), c.IsCycle → d.IsCycle →
        c.edges.toFinset ≠ d.edges.toFinset → Disjoint c.support.toFinset d.support.toFinset) :
    (graph t E).RootedBinaryLevelOne := by
  classical
  refine ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨[], t.root_mem_nodes, rfl⟩),
    ?_, graph_dag t E hE, graph_root_indegree t E, ?_, ?_, graph_leaf_injective t E,
    ?_, ?_, ?_, hcycles⟩
  · intro e he
    exact graph_edge_endpoints t E hE.1 he
  · cases t with
    | leaf a => exact Or.inl (graph_outdegree_leaf hE.1 rfl)
    | fork l r => exact Or.inr (graph_outdegree_fork hE.1 rfl)
  · intro v hv
    exact Relation.ReflTransGen.mono (fun u v he => Finset.mem_union_left _ he) _ _
      (support_reaches t E hE.1 hv)
  · intro a ha
    exact graph_leaf_laws t E hE.1 ha
  · intro v hv
    exact graph_leaf_characterization t ht E hE.1 hv
  · intro v hv hvroot
    exact graph_nonroot_binary t E hE.1 hv hvroot

end Camus.Realization
