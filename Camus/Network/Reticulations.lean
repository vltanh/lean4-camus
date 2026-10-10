module

public import Camus.Network.Realization.Construction
public import Camus.Network.Baseline.Main
public import Camus.Network.Completeness.Main
public import Camus.Network.Isomorphism.Rename
public import Camus.DP.Correctness

/-!
# At most `n − 1` reticulations

Section 2.4 computes one network for each number of reticulations, and bounds the number `m` of
columns of its table using that a level-1 network on `n` leaves has at most `n − 1` reticulations.
This file proves the bound for networks built on a tree `T` with `n` leaves. The reticulations of a
network are its vertices of indegree 2 (`RootedNetwork.reticulationCount`); their number does not
change under isomorphism. A network built on `T` is isomorphic to the canonical network
`Realization.graph t E` of a cycle-separated family `E`, whose reticulations are the recipients of
its added edges, one for each pair of `E`. By Lemma 2 the pairs of `E` have distinct targets
`lca(u, w)`; each target is an internal vertex of `T`, and a full binary tree with `n` leaves has
`n − 1` internal vertices.

## Main results

* `RootedNetwork.reticulationCount`: the number of vertices of indegree 2.
* `RootedNetwork.Iso.reticulationCount_eq`: isomorphic networks have the same number of
  reticulations.
* `Realization.reticulationCount_eq_card`: the canonical network of a cycle-separated family `E` has
  `|E|` reticulations.
* `EdgeAbove.separated_card_bound`: a cycle-separated family of pairs on a tree with `n` leaves has
  at most `n − 1` members.
* `RootedNetwork.anchored_reticulation_bound`: a network built on a tree with `n` leaves has at most
  `n − 1` reticulations.
-/

@[expose] public section

namespace Camus

namespace PhyloTree

/-- The internal vertices of a tree: the addresses of its forks. -/
def internalNodes : PhyloTree → Finset Address
  | .leaf _ => ∅
  | .fork l r => insert []
      ((l.internalNodes.image (false :: ·)) ∪ (r.internalNodes.image (true :: ·)))

/-- An address is an internal vertex of `t` if and only if the subtree of `t` at it is a fork. -/
theorem mem_internalNodes_iff (t : PhyloTree) (p : Address) :
    p ∈ t.internalNodes ↔ ∃ l r, t.nodeAt p = some (.fork l r) := by
  induction t generalizing p with
  | leaf a => cases p <;> simp [internalNodes,nodeAt]
  | fork l r ihl ihr =>
    cases p with
    | nil => simp [internalNodes,nodeAt]
    | cons b p => cases b <;> simp [internalNodes,nodeAt,ihl,ihr]

/-- A fork has as many internal vertices as its two subtrees together, plus one for its root. -/
theorem internalNodes_card_fork (l r : PhyloTree) :
    (PhyloTree.fork l r).internalNodes.card = l.internalNodes.card + r.internalNodes.card + 1 := by
  classical
  have hdis : Disjoint (l.internalNodes.image (false :: ·)) (r.internalNodes.image (true :: ·)) := by
    rw [Finset.disjoint_left]
    intro p hp hq
    obtain ⟨x,hx,hxp⟩ := Finset.mem_image.mp hp
    obtain ⟨y,hy,hyp⟩ := Finset.mem_image.mp hq
    have hheads := List.cons.inj (hxp.trans hyp.symm)
    exact Bool.false_ne_true hheads.1
  have hn : [] ∉ l.internalNodes.image (false :: ·) ∪ r.internalNodes.image (true :: ·) := by simp
  simp only [internalNodes,Finset.card_insert_of_notMem hn,Finset.card_union_of_disjoint hdis]
  rw [Finset.card_image_of_injective _ (fun p q h => (List.cons.inj h).2),
    Finset.card_image_of_injective _ (fun p q h => (List.cons.inj h).2)]

/-- A full binary tree with `n` leaves has `n − 1` internal vertices; here `n` is the number of
leaves, `t.labels.length`. -/
theorem internalNodes_count (t : PhyloTree) : t.internalNodes.card + 1 = t.labels.length := by
  induction t with
  | leaf a => simp [internalNodes,labels]
  | fork l r ihl ihr =>
    rw [internalNodes_card_fork]
    simp only [labels,List.length_append]
    omega

/-- Every tree has a leaf. -/
theorem labels_nonempty (t : PhyloTree) : 0 < t.labels.length := by
  have h := internalNodes_count t
  omega

end PhyloTree

namespace EdgeAbove

/-- The target `lca(u, w)` of an admissible pair `(u, w)` is an internal vertex of `T`. If it were
a leaf, `u` and `w` would both be that leaf, while an admissible recipient `w` is not an ancestor
of `u`. -/
theorem target_mem_internalNodes {t : PhyloTree} {e : Address × Address}
    (he : Admissible t e) : target e ∈ t.internalNodes := by
  have hnode := t.nodes_prefix_closed he.1 (lca_prefix_left e.1 e.2)
  obtain ⟨s,hs⟩ := (t.mem_nodes_iff (target e)).mp hnode
  rw [t.mem_internalNodes_iff]
  cases s with
  | fork l r => exact ⟨l,r,hs⟩
  | leaf a =>
    have hu := PhyloTree.leaf_no_descendant hs he.1 (lca_prefix_left e.1 e.2)
    have hw := PhyloTree.leaf_no_descendant hs he.2.1 (lca_prefix_right e.1 e.2)
    exact False.elim (he.2.2.2.2 (hw.symm.trans hu ▸ List.prefix_refl _))

/-- Section 2.4 (`m ≤ n − 1`), for families of pairs: a cycle-separated family `E` on a tree with
`n` leaves has at most `n − 1` members. The targets `lca(u, w)` of the pairs of `E` are distinct
(Lemma 2, `EdgeAbove.target_unique`) internal vertices of `T`
(`EdgeAbove.target_mem_internalNodes`), and `T` has `n − 1` internal vertices
(`PhyloTree.internalNodes_count`). -/
theorem separated_card_bound {t : PhyloTree} {E : Finset (Address × Address)}
    (hE : CycleSeparated t E) : E.card ≤ t.labels.length - 1 := by
  classical
  have hinj : Set.InjOn target E := fun e he f hf h => target_unique t E hE he hf h
  have hsub : E.image target ⊆ t.internalNodes := by
    intro p hp
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hp
    exact target_mem_internalNodes (Finset.mem_filter.mp (hE.1 he)).2
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj] at hc
  have hi := t.internalNodes_count
  omega

end EdgeAbove

namespace RootedNetwork

/-- Isomorphic rooted binary level-1 networks have the same number of reticulations: the
isomorphism, extended to a permutation of `ℕ`, preserves indegrees
(`RootedNetwork.renameEdges_count`). -/
theorem Iso.reticulationCount_eq {N P : RootedNetwork}
    (hN : N.RootedBinaryLevelOne) (hP : P.RootedBinaryLevelOne) (i : N.Iso P) :
    N.reticulationCount = P.reticulationCount := by
  classical
  let f : ℕ ≃ ℕ := i.vertices.extendSubtype
  have hvertices (v : ℕ) : v ∈ N.vertices ↔ f v ∈ P.vertices := by
    by_cases hv : v ∈ N.vertices
    · exact ⟨fun _ => Equiv.extendSubtype_mem i.vertices v hv,fun _ => hv⟩
    · exact ⟨fun h => (hv h).elim,fun h => (Equiv.extendSubtype_not_mem i.vertices v hv h).elim⟩
  have hedges (u v : ℕ) : (u,v) ∈ N.edges ↔ (f u,f v) ∈ P.edges := by
    by_cases hu : u ∈ N.vertices
    · by_cases hv : v ∈ N.vertices
      · simpa only [f,Equiv.extendSubtype_apply_of_mem _ u hu,
          Equiv.extendSubtype_apply_of_mem _ v hv] using i.edges ⟨u,hu⟩ ⟨v,hv⟩
      · have hn : (u,v) ∉ N.edges := fun h => hv (hN.2.1 _ h).2
        have hp : (f u,f v) ∉ P.edges := fun h => hv ((hvertices v).mpr (hP.2.1 _ h).2)
        simp [hn,hp]
    · have hn : (u,v) ∉ N.edges := fun h => hu (hN.2.1 _ h).1
      have hp : (f u,f v) ∉ P.edges := fun h => hu ((hvertices u).mpr (hP.2.1 _ h).1)
      simp [hn,hp]
  have himage : N.vertices.image f = P.vertices := by
    ext v
    constructor
    · rintro h
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp h
      exact (hvertices u).mp hu
    · intro hv
      exact Finset.mem_image.mpr ⟨f.symm v,(hvertices _).mpr (by simpa using hv),by simp⟩
  have hedgeImage : renameEdges f N.edges = P.edges := by
    ext e
    obtain ⟨u,hu⟩ := f.surjective e.1
    obtain ⟨v,hv⟩ := f.surjective e.2
    have he : e = (f u,f v) := Prod.ext hu.symm hv.symm
    rw [he,renameEdges_mem]
    exact hedges u v
  have hdegree (v : ℕ) : P.indegree (f v) = N.indegree v := by
    unfold indegree
    rw [←hedgeImage,renameEdges_count]
  unfold reticulationCount
  rw [←himage,Finset.filter_image]
  simp only [hdegree]
  rw [Finset.card_image_of_injective _ f.injective]

end RootedNetwork

namespace Realization

/-- For a family `E` of admissible pairs, the vertices of indegree 2 of the canonical network
`Realization.graph t E` are the recipients `w'` of its added edges, one for each pair of `E`
(`Realization.recipient`). -/
theorem reticulation_vertices (t : PhyloTree) (E : Finset Pair)
    (hE : E ⊆ EdgeAbove.candidates t) :
    (graph t E).vertices.filter (fun v => (graph t E).indegree v = 2) = E.image (recipient t) := by
  classical
  ext v
  simp only [Finset.mem_filter,Finset.mem_image]
  constructor
  · rintro ⟨hv,hin⟩
    rcases Finset.mem_union.mp hv with horiginal | hadded
    · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp horiginal
      by_cases hp0 : p = []
      · subst p
        have hz := graph_root_indegree t E
        change (graph t E).indegree (Address.code []) = 0 at hz
        omega
      · rw [graph_indegree_code t E hE hp hp0] at hin
        omega
    · obtain ⟨e,he,hv⟩ := Finset.mem_biUnion.mp hadded
      rcases Finset.mem_insert.mp hv with rfl | hr
      · rw [(endpoint_degrees t E hE he).1] at hin
        omega
      · exact ⟨e,he,(Finset.mem_singleton.mp hr).symm⟩
  · rintro ⟨e,he,rfl⟩
    exact ⟨Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨e,he,by simp⟩),
      (endpoint_degrees t E hE he).2.2.1⟩

/-- The canonical network `Realization.graph t E` of a cycle-separated family `E` has `|E|`
reticulations, one for each added edge. -/
theorem reticulationCount_eq_card (t : PhyloTree) (E : Finset Pair)
    (hE : EdgeAbove.CycleSeparated t E) : (graph t E).reticulationCount = E.card := by
  classical
  unfold RootedNetwork.reticulationCount
  rw [reticulation_vertices t E hE.1]
  exact Finset.card_image_of_injOn (fun e he f hf h => recipient_injective t (hE.1 he) (hE.1 hf) h)

end Realization

namespace RootedNetwork

/-- Section 2.4: a network built on a tree with `n` leaves has at most `n − 1` reticulations. Let
`t` be well-labelled with `n` taxa and `N` built on `t` (`RootedNetwork.AnchoredExtension`). Then
`N` is isomorphic to the canonical network of a cycle-separated family `E` of pairs
(`SupportSubdivision.canonical_iso`), which has `|E|` reticulations
(`Realization.reticulationCount_eq_card`), and `|E| ≤ n − 1`
(`EdgeAbove.separated_card_bound`). -/
theorem anchored_reticulation_bound {t : PhyloTree} (ht : t.WellLabelled)
    {N : RootedNetwork} (hN : N.AnchoredExtension t) : N.reticulationCount ≤ t.taxa.card - 1 := by
  obtain ⟨S,⟨H⟩⟩ := hN.2
  have hE := H.extracted_separated hN.1
  obtain ⟨i⟩ := H.canonical_iso hN.1
  rw [i.reticulationCount_eq hN.1 (Realization.levelOne t ht H.extracted hE),
    Realization.reticulationCount_eq_card t H.extracted hE]
  have hcard : t.taxa.card = t.labels.length := List.toFinset_card_of_nodup ht
  rw [hcard]
  exact EdgeAbove.separated_card_bound hE

end RootedNetwork
end Camus
