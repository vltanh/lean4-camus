module

public import Camus.GraphCompletenessWires
public import Camus.CycleFrontier

@[expose] public section

namespace Camus
namespace RootedNetwork

theorem outdegree_le_two {N : RootedNetwork} (hN : N.RootedBinaryLevelOne)
    {v : ℕ} (hv : v ∈ N.vertices) : N.outdegree v ≤ 2 := by
  by_cases hr : v = N.root
  · subst v
    rcases hN.2.2.2.2.1 with h | h <;> omega
  · rcases hN.2.2.2.2.2.2.2.2.2.1 v hv hr with h | h | h <;> omega

theorem indegree_mono {N : RootedNetwork} {S : Finset (ℕ × ℕ)}
    (hS : S ⊆ N.edges) (v : ℕ) : ({N with edges := S}).indegree v ≤ N.indegree v := by
  classical
  exact Finset.card_mono (Finset.filter_subset_filter _ hS)

theorem outdegree_mono {N : RootedNetwork} {S : Finset (ℕ × ℕ)}
    (hS : S ⊆ N.edges) (v : ℕ) : ({N with edges := S}).outdegree v ≤ N.outdegree v := by
  classical
  exact Finset.card_mono (Finset.filter_subset_filter _ hS)

theorem deleted_edge_indegree_lt {N : RootedNetwork} {S : Finset (ℕ × ℕ)}
    (hS : S ⊆ N.edges) {e : ℕ × ℕ} (he : e ∈ N.edges \ S) :
    ({N with edges := S}).indegree e.2 < N.indegree e.2 := by
  classical
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_exists_subset_erase.mpr ⟨e,
    Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp he).1,rfl⟩, ?_⟩
  intro f hf
  obtain ⟨hf,hfv⟩ := Finset.mem_filter.mp hf
  refine Finset.mem_erase.mpr ⟨?_, Finset.mem_filter.mpr ⟨hS hf,hfv⟩⟩
  intro hfe
  subst f
  exact (Finset.mem_sdiff.mp he).2 hf

theorem deleted_edge_outdegree_lt {N : RootedNetwork} {S : Finset (ℕ × ℕ)}
    (hS : S ⊆ N.edges) {e : ℕ × ℕ} (he : e ∈ N.edges \ S) :
    ({N with edges := S}).outdegree e.1 < N.outdegree e.1 := by
  classical
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_exists_subset_erase.mpr ⟨e,
    Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp he).1,rfl⟩, ?_⟩
  intro f hf
  obtain ⟨hf,hfv⟩ := Finset.mem_filter.mp hf
  refine Finset.mem_erase.mpr ⟨?_, Finset.mem_filter.mpr ⟨hS hf,hfv⟩⟩
  intro hfe
  subst f
  exact (Finset.mem_sdiff.mp he).2 hf

theorem deleted_edge_target_reticulation {N : RootedNetwork}
    (hN : N.RootedBinaryLevelOne) {S : Finset (ℕ × ℕ)} (hS : N.Switching S)
    {e : ℕ × ℕ} (he : e ∈ N.edges \ S) :
    N.indegree e.2 = 2 ∧ N.outdegree e.2 = 1 := by
  have hends := hN.2.1 e (Finset.mem_sdiff.mp he).1
  have hr : e.2 ≠ N.root := by
    intro hr
    have hlt := deleted_edge_indegree_lt hS.1 he
    rw [hr, hN.2.2.2.1] at hlt
    omega
  have hSin : ({N with edges := S}).indegree e.2 = 1 := hS.2 e.2 hends.2 hr
  have hlt := deleted_edge_indegree_lt hS.1 he
  rw [hSin] at hlt
  rcases hN.2.2.2.2.2.2.2.2.2.1 e.2 hends.2 hr with h | h | h
  · omega
  · omega
  · exact h

end RootedNetwork

namespace SupportSubdivision

variable {t : PhyloTree} {N : RootedNetwork} {S : Finset (ℕ × ℕ)}

theorem original_fork_outdegree_support (H : SupportSubdivision t N S)
    {p : Address} {l r : PhyloTree} (hp : t.nodeAt p = some (.fork l r)) :
    2 ≤ ({N with edges := S}).outdegree (H.original p) := by
  classical
  have hleft := PhyloTree.child_mem_nodes hp false
  have hright := PhyloTree.child_mem_nodes hp true
  have hleft0 : p ++ [false] ≠ [] := by simp
  have hright0 : p ++ [true] ≠ [] := by simp
  obtain ⟨u,hu,hum⟩ := H.wire_head_outgoing_exists hleft hleft0
  obtain ⟨v,hv,hvm⟩ := H.wire_head_outgoing_exists hright hright0
  rw [parent_child] at hu hv
  have huv : u ≠ v := by
    intro huv
    have hpq : p ++ [false] ≠ p ++ [true] := by simp
    exact List.disjoint_left.mp (H.tail_wires_disjoint
      hleft hleft0 hright hright0 hpq) hum (huv ▸ hvm)
  have hsub : {(H.original p,u),(H.original p,v)} ⊆
      S.filter (fun e => e.1 = H.original p) := by
    intro e he
    rcases Finset.mem_insert.mp he with he | he
    · subst e
      exact Finset.mem_filter.mpr ⟨hu,rfl⟩
    · have heq := Finset.mem_singleton.mp he
      subst e
      exact Finset.mem_filter.mpr ⟨hv,rfl⟩
  have hc := Finset.card_mono hsub
  simpa [huv, RootedNetwork.outdegree] using hc

theorem original_leaf_outdegree (H : SupportSubdivision t N S)
    (hN : N.RootedBinaryLevelOne) {p : Address} {a : ℕ}
    (hp : t.nodeAt p = some (.leaf a)) : N.outdegree (H.original p) = 0 := by
  have hpn : p ∈ t.nodes := (t.mem_nodes_iff p).mpr ⟨_,hp⟩
  have hat : a ∈ t.taxa := List.mem_toFinset.mpr (PhyloTree.leaf_label_mem hp)
  have haN : a ∈ N.taxa := H.taxa_preserved.symm ▸ hat
  rw [H.leaves_preserved p hpn a hp]
  exact (hN.2.2.2.2.2.2.2.1 a haN).2.2

theorem deleted_source_not_original (H : SupportSubdivision t N S)
    (hN : N.RootedBinaryLevelOne) {e : ℕ × ℕ} (he : e ∈ N.edges \ S) :
    e.1 ∉ t.nodes.image H.original := by
  classical
  intro ho
  obtain ⟨p,hp,heq⟩ := Finset.mem_image.mp ho
  obtain ⟨s,hpAt⟩ := (t.mem_nodes_iff p).mp hp
  have hlt := RootedNetwork.deleted_edge_outdegree_lt H.switching.1 he
  rw [← heq] at hlt
  cases s with
  | leaf a => rw [H.original_leaf_outdegree hN hpAt] at hlt; omega
  | fork l r =>
    have hlo := H.original_fork_outdegree_support hpAt
    have hup := RootedNetwork.outdegree_le_two hN (H.original_mem_vertices hp)
    omega

theorem deleted_target_not_original (H : SupportSubdivision t N S)
    (hN : N.RootedBinaryLevelOne) {e : ℕ × ℕ} (he : e ∈ N.edges \ S) :
    e.2 ∉ t.nodes.image H.original := by
  classical
  intro ho
  obtain ⟨p,hp,heq⟩ := Finset.mem_image.mp ho
  obtain ⟨s,hpAt⟩ := (t.mem_nodes_iff p).mp hp
  have hout := (RootedNetwork.deleted_edge_target_reticulation hN H.switching he).2
  rw [← heq] at hout
  cases s with
  | leaf a => rw [H.original_leaf_outdegree hN hpAt] at hout; omega
  | fork l r =>
    have hlo := H.original_fork_outdegree_support hpAt
    have hmono := RootedNetwork.outdegree_mono H.switching.1 (H.original p)
    omega

theorem deleted_source_anchor_spec (H : SupportSubdivision t N S)
    (hN : N.RootedBinaryLevelOne) {e : ℕ × ℕ} (he : e ∈ N.edges \ S) :
    H.anchor e.1 ∈ t.nodes ∧ H.anchor e.1 ≠ [] ∧
      e.1 ∈ wireInterior (H.wire (H.anchor e.1)) := by
  have hv := (hN.2.1 e (Finset.mem_sdiff.mp he).1).1
  rcases H.vertex_cases hv with ho | hi
  · exact False.elim (H.deleted_source_not_original hN he (Finset.mem_image.mpr ho))
  · exact hi

theorem deleted_target_anchor_spec (H : SupportSubdivision t N S)
    (hN : N.RootedBinaryLevelOne) {e : ℕ × ℕ} (he : e ∈ N.edges \ S) :
    H.anchor e.2 ∈ t.nodes ∧ H.anchor e.2 ≠ [] ∧
      e.2 ∈ wireInterior (H.wire (H.anchor e.2)) := by
  have hv := (hN.2.1 e (Finset.mem_sdiff.mp he).1).2
  rcases H.vertex_cases hv with ho | hi
  · exact False.elim (H.deleted_target_not_original hN he (Finset.mem_image.mpr ho))
  · exact hi

theorem deleted_source_tree_vertex (H : SupportSubdivision t N S)
    (hN : N.RootedBinaryLevelOne) {e : ℕ × ℕ} (he : e ∈ N.edges \ S) :
    N.indegree e.1 = 1 ∧ N.outdegree e.1 = 2 := by
  have ha := H.deleted_source_anchor_spec hN he
  have hSin := H.interior_outdegree_support ha.1 ha.2.1 ha.2.2
  have hlt := RootedNetwork.deleted_edge_outdegree_lt H.switching.1 he
  rw [hSin] at hlt
  have hv := (hN.2.1 e (Finset.mem_sdiff.mp he).1).1
  have hr : e.1 ≠ N.root := by
    intro hr
    exact H.deleted_source_not_original hN he
      (Finset.mem_image.mpr ⟨[],t.root_mem_nodes,H.root_preserved.trans hr.symm⟩)
  rcases hN.2.2.2.2.2.2.2.2.2.1 e.1 hv hr with h | h | h
  · omega
  · exact h
  · omega

/-- Unary support vertices have no role other than an endpoint of one deleted
edge: the binary network degree laws exclude any remaining unary vertex. -/
theorem interior_is_deleted_endpoint (H : SupportSubdivision t N S)
    (hN : N.RootedBinaryLevelOne) {p : Address}
    (hp : p ∈ t.nodes) (hp0 : p ≠ []) {v : ℕ}
    (hv : v ∈ wireInterior (H.wire p)) :
    ∃ e ∈ N.edges \ S, e.1 = v ∨ e.2 = v := by
  classical
  have hvN := H.interior_mem_vertices hp hp0 hv
  have hr : v ≠ N.root := by
    intro hr
    exact H.interior_not_original hp hp0 hv
      (Finset.mem_image.mpr ⟨[],t.root_mem_nodes,H.root_preserved.trans hr.symm⟩)
  have houtS := H.interior_outdegree_support hp hp0 hv
  have hinS : ({N with edges := S}).indegree v = 1 := H.switching.2 v hvN hr
  have houtMono := RootedNetwork.outdegree_mono H.switching.1 v
  rcases hN.2.2.2.2.2.2.2.2.2.1 v hvN hr with hleaf | htree | hretic
  · omega
  · have hc : (S.filter (fun e => e.1 = v)).card <
        (N.edges.filter (fun e => e.1 = v)).card := by
      change ({N with edges := S}).outdegree v < N.outdegree v
      omega
    obtain ⟨e,heN,heS⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
    obtain ⟨heN,hev⟩ := Finset.mem_filter.mp heN
    refine ⟨e,Finset.mem_sdiff.mpr ⟨heN, ?_⟩, Or.inl hev⟩
    intro he
    exact heS (Finset.mem_filter.mpr ⟨he,hev⟩)
  · have hc : (S.filter (fun e => e.2 = v)).card <
        (N.edges.filter (fun e => e.2 = v)).card := by
      change ({N with edges := S}).indegree v < N.indegree v
      omega
    obtain ⟨e,heN,heS⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
    obtain ⟨heN,hev⟩ := Finset.mem_filter.mp heN
    refine ⟨e,Finset.mem_sdiff.mpr ⟨heN, ?_⟩, Or.inr hev⟩
    intro he
    exact heS (Finset.mem_filter.mpr ⟨he,hev⟩)

end SupportSubdivision
end Camus
