module

public import Camus.Network.Completeness.Admissible

@[expose] public section

namespace Camus

/-- A path through a vertex outside a connected region remains connected to
that vertex from at least one endpoint after cuts confined to the region. -/
theorem path_outside_region_reachable {G : SimpleGraph ℕ} (hG : G.IsAcyclic)
    (C : Set ℕ)
    (hC : ∀ x ∈ C, ∀ y ∈ C, ∃ w : G.Walk x y, w.IsPath ∧ ∀ z ∈ w.support, z ∈ C)
    (B : Set (Sym2 ℕ)) (hB : ∀ e ∈ B, ∀ x ∈ e, x ∈ C)
    {a b v : ℕ} (p : G.Walk a b) (hp : p.IsPath) (hv : v ∈ p.support)
    (hvC : v ∉ C) :
    (G.deleteEdges B).Reachable a v ∨ (G.deleteEdges B).Reachable v b := by
  classical
  obtain ⟨l,r,hl,hr,hpEq⟩ := hp.mem_support_iff_exists_append.mp hv
  have hpLR : (l.append r).IsPath := hpEq ▸ hp
  by_cases hleft : ∀ e ∈ l.edges, e ∉ B
  · exact Or.inl ((l.toDeleteEdges B hleft).reachable)
  by_cases hright : ∀ e ∈ r.edges, e ∉ B
  · exact Or.inr ((r.toDeleteEdges B hright).reachable)
  push Not at hleft hright
  obtain ⟨e,he,hBe⟩ := hleft
  obtain ⟨f,hf,hBf⟩ := hright
  induction e using Sym2.inductionOn with
  | _ x x' =>
    induction f using Sym2.inductionOn with
    | _ y y' =>
      have hx : x ∈ l.support := l.fst_mem_support_of_mem_edges he
      have hy : y ∈ r.support := r.fst_mem_support_of_mem_edges hf
      have hxC : x ∈ C := hB _ hBe _ (Sym2.mem_mk_left _ _)
      have hyC : y ∈ C := hB _ hBf _ (Sym2.mem_mk_left _ _)
      obtain ⟨w,hw,hwC⟩ := hC x hxC y hyC
      let q := (l.dropUntil x hx).append (r.takeUntil y hy)
      have hq : q.IsPath := by
        have h := hpLR
        rw [← l.take_spec hx, ← SimpleGraph.Walk.append_assoc] at h
        have h := h.of_append_right
        rw [← r.take_spec hy, SimpleGraph.Walk.append_assoc] at h
        exact h.of_append_left
      have heq : q = w := Subtype.mk.inj
        (hG.subsingleton_path x y |>.elim ⟨q,hq⟩ ⟨w,hw⟩)
      have hvq : v ∈ q.support :=
        (SimpleGraph.Walk.mem_support_append_iff _ _).mpr
          (Or.inl (l.dropUntil x hx).end_mem_support)
      exact False.elim (hvC (hwC v (heq ▸ hvq)))

/-- A walk from a region to its complement has a boundary edge. -/
theorem walk_boundary_edge {G : SimpleGraph ℕ} (C : Set ℕ) {a b : ℕ}
    (p : G.Walk a b) (ha : a ∈ C) (hb : b ∉ C) :
    ∃ u v, s(u,v) ∈ p.edges ∧ u ∈ C ∧ v ∉ C := by
  induction p with
  | nil => exact False.elim (hb ha)
  | @cons a v b hav p ih =>
    by_cases hv : v ∈ C
    · obtain ⟨x,y,hxy,hx,hy⟩ := ih hv hb
      exact ⟨x,y,List.mem_cons_of_mem _ hxy,hx,hy⟩
    · exact ⟨a,v,List.mem_cons_self,ha,hv⟩

/-- Every edge on the unique tree path is necessary for endpoint connectivity. -/
theorem acyclic_path_cut_not_reachable {G : SimpleGraph ℕ} (hG : G.IsAcyclic)
    {a b : ℕ} (p : G.Walk a b) (hp : p.IsPath) {e : Sym2 ℕ} (he : e ∈ p.edges) :
    ¬(G.deleteEdges {e}).Reachable a b := by
  classical
  rintro ⟨w⟩
  let z := w.toPath.val.mapLe (SimpleGraph.deleteEdges_le {e})
  have hz : z.IsPath := w.toPath.isPath.mapLe _
  have heq : p = z := Subtype.mk.inj (hG.subsingleton_path a b |>.elim ⟨p,hp⟩ ⟨z,hz⟩)
  have hez : e ∈ z.edges := heq ▸ he
  have hew : e ∈ w.toPath.val.edges := by
    simpa only [z,SimpleGraph.Walk.edges_mapLe_eq_edges] using hez
  have hcut := w.toPath.val.edges_subset_edgeSet hew
  rw [SimpleGraph.edgeSet_deleteEdges] at hcut
  exact hcut.2 (Set.mem_singleton e)

/-- Two disjoint pair paths in a tree are separated by one tree edge. -/
theorem disjoint_paths_separating_edge {G : SimpleGraph ℕ} (hG : G.IsAcyclic)
    {a b c d : ℕ} (p : G.Walk a b) (r : G.Walk c d)
    (hd : p.support.Disjoint r.support)
    (w : G.Walk a c) (hw : w.IsPath) :
    ∃ e ∈ G.edgeSet,
      (G.deleteEdges {e}).Reachable a b ∧
      (G.deleteEdges {e}).Reachable c d ∧
      ¬(G.deleteEdges {e}).Reachable a c := by
  classical
  have hc : c ∉ {x | x ∈ p.support} :=
    fun hc => hd hc r.start_mem_support
  obtain ⟨u,v,he,hu,hv⟩ := walk_boundary_edge {x | x ∈ p.support} w p.start_mem_support hc
  have hp : s(u,v) ∉ p.edges := fun h => hv (p.snd_mem_support_of_mem_edges h)
  have hr : s(u,v) ∉ r.edges :=
    fun h => hd hu (r.fst_mem_support_of_mem_edges h)
  exact ⟨s(u,v), w.edges_subset_edgeSet he,
    (p.toDeleteEdge _ hp).reachable, (r.toDeleteEdge _ hr).reachable,
    acyclic_path_cut_not_reachable hG w hw he⟩

end Camus
