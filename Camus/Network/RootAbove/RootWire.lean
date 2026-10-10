module

public import Camus.Network.RootAbove.Subdivision
public import Camus.Network.Realization.Degrees

/-!
# The root of a network built on `T` lies at most one edge above the root of `T`

Let `N` be a rooted binary level-1 network built on `T` in the sense of Definition 1, through a
displayed subdivision `H`. If the root of `N` is not the root of `T`, then it is the parent of the
root of `T`, and its other child is a reticulation (`DisplayedSubdivision.root_above`): the root
wire has at most two vertices (`DisplayedSubdivision.rootWire_length_le`). A vertex of the root
wire other than its last one has one child in the switching, the next vertex of the root wire
(`DisplayedSubdivision.switching_edge_of_rootWire`). So the second vertex of a longer root wire is
the end of a non-tree edge, and the root of `N`, of outdegree 2, is the tail of a non-tree edge
whose cycle passes through that second vertex. Two cycles of non-tree edges sharing a vertex
contradict level-1.

## Main results

* `DisplayedSubdivision.rootWire_length_le`: the root wire has at most two vertices.
* `DisplayedSubdivision.root_above`: if the root of `N` is not the root of `T`, the root of `N`
  has the root of `T` and a reticulation as children.
-/

@[expose] public section

namespace Camus

namespace DisplayedSubdivision

variable {t : PhyloTree} {N : RootedNetwork} {S : Finset (ℕ × ℕ)}

/-- An edge of the switching that leaves a vertex of the root wire other than its last one is an
edge of the root wire: such a vertex is neither an image of a vertex of `T` nor inside a wire. -/
theorem switching_edge_of_rootWire (H : DisplayedSubdivision t N S) {v y : ℕ}
    (hv : v ∈ H.rootWire.dropLast) (hvy : (v, y) ∈ S) : (v, y) ∈ wireEdges H.rootWire := by
  rw [Finset.ext_iff.mp H.edges_covered, Finset.mem_union, Finset.mem_biUnion] at hvy
  rcases hvy with ⟨p, hp, he⟩ | he
  · exfalso
    obtain ⟨hp0, hp⟩ := Finset.mem_erase.mp hp
    obtain ⟨hlen, _, hhead, _, _⟩ := H.wire_laws p hp hp0
    have hv' : v ∈ (H.wire p).dropLast := Realization.edge_first_mem_dropLast he
    -- `v` would be the first vertex of the wire, an image, or an interior vertex
    obtain ⟨a, b, rest, hL⟩ : ∃ a b rest, H.wire p = a :: b :: rest := by
      match h : H.wire p, hlen with
      | a :: b :: rest, _ => exact ⟨a, b, rest, rfl⟩
    rw [hL] at hhead hv'
    simp only [List.head?_cons, Option.some.injEq] at hhead
    rw [List.dropLast_cons_of_ne_nil (List.cons_ne_nil _ _), List.mem_cons] at hv'
    rcases hv' with hva | hin
    · have himg : v ∈ t.nodes.image H.original := by
        rw [hva, hhead]
        exact Finset.mem_image_of_mem _ (t.nodes_prefix_closed hp (parent_prefix p))
      exact Finset.disjoint_left.mp H.rootWire_laws.2.2.2 (List.mem_toFinset.mpr hv) himg
    · have hint : v ∈ wireInterior (H.wire p) := by
        rw [hL]
        exact List.mem_toFinset.mpr hin
      exact Finset.disjoint_left.mp (H.rootWire_disjoint p hp hp0) (List.mem_toFinset.mpr hv)
        hint
  · exact he

/-- A vertex of outdegree 2 has an edge out of it other than a given one. -/
theorem exists_other_out {N : RootedNetwork} {v : ℕ} (h : N.outdegree v = 2) (e : ℕ × ℕ) :
    ∃ d ∈ N.edges, d.1 = v ∧ d ≠ e := by
  obtain ⟨d, hd, hde⟩ := Finset.exists_mem_ne (show 1 < N.outdegree v by omega) e
  exact ⟨d, (Finset.mem_filter.mp hd).1, (Finset.mem_filter.mp hd).2, hde⟩

/-- In a rooted binary level-1 network built on `T` in the sense of Definition 1, the root wire
has at most two vertices: the root of `N` is the root of `T` or its parent. Otherwise the second
vertex `x₁` of the root wire has one child in the switching, so it is the end of a non-tree edge,
whose cycle contains `x₁`; and the root of `N` has one child `x₁` in the switching and
outdegree 2, so it is the tail of a non-tree edge `(N.root, y₀)`, whose cycle contains the root
of `N` and its two neighbours `x₁` and `y₀`. The cycles of the two non-tree edges share `x₁`. -/
theorem rootWire_length_le (H : DisplayedSubdivision t N S) (hN : N.RootedBinaryLevelOne) :
    H.rootWire.length ≤ 2 := by
  classical
  by_contra hlen
  have hS := H.switching
  obtain ⟨hnd, hhead, _, _⟩ := H.rootWire_laws
  -- the root wire is `N.root :: x₁ :: x₂ :: rest`
  obtain ⟨x₀, x₁, x₂, rest, hL⟩ : ∃ x₀ x₁ x₂ rest, H.rootWire = x₀ :: x₁ :: x₂ :: rest := by
    match h : H.rootWire, hlen with
    | [], hlen => simp at hlen
    | [_], hlen => simp at hlen
    | [_, _], hlen => simp at hlen
    | x₀ :: x₁ :: x₂ :: rest, _ => exact ⟨x₀, x₁, x₂, rest, rfl⟩
  rw [hL] at hnd hhead
  simp only [List.head?_cons, Option.some.injEq] at hhead
  subst hhead
  have hx₀ : N.root ∉ x₁ :: x₂ :: rest := (List.nodup_cons.mp hnd).1
  have hx₁ : x₁ ∉ x₂ :: rest := (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1
  have hdrop0 : N.root ∈ H.rootWire.dropLast := by
    rw [hL]
    simp [List.dropLast_cons_of_ne_nil]
  have hdrop1 : x₁ ∈ H.rootWire.dropLast := by
    rw [hL]
    simp [List.dropLast_cons_of_ne_nil]
  -- the edges of the root wire out of `N.root` and `x₁`
  have hedges : wireEdges H.rootWire =
      insert (N.root, x₁) (insert (x₁, x₂) (wireEdges (x₂ :: rest))) := by
    rw [hL, Realization.wireEdges_cons_cons, Realization.wireEdges_cons_cons]
  have hout0 : ∀ y, (N.root, y) ∈ wireEdges H.rootWire → y = x₁ := by
    intro y he
    rw [hedges, Finset.mem_insert, Finset.mem_insert] at he
    rcases he with h | h | h
    · exact (Prod.ext_iff.mp h).2
    · have h' : N.root = x₁ := (Prod.ext_iff.mp h).1
      exact (hx₀ (by rw [h']; exact List.mem_cons_self)).elim
    · exact absurd (List.mem_cons_of_mem _ (Realization.edge_first_mem h)) hx₀
  have hout1 : ∀ y, (x₁, y) ∈ wireEdges H.rootWire → y = x₂ := by
    intro y he
    rw [hedges, Finset.mem_insert, Finset.mem_insert] at he
    rcases he with h | h | h
    · have h' : x₁ = N.root := (Prod.ext_iff.mp h).1
      exact (hx₀ (by rw [← h']; exact List.mem_cons_self)).elim
    · exact (Prod.ext_iff.mp h).2
    · exact absurd (Realization.edge_first_mem h) hx₁
  have hrootS : (N.root, x₁) ∈ S := (Finset.ext_iff.mp H.edges_covered _).mpr
    (Finset.mem_union_right _ (by rw [hedges]; exact Finset.mem_insert_self _ _))
  have hx₁S : (x₁, x₂) ∈ S := (Finset.ext_iff.mp H.edges_covered _).mpr
    (Finset.mem_union_right _
      (by rw [hedges]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
  -- the root of `N` has outdegree 2: a second edge `d₀` out of it, outside `S`
  have hrootOut : N.outdegree N.root = 2 := by
    rcases hN.2.2.2.2.1 with h | h
    · have hpos : 0 < N.outdegree N.root :=
        Finset.card_pos.mpr ⟨_, Finset.mem_filter.mpr ⟨hS.1 hrootS, rfl⟩⟩
      omega
    · exact h
  obtain ⟨⟨a₀, y₀⟩, hd₀N, hd₀1, hd₀ne⟩ := exists_other_out hrootOut (N.root, x₁)
  simp only at hd₀1
  subst hd₀1
  set d₀ : ℕ × ℕ := (N.root, y₀) with hd₀
  have hd₀1 : d₀.1 = N.root := rfl
  have hd₀S : d₀ ∉ S := by
    intro h
    have hy := hout0 d₀.2 (H.switching_edge_of_rootWire hdrop0 h)
    exact hd₀ne (Prod.ext hd₀1 hy)
  have hd₀del : d₀ ∈ N.edges \ S := Finset.mem_sdiff.mpr ⟨hd₀N, hd₀S⟩
  have hx₁d : x₁ ≠ d₀.2 := fun h => hd₀ne (Prod.ext hd₀1 h.symm)
  -- the neighbours of the root of `N` are `x₁` and the head of `d₀`
  have hnbr : ∀ w, N.underlying.Adj N.root w → w = x₁ ∨ w = d₀.2 := by
    intro w ⟨_, hw⟩
    rcases hw with hw | hw
    · by_contra hne
      simp only [not_or] at hne
      have hsub : ({(N.root, x₁), d₀, (N.root, w)} : Finset (ℕ × ℕ)) ⊆
          N.edges.filter (fun e => e.1 = N.root) := by
        intro e he
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl | rfl
        · exact Finset.mem_filter.mpr ⟨hS.1 hrootS, rfl⟩
        · exact Finset.mem_filter.mpr ⟨hd₀N, hd₀1⟩
        · exact Finset.mem_filter.mpr ⟨hw, rfl⟩
      have hcard := Finset.card_le_card hsub
      have h3 : ({(N.root, x₁), d₀, (N.root, w)} : Finset (ℕ × ℕ)).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
        · intro h
          rw [Finset.mem_singleton] at h
          exact hne.2 (by rw [h])
        · intro h
          simp only [Finset.mem_insert, Finset.mem_singleton] at h
          rcases h with h | h
          · exact hd₀ne h.symm
          · exact hne.1 (Prod.ext_iff.mp h).2.symm
      rw [h3] at hcard
      change 3 ≤ N.outdegree N.root at hcard
      omega
    · have hpos : 0 < N.indegree N.root :=
        Finset.card_pos.mpr ⟨_, Finset.mem_filter.mpr ⟨hw, rfl⟩⟩
      rw [hN.2.2.2.1] at hpos
      omega
  -- so the cycle of `d₀` passes through `x₁`
  have hc := RootedNetwork.fundamentalCycle_isCycle hN hS hd₀del
  have hx₁c : x₁ ∈ (RootedNetwork.fundamentalCycle hN hS hd₀del).support := by
    have hroot : N.root ∈ (RootedNetwork.fundamentalCycle hN hS hd₀del).support :=
      RootedNetwork.fundamentalCycle_source_mem hN hS hd₀del
    have h2 := hc.ncard_neighborSet_toSubgraph_eq_two hroot
    have hs : (RootedNetwork.fundamentalCycle hN hS hd₀del).toSubgraph.neighborSet N.root ⊆
        {x₁, d₀.2} := fun w hw => hnbr w
          ((RootedNetwork.fundamentalCycle hN hS hd₀del).toSubgraph.adj_sub hw)
    have heq := Set.eq_of_subset_of_ncard_le hs (by rw [Set.ncard_pair hx₁d, h2])
      (Set.toFinite _)
    have hadj : x₁ ∈ (RootedNetwork.fundamentalCycle hN hS hd₀del).toSubgraph.neighborSet
        N.root := heq ▸ Set.mem_insert x₁ {d₀.2}
    exact (RootedNetwork.fundamentalCycle hN hS hd₀del).mem_verts_toSubgraph.mp
      (SimpleGraph.Subgraph.Adj.snd_mem hadj)
  -- `x₁` is a tree vertex or a reticulation, an end of a non-tree edge `d₁`
  have hx₁N : x₁ ∈ N.vertices := (hN.2.1 _ (hS.1 hrootS)).2
  have hx₁root : x₁ ≠ N.root := fun h => hx₀ (h ▸ List.mem_cons_self)
  obtain ⟨d₁, hd₁, hx₁d₁, hne⟩ : ∃ (d₁ : ℕ × ℕ) (hd₁ : d₁ ∈ N.edges \ S),
      x₁ ∈ (RootedNetwork.fundamentalCycle hN hS hd₁).support ∧ d₁ ≠ d₀ := by
    have hx₁out : 0 < N.outdegree x₁ :=
      Finset.card_pos.mpr ⟨_, Finset.mem_filter.mpr ⟨hS.1 hx₁S, rfl⟩⟩
    rcases hN.2.2.2.2.2.2.2.2.2.1 x₁ hx₁N hx₁root with h | h | h
    · omega
    -- a tree vertex: its second edge out is outside `S`
    · obtain ⟨⟨a₁, y₁⟩, hd₁N, hd₁1, hd₁ne⟩ := exists_other_out h.2 (x₁, x₂)
      simp only at hd₁1
      subst hd₁1
      have hd₁S : (a₁, y₁) ∉ S := by
        intro hS'
        have hy := hout1 y₁ (H.switching_edge_of_rootWire hdrop1 hS')
        exact hd₁ne (Prod.ext rfl hy)
      have hdel : (a₁, y₁) ∈ N.edges \ S := Finset.mem_sdiff.mpr ⟨hd₁N, hd₁S⟩
      refine ⟨(a₁, y₁), hdel, RootedNetwork.fundamentalCycle_source_mem hN hS hdel, ?_⟩
      intro h'
      exact hx₁root (congrArg Prod.fst h')
    -- a reticulation: one of its two edges in is outside `S`
    · obtain ⟨⟨u₁, b₁⟩, hdel, hd₁2⟩ :=
        RootedNetwork.deleted_incoming_of_reticulation hN hS x₁ h.1
      simp only at hd₁2
      subst hd₁2
      refine ⟨(u₁, b₁), hdel, RootedNetwork.fundamentalCycle_target_mem hN hS hdel, ?_⟩
      intro h'
      exact hx₁d (congrArg Prod.snd h')
  -- the cycles of `d₀` and `d₁` share `x₁`
  exact Finset.disjoint_left.mp
    (RootedNetwork.fundamentalCycles_disjoint hN hS hd₁ hd₀del hne)
    (List.mem_toFinset.mpr hx₁d₁) (List.mem_toFinset.mpr hx₁c)

/-- In a rooted binary level-1 network built on `T` in the sense of Definition 1 whose root is not
the root of `T`, the root of `N` has two children: the root of `T`, through an edge of the
switching, and the head of an edge outside the switching, which is a reticulation. -/
theorem root_above (H : DisplayedSubdivision t N S) (hN : N.RootedBinaryLevelOne)
    (hne : H.original [] ≠ N.root) :
    H.rootWire = [N.root, H.original []] ∧ (N.root, H.original []) ∈ S ∧
      ∃ w, (N.root, w) ∈ N.edges \ S ∧ N.indegree w = 2 := by
  classical
  obtain ⟨_, hhead, hlast, _⟩ := H.rootWire_laws
  have hlen := H.rootWire_length_le hN
  -- the root wire is `[N.root, original []]`
  have hwire : H.rootWire = [N.root, H.original []] := by
    match hL : H.rootWire, hlen, hhead, hlast with
    | [], _, hhead, _ => simp at hhead
    | [a], _, hhead, hlast =>
      simp only [List.head?_cons, List.getLast?_singleton, Option.some.injEq] at hhead hlast
      exact absurd (hlast.symm.trans hhead) hne
    | [a, b], _, hhead, hlast =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at hlast
      rw [hhead, hlast]
    | _ :: _ :: _ :: _, hlen, _, _ => simp at hlen
  have hedge : (N.root, H.original []) ∈ S := (Finset.ext_iff.mp H.edges_covered _).mpr
    (Finset.mem_union_right _ (by rw [hwire]; simp [wireEdges]))
  refine ⟨hwire, hedge, ?_⟩
  -- the root of `N` has outdegree 2, and its second edge out is outside `S`
  have hS := H.switching
  have hrootOut : N.outdegree N.root = 2 := by
    rcases hN.2.2.2.2.1 with h | h
    · have hpos : 0 < N.outdegree N.root :=
        Finset.card_pos.mpr ⟨_, Finset.mem_filter.mpr ⟨hS.1 hedge, rfl⟩⟩
      omega
    · exact h
  obtain ⟨d, hdN, hd1, hdne⟩ := exists_other_out hrootOut (N.root, H.original [])
  have hdS : d ∉ S := by
    intro h
    have hroot : N.root ∈ H.rootWire.dropLast := by
      rw [hwire]
      simp
    have he := H.switching_edge_of_rootWire hroot (y := d.2) (by rw [← hd1]; exact h)
    rw [hwire] at he
    simp only [wireEdges, List.tail_cons, List.zip_cons_cons, List.zip_nil_right,
      List.toFinset_cons, List.toFinset_nil, insert_empty_eq, Finset.mem_singleton,
      Prod.mk.injEq, true_and] at he
    exact hdne (Prod.ext hd1 he)
  have hdel : d ∈ N.edges \ S := Finset.mem_sdiff.mpr ⟨hdN, hdS⟩
  refine ⟨d.2, ?_, (RootedNetwork.deleted_edge_target_reticulation hN hS hdel).1⟩
  rw [← hd1]
  exact hdel

end DisplayedSubdivision

end Camus
