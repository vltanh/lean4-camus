module

public import Camus.Network.TreeBased.Main

/-!
# When the tree of a switching keeps the root

Every switching `S` of a rooted binary level-1 network `N` is a subdivision of a tree `t`, below a
directed path from the root of `N` to the root of `t` (`RootedNetwork.exists_displayedSubdivision`).
The root of `t` is the root of `N`, so that `N` is built on `t` with the root kept
(`RootedNetwork.AnchoredExtension`), the class over which the dynamic program of Section 2.2
optimizes, exactly when `S` keeps the edges out of the root of `N`
(`DisplayedSubdivision.original_nil_eq_root_iff`, `RootedNetwork.exists_support_iff`). Some
switching keeps them (`RootedNetwork.exists_switching_rootEdges`), so every rooted binary level-1
network is built with the root kept on a well-labelled tree on its taxa
(`RootedNetwork.exists_anchoredExtension`), and is isomorphic to the network obtained from that
tree by adding edges (Definition 3, `RootedNetwork.exists_canonical`): Section 2.1's "N can be
constructed by taking one of the trees t∈𝒯 and adding reticulations (edges) to t". So it has at
most `n − 1` reticulations, Section 2.4's bound (`RootedNetwork.reticulationCount_le`).

Section 3.2 says that "any tree t∈Q(N_r) can be used as the basis for N (i.e. N can be obtained by
adding reticulate edges to t)". This can fail when a child of the root of `N` is a reticulation
(the report's E8), and holds when the root of `N` has an outgroup leaf as a child, as in the
pipelines of Section 3: then every switching keeps the edges out of the root
(`RootedNetwork.rootEdges_mem_of_outgroup`), and `N` is built with the root kept on the tree of
every switching (`RootedNetwork.exists_support_of_outgroup`,
`RootedNetwork.BuiltOn.anchored_of_outgroup`), hence obtained from it by adding edges
(`RootedNetwork.BuiltOn.exists_canonical_of_outgroup`).

## Main results

* `DisplayedSubdivision.original_nil_eq_root_iff`: the root of `T` is the root of `N` iff the
  switching keeps the edges out of the root of `N`.
* `RootedNetwork.exists_support_iff`: `N` is built with the root kept on the tree of the switching
  `S` iff `S` keeps the edges out of the root of `N`.
* `RootedNetwork.exists_anchoredExtension`, `RootedNetwork.exists_canonical`: every rooted binary
  level-1 network is built with the root kept on a well-labelled tree, and is isomorphic to a
  network obtained from it by adding edges.
* `RootedNetwork.reticulationCount_le`, `RootedNetwork.reticulationCount_lt`: Section 2.4's bound
  of `n − 1` reticulations, for every rooted binary level-1 network.
* `RootedNetwork.exists_support_of_outgroup`, `RootedNetwork.BuiltOn.anchored_of_outgroup`,
  `RootedNetwork.BuiltOn.exists_canonical_of_outgroup`: with an outgroup leaf as a child of the
  root, every tree of `N` keeps the root, and `N` is obtained from it by adding edges.
-/

@[expose] public section

namespace Camus

/-- A list without repetition whose first and last elements are `x` is `[x]`. -/
theorem eq_singleton_of_head?_getLast? {L : List ℕ} (hL : L.Nodup) {x : ℕ}
    (hh : L.head? = some x) (hl : L.getLast? = some x) : L = [x] := by
  match L, hL, hh, hl with
  | [a], _, hh, _ =>
    simp only [List.head?_cons, Option.some.injEq] at hh
    rw [hh]
  | a :: b :: rest, hL, hh, hl =>
    simp only [List.head?_cons, Option.some.injEq] at hh
    rw [List.getLast?_cons_cons] at hl
    exact absurd (hh ▸ List.mem_of_getLast? hl) (List.nodup_cons.mp hL).1

namespace SupportSubdivision

variable {t : PhyloTree} {N : RootedNetwork} {S : Finset (ℕ × ℕ)}

/-- The wire above a non-root vertex `p` of `T` leaves the image of `parent p` through an edge of
`S` into the image of `p` or into an interior vertex of the wire. -/
theorem exists_first_edge (H : SupportSubdivision t N S) {p : Address} (hp : p ∈ t.nodes)
    (hp0 : p ≠ []) :
    ∃ x, (H.original (parent p), x) ∈ S ∧
      (x = H.original p ∨ x ∈ wireInterior (H.wire p)) := by
  obtain ⟨hlen, _, hhead, hlast, _⟩ := H.wire_laws p hp hp0
  obtain ⟨a, x, rest, hL⟩ : ∃ a x rest, H.wire p = a :: x :: rest := by
    match h : H.wire p, hlen with
    | a :: x :: rest, _ => exact ⟨a, x, rest, rfl⟩
  rw [hL, List.head?_cons, Option.some.injEq] at hhead
  have hedge : (H.original (parent p), x) ∈ S := by
    refine (Finset.ext_iff.mp H.edges_covered _).mpr
      (Finset.mem_biUnion.mpr ⟨p, Finset.mem_erase.mpr ⟨hp0, hp⟩, ?_⟩)
    rw [hL, Realization.wireEdges_cons_cons, hhead]
    exact Finset.mem_insert_self _ _
  refine ⟨x, hedge, ?_⟩
  cases rest with
  | nil =>
    rw [hL, List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at hlast
    exact Or.inl hlast
  | cons y rest =>
    right
    rw [hL]
    exact List.mem_toFinset.mpr (by simp)

/-- A network built on `T` with the root of `T` at its root keeps the edges out of its root in
the switching: a leaf `T` would make the root of `N` a leaf, and otherwise the wires above the two
children of the root of `T` leave the root of `N` through two distinct edges of `S`, while the
root of `N` has outdegree at most 2. -/
theorem rootEdges_mem (H : SupportSubdivision t N S) (hN : N.RootedBinaryLevelOne)
    {e : ℕ × ℕ} (he : e ∈ N.edges) (he1 : e.1 = N.root) : e ∈ S := by
  classical
  cases t with
  | leaf a =>
    -- the root of `N` is the leaf of `a`, which has no child
    exfalso
    have hroot : N.root = N.leaf a := by
      rw [← H.root_preserved]
      exact H.leaves_preserved [] (PhyloTree.root_mem_nodes _) a rfl
    have ha : a ∈ N.taxa := by
      rw [H.taxa_preserved]
      simp [PhyloTree.taxa, PhyloTree.labels]
    have hzero := (hN.2.2.2.2.2.2.2.1 a ha).2.2
    have hpos : 0 < N.outdegree (N.leaf a) :=
      Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, he1.trans hroot⟩⟩
    omega
  | fork l r =>
    -- the wires above `[false]` and `[true]` leave the root through distinct edges
    have hf : [false] ∈ (PhyloTree.fork l r).nodes :=
      PhyloTree.mem_fork_nodes.mpr (Or.inr (Or.inl ⟨[], l.root_mem_nodes, rfl⟩))
    have ht : [true] ∈ (PhyloTree.fork l r).nodes :=
      PhyloTree.mem_fork_nodes.mpr (Or.inr (Or.inr ⟨[], r.root_mem_nodes, rfl⟩))
    obtain ⟨x₁, hx₁S, hx₁⟩ := H.exists_first_edge hf (List.cons_ne_nil _ _)
    obtain ⟨x₂, hx₂S, hx₂⟩ := H.exists_first_edge ht (List.cons_ne_nil _ _)
    change (H.original [], x₁) ∈ S at hx₁S
    change (H.original [], x₂) ∈ S at hx₂S
    rw [H.root_preserved] at hx₁S hx₂S
    have himg {p : Address} (hp : p ∈ (PhyloTree.fork l r).nodes) :
        H.original p ∈ (PhyloTree.fork l r).nodes.image H.original :=
      Finset.mem_image_of_mem _ hp
    have hne : x₁ ≠ x₂ := by
      rintro rfl
      rcases hx₁ with h₁ | h₁ <;> rcases hx₂ with h₂ | h₂
      · exact absurd (H.original_injective hf ht (h₁.symm.trans h₂)) (by simp)
      · exact Finset.disjoint_left.mp (H.wire_laws _ ht (List.cons_ne_nil _ _)).2.2.2.2 h₂
          (h₁ ▸ himg hf)
      · exact Finset.disjoint_left.mp (H.wire_laws _ hf (List.cons_ne_nil _ _)).2.2.2.2 h₁
          (h₂ ▸ himg ht)
      · exact Finset.disjoint_left.mp (H.interiors_disjoint
          (Finset.mem_erase.mpr ⟨List.cons_ne_nil _ _, hf⟩)
          (Finset.mem_erase.mpr ⟨List.cons_ne_nil _ _, ht⟩) (by simp)) h₁ h₂
    -- a third edge out of the root would exceed its outdegree
    by_contra heS
    have hsub : ({(N.root, x₁), (N.root, x₂), e} : Finset (ℕ × ℕ)) ⊆
        N.edges.filter (fun d => d.1 = N.root) := by
      intro d hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with rfl | rfl | rfl
      · exact Finset.mem_filter.mpr ⟨H.switching.1 hx₁S, rfl⟩
      · exact Finset.mem_filter.mpr ⟨H.switching.1 hx₂S, rfl⟩
      · exact Finset.mem_filter.mpr ⟨he, he1⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem, Finset.card_pair] at hcard
    · have h2 := RootedNetwork.outdegree_le_two hN hN.1
      change _ ≤ N.outdegree N.root at hcard
      omega
    · intro h
      exact heS (h ▸ hx₂S)
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨fun h => hne (Prod.ext_iff.mp h).2, fun h => heS (h ▸ hx₁S)⟩

end SupportSubdivision

namespace DisplayedSubdivision

variable {t : PhyloTree} {N : RootedNetwork} {S : Finset (ℕ × ℕ)}

/-- If the switching keeps the edges out of the root of `N`, the root of `T` is the root of `N`:
otherwise the root of `N` would have an edge out of it outside the switching
(`DisplayedSubdivision.root_above`). -/
theorem original_nil_eq_root (H : DisplayedSubdivision t N S) (hN : N.RootedBinaryLevelOne)
    (hroot : ∀ e ∈ N.edges, e.1 = N.root → e ∈ S) : H.original [] = N.root := by
  by_contra hne
  obtain ⟨_, _, w, hw, _⟩ := H.root_above hN hne
  exact (Finset.mem_sdiff.mp hw).2 (hroot _ (Finset.mem_sdiff.mp hw).1 rfl)

/-- If the root of `T` is the root of `N`, the root wire is the root of `N` alone. -/
theorem rootWire_eq_of_original (H : DisplayedSubdivision t N S)
    (h : H.original [] = N.root) : H.rootWire = [N.root] :=
  eq_singleton_of_head?_getLast? H.rootWire_laws.1 H.rootWire_laws.2.1
    (h ▸ H.rootWire_laws.2.2.1)

/-- The root of `T` is the root of `N` iff the switching keeps the edges out of the root of `N`. -/
theorem original_nil_eq_root_iff (H : DisplayedSubdivision t N S) (hN : N.RootedBinaryLevelOne) :
    H.original [] = N.root ↔ ∀ e ∈ N.edges, e.1 = N.root → e ∈ S := by
  constructor
  · intro h e he he1
    exact (H.toSupport (H.rootWire_eq_of_original h)).rootEdges_mem hN he he1
  · exact H.original_nil_eq_root hN

/-- A displayed subdivision whose switching keeps the edges out of the root of `N` is a support
subdivision: the root of `T` is the root of `N`. -/
def toSupportOfRootEdges (H : DisplayedSubdivision t N S) (hN : N.RootedBinaryLevelOne)
    (hroot : ∀ e ∈ N.edges, e.1 = N.root → e ∈ S) : SupportSubdivision t N S :=
  H.toSupport (H.rootWire_eq_of_original (H.original_nil_eq_root hN hroot))

end DisplayedSubdivision

namespace RootedNetwork

variable {N : RootedNetwork} {S : Finset (ℕ × ℕ)}

/-- The switching `S` of a rooted binary level-1 network `N` is a subdivision of a well-labelled
tree with the root of the tree at the root of `N` (`SupportSubdivision`) iff `S` keeps the edges
out of the root of `N`. In that case `N` is built on the tree of `S` with the root kept. -/
theorem exists_support_iff (hN : N.RootedBinaryLevelOne) (hS : N.Switching S) :
    (∃ t : PhyloTree, t.WellLabelled ∧ t.taxa = N.taxa ∧ Nonempty (SupportSubdivision t N S)) ↔
      ∀ e ∈ N.edges, e.1 = N.root → e ∈ S := by
  constructor
  · rintro ⟨t, _, _, ⟨H⟩⟩ e he he1
    exact H.rootEdges_mem hN he he1
  · intro hroot
    obtain ⟨t, ht, htaxa, ⟨H⟩⟩ := exists_displayedSubdivision hN hS
    exact ⟨t, ht, htaxa, ⟨H.toSupportOfRootEdges hN hroot⟩⟩

/-- Some switching of a rooted binary level-1 network keeps the edges out of its root: at each
child of the root, keep the edge from the root, and elsewhere the edge of any switching. -/
theorem exists_switching_rootEdges (hN : N.RootedBinaryLevelOne) :
    ∃ S, N.Switching S ∧ ∀ e ∈ N.edges, e.1 = N.root → e ∈ S := by
  classical
  obtain ⟨R, hR⟩ := exists_switching hN
  refine ⟨R.filter (fun e => (N.root, e.2) ∉ N.edges) ∪ N.edges.filter (fun e => e.1 = N.root),
    ⟨?_, fun v hv hvr => ?_⟩, fun e he he1 => Finset.mem_union_right _
      (Finset.mem_filter.mpr ⟨he, he1⟩)⟩
  · intro e he
    rcases Finset.mem_union.mp he with h | h
    · exact hR.1 (Finset.mem_filter.mp h).1
    · exact (Finset.mem_filter.mp h).1
  · by_cases hrv : (N.root, v) ∈ N.edges
    -- at a child of the root, the edge from the root alone
    · have hfilter : (R.filter (fun e => (N.root, e.2) ∉ N.edges) ∪
          N.edges.filter (fun e => e.1 = N.root)).filter (fun e => e.2 = v) = {(N.root, v)} := by
        ext e
        simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_singleton]
        constructor
        · rintro ⟨⟨he, hn⟩ | ⟨he, he1⟩, hev⟩
          · exact absurd (hev ▸ hrv) hn
          · exact Prod.ext he1 hev
        · rintro rfl
          exact ⟨Or.inr ⟨hrv, rfl⟩, rfl⟩
      rw [hfilter, Finset.card_singleton]
    -- elsewhere, the edge of `R`
    · have hfilter : (R.filter (fun e => (N.root, e.2) ∉ N.edges) ∪
          N.edges.filter (fun e => e.1 = N.root)).filter (fun e => e.2 = v) =
          R.filter (fun e => e.2 = v) := by
        ext e
        simp only [Finset.mem_filter, Finset.mem_union]
        constructor
        · rintro ⟨⟨he, _⟩ | ⟨he, he1⟩, hev⟩
          · exact ⟨he, hev⟩
          · exact absurd (show (N.root, v) ∈ N.edges by rw [← he1, ← hev]; exact he) hrv
        · rintro ⟨he, hev⟩
          exact ⟨Or.inl ⟨he, by rw [hev]; exact hrv⟩, hev⟩
      rw [hfilter]
      exact hR.2 v hv hvr

/-- Every rooted binary level-1 network `N` is built, with the root kept, on a well-labelled tree
on its taxa: the tree of a switching that keeps the edges out of the root. -/
theorem exists_anchoredExtension (hN : N.RootedBinaryLevelOne) :
    ∃ t : PhyloTree, t.WellLabelled ∧ t.taxa = N.taxa ∧ N.AnchoredExtension t := by
  obtain ⟨S, hS, hroot⟩ := exists_switching_rootEdges hN
  obtain ⟨t, ht, htaxa, ⟨H⟩⟩ := (exists_support_iff hN hS).mpr hroot
  exact ⟨t, ht, htaxa, hN, S, ⟨H⟩⟩

/-- Section 2.4: "it is known that a level-1 phylogenetic network on n leaves will not have more
than n−1 reticulations". Every rooted binary level-1 network `N` has at most `n − 1`
reticulations, where `n` is the number of its taxa: it is built with the root kept on a
well-labelled tree on its taxa (`RootedNetwork.exists_anchoredExtension`), and a network built so
on a tree with `n` taxa has at most `n − 1` reticulations
(`RootedNetwork.anchored_reticulation_bound`). -/
theorem reticulationCount_le (hN : N.RootedBinaryLevelOne) :
    N.reticulationCount ≤ N.taxa.card - 1 := by
  obtain ⟨t, ht, htaxa, hA⟩ := exists_anchoredExtension hN
  rw [← htaxa]
  exact anchored_reticulation_bound ht hA

/-- Section 2.4's bound without truncated subtraction: a rooted binary level-1 network has fewer
reticulations than taxa. -/
theorem reticulationCount_lt (hN : N.RootedBinaryLevelOne) :
    N.reticulationCount < N.taxa.card := by
  have h1 := reticulationCount_le hN
  have h2 := (taxa_nonempty hN).card_pos
  omega

/-- Section 2.1: "N can be constructed by taking one of the trees t∈𝒯 and adding reticulations
(edges) to t". Every rooted binary level-1 network `N` is built with the root kept on a
well-labelled tree `t` on its taxa, the tree of a switching that keeps the edges out of the root of
`N`, and is isomorphic to the network obtained from `t` by adding an edge above each pair of a
cycle-separated family `E` (Definition 3). -/
theorem exists_canonical (hN : N.RootedBinaryLevelOne) :
    ∃ (t : PhyloTree) (E : Finset (Address × Address)), t.WellLabelled ∧ t.taxa = N.taxa ∧
      N.AnchoredExtension t ∧ EdgeAbove.CycleSeparated t E ∧
        Nonempty (N.Iso (Realization.graph t E)) := by
  obtain ⟨t, ht, htaxa, hA⟩ := exists_anchoredExtension hN
  obtain ⟨-, S, ⟨H⟩⟩ := hA
  exact ⟨t, H.extracted, ht, htaxa, ⟨hN, S, ⟨H⟩⟩, H.extracted_separated hN, H.canonical_iso hN⟩

/-- A vertex with edges to two distinct vertices `a` and `b` has no other child. -/
theorem child_eq_of_two {v a b c : ℕ} (hN : N.RootedBinaryLevelOne) (ha : (v, a) ∈ N.edges)
    (hb : (v, b) ∈ N.edges) (hab : a ≠ b) (hc : (v, c) ∈ N.edges) : c = a ∨ c = b := by
  classical
  by_contra h
  simp only [not_or] at h
  have hsub : ({(v, a), (v, b), (v, c)} : Finset (ℕ × ℕ)) ⊆ N.edges.filter (fun e => e.1 = v) := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨ha, rfl⟩
    · exact Finset.mem_filter.mpr ⟨hb, rfl⟩
    · exact Finset.mem_filter.mpr ⟨hc, rfl⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem, Finset.card_pair] at hcard
  · have h2 := outdegree_le_two hN (show v ∈ N.vertices from (hN.2.1 _ ha).1)
    change _ ≤ N.outdegree v at hcard
    omega
  · exact fun h' => h.2 (Prod.ext_iff.mp h').2.symm
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h' => hab (Prod.ext_iff.mp h').2, fun h' => h.1 (Prod.ext_iff.mp h').2.symm⟩

/-- If the root of `N` has an outgroup leaf as a child, every switching keeps the edges out of the
root. An edge `(N.root, y)` outside the switching `S` would make `y` a reticulation, whose edge in
`S` comes from a vertex `x` other than the root. The path of `S` from the root to `x` starts with an
edge into the outgroup leaf, which has no child, or with the edge `(N.root, y)`, which is not in
`S`. -/
theorem rootEdges_mem_of_outgroup (hN : N.RootedBinaryLevelOne) (hS : N.Switching S) {z : ℕ}
    (hz : z ∈ N.taxa) (hzr : (N.root, N.leaf z) ∈ N.edges) :
    ∀ e ∈ N.edges, e.1 = N.root → e ∈ S := by
  classical
  rintro ⟨r, y⟩ he (rfl : r = N.root)
  by_contra heS
  have hdel : (N.root, y) ∈ N.edges \ S := Finset.mem_sdiff.mpr ⟨he, heS⟩
  have hleaf0 := (hN.2.2.2.2.2.2.2.1 z hz).2.2
  -- `y` is a reticulation, not the outgroup leaf
  have hy2 := (deleted_edge_target_reticulation hN hS hdel).1
  have hyz : y ≠ N.leaf z := by
    intro h
    have h1 := (hN.2.2.2.2.2.2.2.1 z hz).2.1
    rw [← h, ite_eq_right (fun h' => edge_ne hN he h'.symm)] at h1
    change N.indegree y = 2 at hy2
    omega
  -- the edge of `S` into `y` comes from a vertex `x` other than the root
  have hyN : y ∈ N.vertices := (hN.2.1 _ he).2
  have hyr : y ≠ N.root := fun h => edge_ne hN he h.symm
  obtain ⟨f, hf⟩ := Finset.card_pos.mp (show 0 < (S.filter (fun e => e.2 = y)).card by
    rw [hS.2 y hyN hyr]; omega)
  obtain ⟨hfS, hfy⟩ := Finset.mem_filter.mp hf
  set x := f.1 with hx
  have hxS : (x, y) ∈ S := by
    rw [← hfy]
    exact hfS
  have hxr : x ≠ N.root := fun h => heS (h ▸ hxS)
  -- the path of `S` from the root to `x`
  rcases (switching_reachable hN hS (hN.2.1 _ (hS.1 hxS)).1).cases_head with h | ⟨c, hrc, hcx⟩
  · exact hxr h.symm
  rcases child_eq_of_two hN hzr he hyz.symm (hS.1 hrc) with rfl | rfl
  -- through the outgroup leaf, which has no child
  · rcases hcx.cases_head with h | ⟨d, hzd, _⟩
    · have hpos : 0 < N.outdegree (N.leaf z) :=
        Finset.card_pos.mpr ⟨_, Finset.mem_filter.mpr ⟨hS.1 hxS, h.symm⟩⟩
      omega
    · have hpos : 0 < N.outdegree (N.leaf z) :=
        Finset.card_pos.mpr ⟨_, Finset.mem_filter.mpr ⟨hS.1 hzd, rfl⟩⟩
      omega
  -- through the edge `(N.root, y)`, which is not in `S`
  · exact heS hrc

/-- Section 3.2, "any tree t∈Q(N_r) can be used as the basis for N (i.e. N can be obtained by
adding reticulate edges to t)", with an outgroup: if the root of `N` has an outgroup leaf as a
child, the tree of every switching `S` keeps the root, and `N` is built on it with the root kept.
Without the outgroup this can fail when a child of the root is a reticulation (the report's E8). -/
theorem exists_support_of_outgroup (hN : N.RootedBinaryLevelOne) (hS : N.Switching S) {z : ℕ}
    (hz : z ∈ N.taxa) (hzr : (N.root, N.leaf z) ∈ N.edges) :
    ∃ t : PhyloTree, t.WellLabelled ∧ t.taxa = N.taxa ∧ Nonempty (SupportSubdivision t N S) :=
  (exists_support_iff hN hS).mpr (rootEdges_mem_of_outgroup hN hS hz hzr)

/-- Section 3.2, with an outgroup: if the root of `N` has an outgroup leaf as a child, every tree
on which `N` is built in the sense of Definition 1 has `N` built on it with the root kept. -/
theorem BuiltOn.anchored_of_outgroup {t : PhyloTree} (hN : N.BuiltOn t) {z : ℕ}
    (hz : z ∈ N.taxa) (hzr : (N.root, N.leaf z) ∈ N.edges) : N.AnchoredExtension t := by
  obtain ⟨hbin, S, ⟨H⟩⟩ := hN
  exact ⟨hbin, S, ⟨H.toSupportOfRootEdges hbin
    (rootEdges_mem_of_outgroup hbin H.switching hz hzr)⟩⟩

/-- Section 3.2, "N can be obtained by adding reticulate edges to t", with an outgroup: if the root
of `N` has an outgroup leaf as a child, then for every tree `t` on which `N` is built in the sense
of Definition 1, `N` is isomorphic to the network obtained from `t` by adding an edge above each
pair of a cycle-separated family `E` (Definition 3). -/
theorem BuiltOn.exists_canonical_of_outgroup {t : PhyloTree} (hN : N.BuiltOn t) {z : ℕ}
    (hz : z ∈ N.taxa) (hzr : (N.root, N.leaf z) ∈ N.edges) :
    ∃ E : Finset (Address × Address), EdgeAbove.CycleSeparated t E ∧
      Nonempty (N.Iso (Realization.graph t E)) := by
  obtain ⟨hbin, S, ⟨H⟩⟩ := hN.anchored_of_outgroup hz hzr
  exact ⟨H.extracted, H.extracted_separated hbin, H.canonical_iso hbin⟩

end RootedNetwork

end Camus
