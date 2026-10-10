module

public import Camus.Network.TreeBased.Main

/-!
# The quartets displayed by a network are those of its trees

Definition 1 sets Q(N_r) = ∪_{t∈𝒯} Q(t), where 𝒯 is the set of the trees of `N`: delete one of the
two edges into each reticulation, in each of the possible ways, and clean up. The library's
`RootedNetwork.DisplaysQuartet` tests a quartet on the switchings themselves, before the clean-up:
some edge of some switching separates its two pairs. This file shows that the two readings agree.
For a displayed subdivision of `t` in `N` through the switching `S` (`DisplayedSubdivision`), the
taxa below the image of a vertex `p` of `t` in `S` are the clade of `p` in `t`
(`DisplayedSubdivision.cladeBelow_original`), and so are the taxa below every interior vertex of the
wire above `p` (`DisplayedSubdivision.cladeBelow_interior`), while every vertex of the root wire
has all the taxa below it. So `t` induces a quartet iff some edge of `S` cuts it
(`DisplayedSubdivision.induced_iff_cuts`). Every switching gives such a tree
(`RootedNetwork.exists_displayedSubdivision`), so `N` displays a quartet iff some tree on which `N`
is built (Definition 1) induces it (`RootedNetwork.displays_iff_exists_builtOn`).

## Main results

* `DisplayedSubdivision.wellLabelled`: a tree on which a network is built is well-labelled.
* `DisplayedSubdivision.cladeBelow_original`: the taxa below the image of a vertex `p` of `t` are
  the clade of `p`.
* `DisplayedSubdivision.induced_iff_cuts`: `t` induces the quartets cut by the edges of `S`.
* `RootedNetwork.displays_iff_exists_builtOn`: Definition 1, Q(N_r) = ∪_{t∈𝒯} Q(t).
-/

@[expose] public section

namespace Camus

/-- A tree whose leaves with the same label have the same address is well-labelled. -/
theorem PhyloTree.wellLabelled_of_leaves {t : PhyloTree}
    (h : ∀ p q a, t.nodeAt p = some (.leaf a) → t.nodeAt q = some (.leaf a) → p = q) :
    t.WellLabelled := by
  induction t with
  | leaf a => exact List.nodup_singleton a
  | fork l r ihl ihr =>
    refine List.nodup_append.mpr ⟨ihl ?_, ihr ?_, ?_⟩
    · intro p q a hp hq
      exact List.tail_eq_of_cons_eq (h (false :: p) (false :: q) a hp hq)
    · intro p q a hp hq
      exact List.tail_eq_of_cons_eq (h (true :: p) (true :: q) a hp hq)
    · rintro a ha b hb rfl
      obtain ⟨p, hp⟩ := PhyloTree.exists_leaf_address ha
      obtain ⟨q, hq⟩ := PhyloTree.exists_leaf_address hb
      exact absurd (h (false :: p) (true :: q) a hp hq) (by simp)

/-- Along a path whose edges are in `S`, every vertex is reached from the first one. -/
theorem reach_of_mem_path {S : Finset (ℕ × ℕ)} {L : List ℕ} (hL : wireEdges L ⊆ S) {a x : ℕ}
    (ha : L.head? = some a) (hx : x ∈ L) : Relation.ReflTransGen (fun u v => (u, v) ∈ S) a x := by
  induction L generalizing a with
  | nil => simp at ha
  | cons b L ih =>
    simp only [List.head?_cons, Option.some.injEq] at ha
    subst ha
    rcases List.mem_cons.mp hx with rfl | hx
    · exact .refl
    · cases L with
      | nil => simp at hx
      | cons c L =>
        have hbc : (b, c) ∈ S :=
          hL (by rw [Realization.wireEdges_cons_cons]; exact Finset.mem_insert_self _ _)
        have hL' : wireEdges (c :: L) ⊆ S := fun e he =>
          hL (by rw [Realization.wireEdges_cons_cons]; exact Finset.mem_insert_of_mem he)
        exact Relation.ReflTransGen.head hbc (ih hL' rfl hx)

/-- Along a path whose edges are in `S`, the last vertex is reached from every vertex. -/
theorem reach_getLast_of_path {S : Finset (ℕ × ℕ)} {L : List ℕ} (hL : wireEdges L ⊆ S)
    {x z : ℕ} (hx : x ∈ L) (hz : L.getLast? = some z) :
    Relation.ReflTransGen (fun u v => (u, v) ∈ S) x z := by
  induction L generalizing x with
  | nil => simp at hx
  | cons b L ih =>
    cases L with
    | nil =>
      simp only [List.mem_singleton] at hx
      simp only [List.getLast?_singleton, Option.some.injEq] at hz
      rw [hx, hz]
    | cons c L =>
      have hbc : (b, c) ∈ S :=
        hL (by rw [Realization.wireEdges_cons_cons]; exact Finset.mem_insert_self _ _)
      have hL' : wireEdges (c :: L) ⊆ S := fun e he =>
        hL (by rw [Realization.wireEdges_cons_cons]; exact Finset.mem_insert_of_mem he)
      rw [List.getLast?_cons_cons] at hz
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Relation.ReflTransGen.head hbc (ih hL' List.mem_cons_self hz)
      · exact ih hL' hx hz

/-- A path with at least two vertices has an edge into its last vertex. -/
theorem exists_edge_into_getLast : ∀ {L : List ℕ}, 2 ≤ L.length → ∀ {z : ℕ},
    L.getLast? = some z → ∃ x, (x, z) ∈ wireEdges L
  | [], h, _, _ => by simp at h
  | [_], h, _, _ => by simp at h
  | [a, b], _, z, hz => by
    simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at hz
    subst hz
    exact ⟨a, by simp [wireEdges]⟩
  | a :: b :: c :: rest, _, z, hz => by
    rw [List.getLast?_cons_cons] at hz
    obtain ⟨x, hx⟩ := exists_edge_into_getLast (L := b :: c :: rest) (by simp) hz
    exact ⟨x, by rw [Realization.wireEdges_cons_cons]; exact Finset.mem_insert_of_mem hx⟩

namespace DisplayedSubdivision

variable {t : PhyloTree} {N : RootedNetwork} {S : Finset (ℕ × ℕ)}

/-- A tree on which a network is built is well-labelled: two leaves with the same label `a` are
sent to the leaf of `a`, and the vertices of `t` are sent injectively. -/
theorem wellLabelled (H : DisplayedSubdivision t N S) : t.WellLabelled :=
  PhyloTree.wellLabelled_of_leaves fun p q a hp hq =>
    H.original_injective ((t.mem_nodes_iff p).mpr ⟨_, hp⟩) ((t.mem_nodes_iff q).mpr ⟨_, hq⟩)
      ((H.leaves_preserved p ((t.mem_nodes_iff p).mpr ⟨_, hp⟩) a hp).trans
        (H.leaves_preserved q ((t.mem_nodes_iff q).mpr ⟨_, hq⟩) a hq).symm)

/-- The edges of the wire above a non-root vertex of `t` are edges of `S`. -/
theorem wireEdges_subset (H : DisplayedSubdivision t N S) {p : Address} (hp : p ∈ t.nodes)
    (hp0 : p ≠ []) : wireEdges (H.wire p) ⊆ S := fun e he =>
  (Finset.ext_iff.mp H.edges_covered e).mpr
    (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨p, Finset.mem_erase.mpr ⟨hp0, hp⟩, he⟩))

/-- The edges of the root wire are edges of `S`. -/
theorem rootWire_edges_subset (H : DisplayedSubdivision t N S) : wireEdges H.rootWire ⊆ S :=
  fun e he => (Finset.ext_iff.mp H.edges_covered e).mpr (Finset.mem_union_right _ he)

/-- The image of a descendant `p ++ s` of a vertex `p` of `t` is reached from the image of `p`
along `S`, through the wires between them. -/
theorem reach_original_append (H : DisplayedSubdivision t N S) (p : Address) (s : List Bool) :
    p ++ s ∈ t.nodes →
      Relation.ReflTransGen (fun u v => (u, v) ∈ S) (H.original p) (H.original (p ++ s)) := by
  induction s using List.reverseRecOn with
  | nil => intro _; simp only [List.append_nil]; exact .refl
  | append_singleton s b ih =>
    intro hq
    rw [← List.append_assoc] at hq ⊢
    have hq0 : p ++ s ++ [b] ≠ [] := by simp
    have hmid : p ++ s ∈ t.nodes := t.nodes_prefix_closed hq (List.prefix_append _ _)
    obtain ⟨_, _, hhead, hlast, _⟩ := H.wire_laws _ hq hq0
    rw [Realization.parent_append_singleton] at hhead
    exact (ih hmid).trans (reach_of_mem_path (H.wireEdges_subset hq hq0) hhead
      (List.mem_of_getLast? hlast))

/-- The image of a descendant `q` of a vertex `p` of `t` is reached from the image of `p` along
`S`. -/
theorem reach_original (H : DisplayedSubdivision t N S) {p q : Address} (hq : q ∈ t.nodes)
    (hpq : p <+: q) :
    Relation.ReflTransGen (fun u v => (u, v) ∈ S) (H.original p) (H.original q) := by
  obtain ⟨s, rfl⟩ := hpq
  exact H.reach_original_append p s hq

/-- A vertex of the wire above `p`, other than its last one, is the image of the parent of `p` or
an interior vertex of the wire. -/
theorem mem_dropLast_wire (H : DisplayedSubdivision t N S) {p : Address} (hp : p ∈ t.nodes)
    (hp0 : p ≠ []) {x : ℕ} (hx : x ∈ (H.wire p).dropLast) :
    x = H.original (parent p) ∨ x ∈ wireInterior (H.wire p) := by
  obtain ⟨hlen, _, hhead, _, _⟩ := H.wire_laws p hp hp0
  obtain ⟨a, b, rest, hL⟩ : ∃ a b rest, H.wire p = a :: b :: rest := by
    match h : H.wire p, hlen with
    | a :: b :: rest, _ => exact ⟨a, b, rest, rfl⟩
  rw [hL, List.head?_cons, Option.some.injEq] at hhead
  rw [hL, List.dropLast_cons_of_ne_nil (List.cons_ne_nil _ _), List.mem_cons] at hx
  rcases hx with rfl | hx
  · exact Or.inl hhead
  · right
    rw [hL]
    exact List.mem_toFinset.mpr hx

/-- A vertex of the wire above `p`, other than its first one, is an interior vertex of the wire or
the image of `p`. -/
theorem mem_tail_wire (H : DisplayedSubdivision t N S) {p : Address} (hp : p ∈ t.nodes)
    (hp0 : p ≠ []) {x : ℕ} (hx : x ∈ (H.wire p).tail) :
    x ∈ wireInterior (H.wire p) ∨ x = H.original p := by
  obtain ⟨hlen, _, _, hlast, _⟩ := H.wire_laws p hp hp0
  obtain ⟨a, b, rest, hL⟩ : ∃ a b rest, H.wire p = a :: b :: rest := by
    match h : H.wire p, hlen with
    | a :: b :: rest, _ => exact ⟨a, b, rest, rfl⟩
  rw [hL, List.getLast?_cons_cons, List.getLast?_eq_some_getLast (List.cons_ne_nil b rest),
    Option.some.injEq] at hlast
  rw [hL, List.tail_cons, ← List.dropLast_append_getLast (List.cons_ne_nil b rest),
    List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | hx
  · left
    rw [hL]
    exact List.mem_toFinset.mpr hx
  · exact Or.inr (hx.trans hlast)

/-- The vertices below the vertex `p` of `t` in the subdivision: the images of the descendants of
`p` and the interior vertices of the wires above them (above `p` included). They are closed under
the edges of `S` (`DisplayedSubdivision.below_step`). -/
def Below (H : DisplayedSubdivision t N S) (p : Address) (y : ℕ) : Prop :=
  (∃ q ∈ t.nodes, p <+: q ∧ y = H.original q) ∨
    ∃ q ∈ t.nodes, q ≠ [] ∧ p <+: q ∧ y ∈ wireInterior (H.wire q)

/-- The edges of `S` leave the vertices below `p` only to vertices below `p`. An edge out of the
image of a vertex `q` is the first edge of the wire above a child of `q`; an edge out of an
interior vertex of a wire is the next edge of that wire; the root wire leaves no vertex below
`p`. -/
theorem below_step (H : DisplayedSubdivision t N S) {p : Address} {y y' : ℕ} (hy : H.Below p y)
    (hyy : (y, y') ∈ S) : H.Below p y' := by
  rcases Finset.mem_union.mp ((Finset.ext_iff.mp H.edges_covered _).mp hyy) with he | he
  · obtain ⟨q', hq', he⟩ := Finset.mem_biUnion.mp he
    obtain ⟨hq'0, hq'⟩ := Finset.mem_erase.mp hq'
    have hy1 : y ∈ (H.wire q').dropLast := Realization.edge_first_mem_dropLast he
    have hy2 : y' ∈ (H.wire q').tail := Realization.edge_second_mem_tail he
    -- the next vertex of the wire above `q'` is below `q'`
    have hnext : p <+: q' → H.Below p y' := fun hpq' => by
      rcases H.mem_tail_wire hq' hq'0 hy2 with h | h
      · exact Or.inr ⟨q', hq', hq'0, hpq', h⟩
      · exact Or.inl ⟨q', hq', hpq', h⟩
    have hpar : parent q' ∈ t.nodes := t.nodes_prefix_closed hq' (parent_prefix q')
    rcases hy with ⟨q, hq, hpq, rfl⟩ | ⟨q, hq, hq0, hpq, hyq⟩
    -- the image of `q` starts the wire above a child of `q`
    · rcases H.mem_dropLast_wire hq' hq'0 hy1 with h | h
      · rw [H.original_injective hq hpar h] at hpq
        exact hnext (hpq.trans (parent_prefix q'))
      · exact absurd (Finset.mem_image_of_mem _ hq)
          (Finset.disjoint_left.mp (H.wire_laws q' hq' hq'0).2.2.2.2 h)
    -- an interior vertex lies inside one wire
    · rcases H.mem_dropLast_wire hq' hq'0 hy1 with h | h
      · exact absurd (h ▸ Finset.mem_image_of_mem _ hpar)
          (Finset.disjoint_left.mp (H.wire_laws q hq hq0).2.2.2.2 hyq)
      · have hqq : q = q' := by
          by_contra hne
          exact Finset.disjoint_left.mp (H.interiors_disjoint (Finset.mem_erase.mpr ⟨hq0, hq⟩)
            (Finset.mem_erase.mpr ⟨hq'0, hq'⟩) hne) hyq h
        exact hnext (hqq ▸ hpq)
  -- the vertices of the root wire but its last are neither images nor interior vertices
  · exfalso
    have hy1 : y ∈ H.rootWire.dropLast.toFinset :=
      List.mem_toFinset.mpr (Realization.edge_first_mem_dropLast he)
    rcases hy with ⟨q, hq, _, rfl⟩ | ⟨q, hq, hq0, _, hyq⟩
    · exact Finset.disjoint_left.mp H.rootWire_laws.2.2.2 hy1 (Finset.mem_image_of_mem _ hq)
    · exact Finset.disjoint_left.mp (H.rootWire_disjoint q hq hq0) hy1 hyq

/-- A vertex reached along `S` from a vertex below `p` is below `p`. -/
theorem below_of_reach (H : DisplayedSubdivision t N S) {p : Address} {y y' : ℕ}
    (hy : H.Below p y) (h : Relation.ReflTransGen (fun u v => (u, v) ∈ S) y y') : H.Below p y' := by
  induction h with
  | refl => exact hy
  | tail _ hstep ih => exact H.below_step ih hstep

/-- The leaf of a taxon `a` of `t` is the image of the leaf of `t` labelled `a`. -/
theorem leaf_eq_original (H : DisplayedSubdivision t N S) {a : ℕ} (ha : a ∈ t.taxa) :
    N.leaf a = H.original (Realization.leafAddress t a) :=
  (H.leaves_preserved _ (Realization.leafAddress_mem_nodes ha) a
    (Realization.leafAddress_nodeAt ha)).symm

/-- A leaf below `p` lies below `p` in `t`. -/
theorem prefix_of_below_leaf (H : DisplayedSubdivision t N S) {p : Address} {a : ℕ}
    (ha : a ∈ t.taxa) (hb : H.Below p (N.leaf a)) : p <+: Realization.leafAddress t a := by
  have hℓ := Realization.leafAddress_mem_nodes ha
  rw [H.leaf_eq_original ha] at hb
  rcases hb with ⟨q, hq, hpq, he⟩ | ⟨q, hq, hq0, _, hint⟩
  · rw [H.original_injective hℓ hq he]
    exact hpq
  · exact absurd (Finset.mem_image_of_mem _ hℓ)
      (Finset.disjoint_left.mp (H.wire_laws q hq hq0).2.2.2.2 hint)

/-- The taxa below the image of a vertex `p` of a well-labelled tree `t` in the switching `S` are
the clade of `p` in `t`. -/
theorem cladeBelow_original (H : DisplayedSubdivision t N S) (ht : t.WellLabelled)
    {p : Address} (hp : p ∈ t.nodes) : N.cladeBelow S (H.original p) = t.taxaAt p := by
  ext a
  rw [RootedNetwork.mem_cladeBelow, PhyloTree.mem_taxaAt_iff ht hp, H.taxa_preserved]
  refine and_congr_right fun ha => ⟨fun hr => ?_, fun hpℓ => ?_⟩
  · exact H.prefix_of_below_leaf ha
      (H.below_of_reach (Or.inl ⟨p, hp, List.prefix_refl p, rfl⟩) hr)
  · rw [H.leaf_eq_original ha]
    exact H.reach_original (Realization.leafAddress_mem_nodes ha) hpℓ

/-- The taxa below an interior vertex of the wire above `p` are the clade of `p` in `t`. -/
theorem cladeBelow_interior (H : DisplayedSubdivision t N S) (ht : t.WellLabelled)
    {p : Address} (hp : p ∈ t.nodes) (hp0 : p ≠ []) {y : ℕ}
    (hy : y ∈ wireInterior (H.wire p)) : N.cladeBelow S y = t.taxaAt p := by
  ext a
  rw [RootedNetwork.mem_cladeBelow, PhyloTree.mem_taxaAt_iff ht hp, H.taxa_preserved]
  refine and_congr_right fun ha => ⟨fun hr => ?_, fun hpℓ => ?_⟩
  · exact H.prefix_of_below_leaf ha
      (H.below_of_reach (Or.inr ⟨p, hp, hp0, List.prefix_refl p, hy⟩) hr)
  -- `y` reaches the image of `p` along the wire, and then the leaf
  · have hyw : y ∈ H.wire p :=
      List.mem_of_mem_tail (List.dropLast_subset _ (List.mem_toFinset.mp hy))
    rw [H.leaf_eq_original ha]
    exact (reach_getLast_of_path (H.wireEdges_subset hp hp0) hyw
      (H.wire_laws p hp hp0).2.2.2.1).trans
      (H.reach_original (Realization.leafAddress_mem_nodes ha) hpℓ)

/-- All the taxa lie below every vertex of the root wire. -/
theorem cladeBelow_rootWire (H : DisplayedSubdivision t N S) {y : ℕ} (hy : y ∈ H.rootWire) :
    N.cladeBelow S y = N.taxa := by
  ext a
  rw [RootedNetwork.mem_cladeBelow]
  refine ⟨fun h => h.1, fun ha => ⟨ha, ?_⟩⟩
  have ha' : a ∈ t.taxa := H.taxa_preserved ▸ ha
  rw [H.leaf_eq_original ha']
  exact (reach_getLast_of_path H.rootWire_edges_subset hy H.rootWire_laws.2.2.1).trans
    (H.reach_original (Realization.leafAddress_mem_nodes ha') List.nil_prefix)

/-- Definition 1 for one tree: the tree `t` of a displayed subdivision induces the quartet `q` iff
the taxa of `q` are taxa of `N` and some edge `(x, y)` of the switching `S` cuts `q`, that is, the
taxa below `y` meet the taxa of `q` in one side of `q`. The clean-up of Definition 1, which turns
`S` into `t`, does not change the quartets cut by deleting one edge. -/
theorem induced_iff_cuts (H : DisplayedSubdivision t N S) (ht : t.WellLabelled) (q : Quartet) :
    q.induced t = true ↔
      q.taxa ⊆ N.taxa ∧ ∃ x y, (x, y) ∈ S ∧ q.cutBy (N.cladeBelow S y) = true := by
  rw [Quartet.induced_iff_taxaAt, H.taxa_preserved]
  refine and_congr_right fun hq => ⟨?_, ?_⟩
  -- the last edge of the wire above `p` enters the image of `p`
  · rintro ⟨p, hp, hp0, hcut⟩
    obtain ⟨hlen, _, _, hlast, _⟩ := H.wire_laws p hp hp0
    obtain ⟨x, hx⟩ := exists_edge_into_getLast hlen hlast
    exact ⟨x, H.original p, H.wireEdges_subset hp hp0 hx,
      by rw [H.cladeBelow_original ht hp]; exact hcut⟩
  · rintro ⟨x, y, hxy, hcut⟩
    rcases Finset.mem_union.mp ((Finset.ext_iff.mp H.edges_covered _).mp hxy) with he | he
    -- an edge of the wire above `p` enters an interior vertex of the wire or the image of `p`
    · obtain ⟨p, hp, he⟩ := Finset.mem_biUnion.mp he
      obtain ⟨hp0, hp⟩ := Finset.mem_erase.mp hp
      refine ⟨p, hp, hp0, ?_⟩
      rcases H.mem_tail_wire hp hp0 (Realization.edge_second_mem_tail he) with h | h
      · rw [← H.cladeBelow_interior ht hp hp0 h]
        exact hcut
      · rw [← H.cladeBelow_original ht hp, ← h]
        exact hcut
    -- an edge of the root wire has all the taxa below it, and cuts no quartet
    · have hy : y ∈ H.rootWire := List.mem_of_mem_tail (Realization.edge_second_mem_tail he)
      rw [H.cladeBelow_rootWire hy, q.cutBy_false_of_taxa_subset (hq.trans
        H.taxa_preserved.symm.subset)] at hcut
      exact absurd hcut (by simp)

end DisplayedSubdivision

/-- **Definition 1** (`mthst1`). Q(N_r) = ∪_{t∈𝒯} Q(t): a rooted binary level-1 network `N`
displays the quartet `q` iff some tree on which `N` is built, in the sense of Definition 1, induces
`q`. The trees of `𝒯` are the trees `t` with `N.BuiltOn t`, obtained from the switchings by the
clean-up; every switching gives one (`RootedNetwork.exists_displayedSubdivision`), and each of them
induces the quartets that the edges of its switching cut
(`DisplayedSubdivision.induced_iff_cuts`). -/
theorem RootedNetwork.displays_iff_exists_builtOn {N : RootedNetwork} (hN : N.RootedBinaryLevelOne)
    (q : Quartet) : N.DisplaysQuartet q ↔ ∃ t : PhyloTree, N.BuiltOn t ∧ q.induced t = true := by
  rw [displays_iff_cladeBelow hN]
  constructor
  · rintro ⟨hq, S, hS, x, y, hxy, hcut⟩
    obtain ⟨t, ht, -, ⟨H⟩⟩ := exists_displayedSubdivision hN hS
    exact ⟨t, ⟨hN, S, ⟨H⟩⟩, (H.induced_iff_cuts ht q).mpr ⟨hq, x, y, hxy, hcut⟩⟩
  · rintro ⟨t, ⟨_, S, ⟨H⟩⟩, hind⟩
    obtain ⟨hq, x, y, hxy, hcut⟩ := (H.induced_iff_cuts H.wellLabelled q).mp hind
    exact ⟨hq, S, H.switching, x, y, hxy, hcut⟩

end Camus
