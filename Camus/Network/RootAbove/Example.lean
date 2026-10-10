module

public import Camus.Network.RootAbove.Main
public import Camus.Network.RootAbove.Transport
public import Camus.DP.Theorem1

/-!
# A network built on `T` whose root lies above the root of `T`

Definition 1's class of networks built on `T` (`RootedNetwork.BuiltOn`) is larger than the class
of networks built on `T` with the root of `T` at the root (`RootedNetwork.AnchoredExtension`).
Take the tree `T = ((A,B),C)` (`Counterexamples.cherryTree`) and the network `N`
(`Counterexamples.rootAboveNet`) whose root `ρ` has two children: the root `r` of `T` and a
reticulation `w'` above `B`, whose other parent is the parent `a` of the cherry `(A,B)`. Its cycle
`ρ → r → a → w' ← ρ` has four vertices. Deleting the edge from `ρ` to `w'` leaves `T` below a
root with one child, so `N` is built on `T` in the sense of Definition 1. Deleting instead the
edge from `a` to `w'` gives the tree `((A,C),B)`; no switching of `N` is `T` with the root of `T`
at the root of `N`. The proof of the latter follows the wires: the wire above `C` must run
`ρ → r → C`, so the wire above the cherry must leave `ρ` through `w'`, below which `A` is not.

## Main results

* `Counterexamples.rootAboveNet_builtOn`: `N` is built on `T` in the sense of Definition 1.
* `Counterexamples.rootAboveNet_not_anchored`: `N` is not built on `T` with the root kept.
* `Counterexamples.builtOn_not_anchored`: the class of Definition 1 is larger.
* `Counterexamples.rootAboveNet_not_iso_graph`, `Counterexamples.camus_output_not_rootAboveNet`:
  no network obtained from `T` by adding edges, in particular no output of CAMUS on `T`, is
  isomorphic to `N`, although `T` is a tree of `N` (Section 3.2 says that any tree of `N` can be
  used as its basis).
-/

@[expose] public section

namespace Camus

namespace Counterexamples

/-- The tree `((A,B),C)`, with `A = 0`, `B = 1`, `C = 2`. -/
def cherryTree : PhyloTree := .fork (.fork (.leaf 0) (.leaf 1)) (.leaf 2)

/-- The network with root `ρ = 0` above the root `r = 1` of `((A,B),C)`. The root `0` has children
`1` and the reticulation `w' = 3`; the vertex `1` has children `a = 2`, the parent of the cherry,
and the leaf `6` of `C`; the vertex `2` has children the leaf `4` of `A` and `3`; the reticulation
`3` has the leaf `5` of `B` as its child. Every edge goes from a smaller to a larger vertex. -/
def rootAboveNet : RootedNetwork where
  vertices := {0, 1, 2, 3, 4, 5, 6}
  edges := {(0, 1), (0, 3), (1, 2), (1, 6), (2, 3), (2, 4), (3, 5)}
  root := 0
  taxa := {0, 1, 2}
  leaf := fun a => a + 4

/-- The neighbours of each vertex in the undirected graph of `rootAboveNet`. -/
theorem rootAboveNet_nbrs {v w : ℕ} (h : rootAboveNet.underlying.Adj v w) :
    (v = 0 → w = 1 ∨ w = 3) ∧ (v = 1 → w = 0 ∨ w = 2 ∨ w = 6) ∧
      (v = 2 → w = 1 ∨ w = 3 ∨ w = 4) ∧ (v = 3 → w = 0 ∨ w = 2 ∨ w = 5) ∧
      (v = 4 → w = 2) ∧ (v = 5 → w = 3) ∧ (v = 6 → w = 1) ∧ v ≤ 6 := by
  obtain ⟨_, h | h⟩ := h <;> simp [rootAboveNet] at h <;> omega

/-- In a cycle, a vertex whose neighbours on the cycle are among `a ≠ b` is adjacent on the cycle
to both. -/
theorem rootAbove_cycle_adj_of_nbrs {G : SimpleGraph ℕ} {u v a b : ℕ} {c : G.Walk u u}
    (hc : c.IsCycle)
    (hv : v ∈ c.support) (hab : a ≠ b) (hsub : ∀ w, c.toSubgraph.Adj v w → w = a ∨ w = b) :
    c.toSubgraph.Adj v a ∧ c.toSubgraph.Adj v b := by
  have h2 := hc.ncard_neighborSet_toSubgraph_eq_two hv
  have hs : c.toSubgraph.neighborSet v ⊆ {a, b} := fun w hw => hsub w hw
  have heq := Set.eq_of_subset_of_ncard_le hs (by rw [Set.ncard_pair hab, h2]) (Set.toFinite _)
  have ha : a ∈ c.toSubgraph.neighborSet v := heq ▸ Set.mem_insert a {b}
  have hb : b ∈ c.toSubgraph.neighborSet v := heq ▸ Set.mem_insert_of_mem a rfl
  exact ⟨ha, hb⟩

/-- A vertex with at most one neighbour on a cycle does not lie on it. -/
theorem rootAbove_cycle_not_mem_of_nbr {G : SimpleGraph ℕ} {u v a : ℕ} {c : G.Walk u u}
    (hc : c.IsCycle) (hsub : ∀ w, c.toSubgraph.Adj v w → w = a) : v ∉ c.support := by
  intro hv
  have h2 := hc.ncard_neighborSet_toSubgraph_eq_two hv
  have hs : c.toSubgraph.neighborSet v ⊆ {a} := fun w hw => hsub w hw
  have hle := Set.ncard_le_ncard hs (Set.finite_singleton a)
  rw [Set.ncard_singleton] at hle
  omega

/-- Every cycle of `rootAboveNet` is the cycle `0 - 1 - 2 - 3 - 0`: the leaves `4`, `5`, `6` have
one neighbour each, and each of `0`, `1`, `2`, `3` has two neighbours other than leaves. -/
theorem rootAboveNet_cycle_edges {u : ℕ} (c : rootAboveNet.underlying.Walk u u)
    (hc : c.IsCycle) :
    c.edges.toFinset = {s(0, 1), s(1, 2), s(2, 3), s(0, 3)} := by
  classical
  have hnb : ∀ {v w}, c.toSubgraph.Adj v w → rootAboveNet.underlying.Adj v w :=
    fun h => c.toSubgraph.adj_sub h
  have hmem : ∀ {v w}, c.toSubgraph.Adj v w → w ∈ c.support :=
    fun h => c.mem_verts_toSubgraph.mp (SimpleGraph.Subgraph.Adj.snd_mem h)
  -- the leaves are not on the cycle
  have h4 : 4 ∉ c.support := rootAbove_cycle_not_mem_of_nbr hc
    (fun w h => (rootAboveNet_nbrs (hnb h)).2.2.2.2.1 rfl)
  have h5 : 5 ∉ c.support := rootAbove_cycle_not_mem_of_nbr hc
    (fun w h => (rootAboveNet_nbrs (hnb h)).2.2.2.2.2.1 rfl)
  have h6 : 6 ∉ c.support := rootAbove_cycle_not_mem_of_nbr hc
    (fun w h => (rootAboveNet_nbrs (hnb h)).2.2.2.2.2.2.1 rfl)
  -- the neighbours on the cycle of `0`, `1`, `2`, `3`
  have hn0 : 0 ∈ c.support → c.toSubgraph.Adj 0 1 ∧ c.toSubgraph.Adj 0 3 := fun hv =>
    rootAbove_cycle_adj_of_nbrs hc hv (by decide) (fun w h => (rootAboveNet_nbrs (hnb h)).1 rfl)
  have hn1 : 1 ∈ c.support → c.toSubgraph.Adj 1 0 ∧ c.toSubgraph.Adj 1 2 := by
    intro hv
    refine rootAbove_cycle_adj_of_nbrs hc hv (by decide) (fun w h => ?_)
    rcases (rootAboveNet_nbrs (hnb h)).2.1 rfl with h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr h'
    · exact absurd (h' ▸ hmem h) h6
  have hn2 : 2 ∈ c.support → c.toSubgraph.Adj 2 1 ∧ c.toSubgraph.Adj 2 3 := by
    intro hv
    refine rootAbove_cycle_adj_of_nbrs hc hv (by decide) (fun w h => ?_)
    rcases (rootAboveNet_nbrs (hnb h)).2.2.1 rfl with h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr h'
    · exact absurd (h' ▸ hmem h) h4
  have hn3 : 3 ∈ c.support → c.toSubgraph.Adj 3 0 ∧ c.toSubgraph.Adj 3 2 := by
    intro hv
    refine rootAbove_cycle_adj_of_nbrs hc hv (by decide) (fun w h => ?_)
    rcases (rootAboveNet_nbrs (hnb h)).2.2.2.1 rfl with h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr h'
    · exact absurd (h' ▸ hmem h) h5
  -- the vertices of the cycle are among `0`, `1`, `2`, `3`
  have hcore : ∀ v ∈ c.support, v ≤ 3 := by
    intro v hv
    have h2 := hc.ncard_neighborSet_toSubgraph_eq_two hv
    obtain ⟨w, hw⟩ : (c.toSubgraph.neighborSet v).Nonempty :=
      Set.nonempty_of_ncard_ne_zero (by omega)
    have h6' := (rootAboveNet_nbrs (hnb hw)).2.2.2.2.2.2.2
    have : v ≠ 4 := fun h => h4 (h ▸ hv)
    have : v ≠ 5 := fun h => h5 (h ▸ hv)
    have : v ≠ 6 := fun h => h6 (h ▸ hv)
    omega
  -- `0` lies on the cycle, hence all four vertices do
  have hu := hcore u c.start_mem_support
  have h0 : 0 ∈ c.support := by
    rcases (show u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 3 by omega) with rfl | rfl | rfl | rfl
    · exact c.start_mem_support
    · exact hmem (hn1 c.start_mem_support).1
    · exact hmem (hn1 (hmem (hn2 c.start_mem_support).1)).1
    · exact hmem (hn3 c.start_mem_support).1
  have h2 : 2 ∈ c.support := hmem (hn1 (hmem (hn0 h0).1)).2
  ext e
  simp only [List.mem_toFinset, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro he
    induction e using Sym2.ind with
    | _ x y =>
      have hxy : c.toSubgraph.Adj x y := SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mpr he
      have hx := hcore x (c.mem_verts_toSubgraph.mp (SimpleGraph.Subgraph.Adj.fst_mem hxy))
      have hy := hcore y (hmem hxy)
      have hn := rootAboveNet_nbrs (hnb hxy)
      rcases (show x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 by omega) with rfl | rfl | rfl | rfl
      · rcases hn.1 rfl with rfl | rfl <;> simp
      · rcases hn.2.1 rfl with rfl | rfl | rfl <;> first | omega | simp [Sym2.eq_swap]
      · rcases hn.2.2.1 rfl with rfl | rfl | rfl <;> first | omega | simp [Sym2.eq_swap]
      · rcases hn.2.2.2.1 rfl with rfl | rfl | rfl <;> first | omega | simp [Sym2.eq_swap]
  · rintro (rfl | rfl | rfl | rfl)
    · exact SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mp (hn0 h0).1
    · exact SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mp (hn2 h2).1.symm
    · exact SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mp (hn2 h2).2
    · exact SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mp (hn0 h0).2

/-- `rootAboveNet` is a rooted binary level-1 network. -/
theorem rootAboveNet_levelOne : rootAboveNet.RootedBinaryLevelOne := by
  have hinc : ∀ e ∈ rootAboveNet.edges, e.1 < e.2 := by decide
  refine ⟨by decide, by decide, ?_, by decide, by decide, ?_, ?_, by decide, by decide, by decide,
    ?_⟩
  -- no directed cycle: every edge increases the vertex
  · have hlt : ∀ a b, Relation.TransGen (fun u w => (u, w) ∈ rootAboveNet.edges) a b → a < b := by
      intro a b h
      induction h with
      | single h => exact hinc _ h
      | tail _ h ih => exact ih.trans (hinc _ h)
    intro v hv
    exact lt_irrefl _ (hlt v v hv)
  -- every vertex is reachable from the root
  · have hstep : ∀ {a b c : ℕ}, (a, b) ∈ rootAboveNet.edges →
        Relation.ReflTransGen (fun u w => (u, w) ∈ rootAboveNet.edges) b c →
        Relation.ReflTransGen (fun u w => (u, w) ∈ rootAboveNet.edges) a c :=
      fun h h' => Relation.ReflTransGen.head h h'
    have hedge : ∀ {a b : ℕ}, (a, b) ∈ rootAboveNet.edges →
        Relation.ReflTransGen (fun u w => (u, w) ∈ rootAboveNet.edges) a b :=
      fun h => Relation.ReflTransGen.single h
    intro v hv
    change v ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset ℕ) at hv
    change Relation.ReflTransGen _ 0 v
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Relation.ReflTransGen.refl
    · exact hedge (by decide)
    · exact hstep (b := 1) (by decide) (hedge (by decide))
    · exact hedge (by decide)
    · exact hstep (b := 1) (by decide) (hstep (b := 2) (by decide) (hedge (by decide)))
    · exact hstep (b := 3) (by decide) (hedge (by decide))
    · exact hstep (b := 1) (by decide) (hedge (by decide))
  -- distinct taxa label distinct leaves
  · intro a _ b _ h
    change a + 4 = b + 4 at h
    omega
  -- level-1: there is one cycle
  · intro v w c d hc hd hcd
    exact absurd ((rootAboveNet_cycle_edges c hc).trans (rootAboveNet_cycle_edges d hd).symm) hcd

/-- The switching of `rootAboveNet` that keeps the edge from `2` into the reticulation `3`: the
tree `((A,B),C)` below the root `0`, which has one child. -/
def rootAboveSwitching : Finset (ℕ × ℕ) := {(0, 1), (1, 2), (1, 6), (2, 3), (2, 4), (3, 5)}

/-- The vertices of `((A,B),C)` in `rootAboveNet`: the root at `1`, the parent of the cherry at
`2`, and the leaves `A`, `B`, `C` at `4`, `5`, `6`. -/
def rootAboveOriginal : Address → ℕ
  | [] => 1
  | [false] => 2
  | [false, false] => 4
  | [false, true] => 5
  | _ => 6

/-- The wires of `rootAboveNet` above the vertices of `((A,B),C)`: the edge above `B` is
subdivided by the reticulation `3`. -/
def rootAboveWire : Address → List ℕ
  | [false] => [1, 2]
  | [false, false] => [2, 4]
  | [false, true] => [2, 3, 5]
  | _ => [1, 6]

/-- The vertices of `((A,B),C)`. -/
theorem cherryTree_nodes :
    cherryTree.nodes = {[], [false], [false, false], [false, true], [true]} := by decide

/-- The switching `rootAboveSwitching` is `((A,B),C)` subdivided, below the root wire `[0, 1]`. -/
def rootAboveDisplayed : DisplayedSubdivision cherryTree rootAboveNet rootAboveSwitching where
  original := rootAboveOriginal
  wire := rootAboveWire
  rootWire := [0, 1]
  original_injective := Finset.card_image_iff.mp (by decide)
  taxa_preserved := by decide
  leaves_preserved := by
    intro p hp a ha
    rw [cherryTree_nodes] at hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;>
      simp [cherryTree, PhyloTree.nodeAt] at ha <;> subst ha <;> rfl
  rootWire_laws := by decide
  wire_laws := by decide
  interiors_disjoint := by
    have h : ∀ p ∈ cherryTree.nodes.erase [], ∀ q ∈ cherryTree.nodes.erase [], p ≠ q →
        Disjoint (wireInterior (rootAboveWire p)) (wireInterior (rootAboveWire q)) := by decide
    exact fun p hp q hq hpq => h p hp q hq hpq
  rootWire_disjoint := by decide
  vertices_covered := by decide
  edges_covered := by decide
  switching := ⟨by decide, by decide⟩

/-- `rootAboveNet` is built on `((A,B),C)` in the sense of Definition 1: deleting the edge from
the root to the reticulation leaves `((A,B),C)` below a root with one child. -/
theorem rootAboveNet_builtOn : rootAboveNet.BuiltOn cherryTree :=
  ⟨rootAboveNet_levelOne, _, ⟨rootAboveDisplayed⟩⟩

/-- The vertices of a path whose edges lie in `E` lie in every set that contains its first vertex
and is closed under the edges of `E`. -/
theorem rootAbove_wire_mem_of_closed {E : Finset (ℕ × ℕ)} {R : Finset ℕ}
    (hR : ∀ e ∈ E, e.1 ∈ R → e.2 ∈ R) (L : List ℕ) {x : ℕ} (hx : L.head? = some x)
    (hxR : x ∈ R) (hE : wireEdges L ⊆ E) : ∀ v ∈ L, v ∈ R := by
  induction L generalizing x with
  | nil => intro v hv; simp at hv
  | cons a rest ih =>
    intro v hv
    simp only [List.head?_cons, Option.some.injEq] at hx
    subst hx
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hxR
    · cases rest with
      | nil => simp at hv
      | cons b rest' =>
        rw [Realization.wireEdges_cons_cons] at hE
        exact ih rfl (hR _ (hE (Finset.mem_insert_self _ _)) hxR)
          (fun e he => hE (Finset.mem_insert_of_mem he)) v hv

/-- A wire starts with its first vertex and a second one, joined by an edge of the wire. -/
theorem rootAbove_wire_cons_cons {L : List ℕ} {x : ℕ} (hlen : 2 ≤ L.length)
    (hx : L.head? = some x) :
    ∃ b rest, L = x :: b :: rest := by
  match L, hlen, hx with
  | a :: b :: rest, _, hx =>
    simp only [List.head?_cons, Option.some.injEq] at hx
    exact ⟨b, rest, by rw [hx]⟩

/-- The second vertex of a wire is its last vertex or an interior one. -/
theorem rootAbove_second_interior_or_last (x b : ℕ) (rest : List ℕ) :
    b ∈ wireInterior (x :: b :: rest) ∨ (x :: b :: rest).getLast? = some b := by
  cases rest with
  | nil => exact Or.inr rfl
  | cons c rest =>
    left
    simp [wireInterior, List.dropLast_cons_of_ne_nil]

/-- `rootAboveNet` is not built on `((A,B),C)` with the root kept. A support subdivision would put
the root of `((A,B),C)` at the root `0`; the wire above `C` must run `0 → 1 → 6`, so the wire
above the cherry `(A,B)` must leave `0` through the reticulation `3`, from which the leaf `A` is
not reachable. -/
theorem rootAboveNet_not_anchored : ¬rootAboveNet.AnchoredExtension cherryTree := by
  rintro ⟨_, S, ⟨H⟩⟩
  -- the edges of the wires are edges of `rootAboveNet`
  have hwireE : ∀ p ∈ cherryTree.nodes, p ≠ [] → wireEdges (H.wire p) ⊆ rootAboveNet.edges := by
    intro p hp hp0 e he
    apply H.switching.1
    rw [H.edges_covered]
    exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_erase.mpr ⟨hp0, hp⟩, he⟩
  -- the vertices reachable from the reticulation `3`
  have hclosed : ∀ e ∈ rootAboveNet.edges, e.1 ∈ ({3, 5} : Finset ℕ) →
      e.2 ∈ ({3, 5} : Finset ℕ) := by decide
  have hroot : H.original [] = 0 := H.root_preserved
  have hC : H.original [true] = 6 := H.leaves_preserved [true] (by decide) 2 rfl
  have hA : H.original [false, false] = 4 := H.leaves_preserved _ (by decide) 0 rfl
  -- the wire above `C` runs from `0` through `1`
  obtain ⟨hlenC, _, hheadC, hlastC, hdisC⟩ := H.wire_laws [true] (by decide) (by decide)
  rw [show parent [true] = [] from rfl, hroot] at hheadC
  obtain ⟨bC, restC, hLC⟩ := rootAbove_wire_cons_cons hlenC hheadC
  have hEC := hwireE [true] (by decide) (by decide)
  rw [hLC] at hEC hlastC hdisC
  have hbC : (0, bC) ∈ rootAboveNet.edges :=
    hEC (by rw [Realization.wireEdges_cons_cons]; exact Finset.mem_insert_self _ _)
  have hbC' : bC = 1 ∨ bC = 3 := by
    revert hbC; simp only [rootAboveNet, Finset.mem_insert, Finset.mem_singleton,
      Prod.mk.injEq]; omega
  have h1C : bC = 1 := by
    rcases hbC' with h | h
    · exact h
    · -- from `3`, the leaf `6` of `C` is not reachable
      exfalso
      rw [Realization.wireEdges_cons_cons] at hEC
      have hmem := rootAbove_wire_mem_of_closed hclosed (bC :: restC) rfl (by rw [h]; decide)
        (fun e he => hEC (Finset.mem_insert_of_mem he))
      have hlast : (bC :: restC).getLast? = some 6 := by
        rw [← hC, ← hlastC, List.getLast?_cons_cons]
      have h6 := hmem 6 (List.mem_of_getLast? hlast)
      simp at h6
  subst h1C
  -- so `1` lies inside the wire above `C`
  have h1int : 1 ∈ wireInterior (0 :: 1 :: restC) := by
    rcases rootAbove_second_interior_or_last 0 1 restC with h | h
    · exact h
    · rw [hlastC, hC] at h
      simp at h
  -- the wire above the cherry runs from `0`
  obtain ⟨hlenF, _, hheadF, hlastF, hdisF⟩ := H.wire_laws [false] (by decide) (by decide)
  rw [show parent [false] = [] from rfl, hroot] at hheadF
  obtain ⟨bF, restF, hLF⟩ := rootAbove_wire_cons_cons hlenF hheadF
  have hEF := hwireE [false] (by decide) (by decide)
  rw [hLF] at hEF hlastF hdisF
  have hbF : (0, bF) ∈ rootAboveNet.edges :=
    hEF (by rw [Realization.wireEdges_cons_cons]; exact Finset.mem_insert_self _ _)
  have hbF' : bF = 1 ∨ bF = 3 := by
    revert hbF; simp only [rootAboveNet, Finset.mem_insert, Finset.mem_singleton,
      Prod.mk.injEq]; omega
  rcases hbF' with h | h
  -- through `1`: `1` would be the parent of the cherry, or inside two wires
  · subst h
    rcases rootAbove_second_interior_or_last 0 1 restF with h | h
    · have hdis : Disjoint (wireInterior (H.wire [false])) (wireInterior (H.wire [true])) :=
        H.interiors_disjoint (show [false] ∈ (cherryTree.nodes.erase [] : Set _) by decide)
          (show [true] ∈ (cherryTree.nodes.erase [] : Set _) by decide) (by decide)
      rw [hLF, hLC] at hdis
      exact Finset.disjoint_left.mp hdis h h1int
    · rw [hlastF] at h
      have hF1 : H.original [false] = 1 := Option.some.inj h
      exact Finset.disjoint_left.mp hdisC h1int
        (Finset.mem_image.mpr ⟨[false], by decide, hF1⟩)
  -- through the reticulation `3`: the leaf `A` is not reachable
  · subst h
    rw [Realization.wireEdges_cons_cons] at hEF
    have hmemF := rootAbove_wire_mem_of_closed hclosed (3 :: restF) rfl (by decide)
      (fun e he => hEF (Finset.mem_insert_of_mem he))
    have hlastF' : (3 :: restF).getLast? = some (H.original [false]) := by
      rw [← hlastF, List.getLast?_cons_cons]
    have hα := hmemF _ (List.mem_of_getLast? hlastF')
    -- the wire above `A` starts at the parent of the cherry
    obtain ⟨hlenA, _, hheadA, hlastA, _⟩ := H.wire_laws [false, false] (by decide) (by decide)
    rw [show parent [false, false] = [false] from rfl] at hheadA
    have hmemA := rootAbove_wire_mem_of_closed hclosed (H.wire [false, false]) hheadA hα
      (hwireE [false, false] (by decide) (by decide))
    have h4 := hmemA _ (List.mem_of_getLast? hlastA)
    rw [hA] at h4
    simp at h4

/-- Definition 1's class of networks built on `T` is larger than the class of networks built on
`T` with the root kept: `rootAboveNet` is built on the well-labelled tree `((A,B),C)` in the sense
of Definition 1, and not with the root kept. -/
theorem builtOn_not_anchored :
    ∃ (t : PhyloTree) (N : RootedNetwork), t.WellLabelled ∧ N.BuiltOn t ∧ ¬N.AnchoredExtension t :=
  ⟨cherryTree, rootAboveNet, by decide, rootAboveNet_builtOn, rootAboveNet_not_anchored⟩

/-- `rootAboveNet` is not isomorphic to any network obtained from `((A,B),C)` by adding edges above
the pairs of a cycle-separated family (Definition 3). Such a network is built on `((A,B),C)` with
the root kept (`Realization.levelOne`, `Realization.support`), and so would be `rootAboveNet`
(`RootedNetwork.AnchoredExtension.of_iso`), against `rootAboveNet_not_anchored`. -/
theorem rootAboveNet_not_iso_graph (E : Finset Realization.Pair)
    (hE : EdgeAbove.CycleSeparated cherryTree E) :
    IsEmpty (rootAboveNet.Iso (Realization.graph cherryTree E)) := by
  refine ⟨fun i => rootAboveNet_not_anchored ?_⟩
  have ht : cherryTree.WellLabelled := by decide
  exact RootedNetwork.AnchoredExtension.of_iso rootAboveNet_levelOne i
    ⟨Realization.levelOne cherryTree ht E hE, _, ⟨Realization.support cherryTree ht E hE⟩⟩

open DynamicProgramming in
/-- Section 3.2: "any tree t ∈ Q(N_r) can be used as the basis for N (i.e. N can be obtained by
adding reticulate edges to t)", with `t` a displayed tree of `N` (Definition 1), fails when the root
of `N` has a reticulation child. The tree `((A,B),C)` is a tree of `rootAboveNet`
(`rootAboveNet_builtOn`), but for every multiset `Q`, every array `M` satisfying the recurrence of
Section 2.2 on `((A,B),C)` and every backtracking trace `E` from the root, the network that CAMUS
outputs, `Realization.graph cherryTree E`, is not isomorphic to `rootAboveNet`. The output is
built on `((A,B),C)` with the root kept (`theorem1`); by `RootedNetwork.BuiltOn.exists_anchored`
it can still display the quartets of `rootAboveNet` with as many reticulations. -/
theorem camus_output_not_rootAboveNet (Q : Multiset Quartet) (M : Address → ℕ)
    (hM : Array cherryTree (edgeWeight cherryTree Q) M) (E : Finset Pair)
    (trace : Trace cherryTree (edgeWeight cherryTree Q) M [] E) :
    IsEmpty (rootAboveNet.Iso (Realization.graph cherryTree E)) := by
  refine ⟨fun i => rootAboveNet_not_anchored ?_⟩
  have ht : cherryTree.WellLabelled := by decide
  exact RootedNetwork.AnchoredExtension.of_iso rootAboveNet_levelOne i
    (theorem1 cherryTree ht Q M hM E trace).1

end Counterexamples

end Camus
