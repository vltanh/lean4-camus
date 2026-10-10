module

public import Camus.Network.Cuts
public import Camus.Network.Baseline.Clades

/-!
# Displayed quartets by clades

A switching `S` of a rooted binary level-1 network `N` is a spanning tree of `N`, directed away
from the root. Deleting the edge `(x, y)` of `S` separates the taxa whose leaves lie below `y` in
`S` (`RootedNetwork.cladeBelow`) from the other taxa. So `N` displays the quartet `q`
(Definition 1) if and only if some switching `S` has an edge `(x, y)` whose clade below `y` cuts
`q`. The edge can be taken to enter a vertex that is not a reticulation: an edge into a
reticulation `y` cuts the same clade as the edge out of `y`.

## Main results

* `RootedNetwork.cladeBelow`: the clade below a vertex in a switching.
* `RootedNetwork.switching_cut_reachable_iff`: deleting the edge `(x, y)` of a switching leaves
  two components, the vertices below `y` and the others.
* `RootedNetwork.displays_iff_cladeBelow`: Definition 1 by clades.
* `RootedNetwork.displays_iff_treeEdge_cladeBelow`: the same, with an edge into a vertex of
  indegree 1.
-/

@[expose] public section

namespace Camus

namespace RootedNetwork

/-- The taxa whose leaves are reached from `y` by a directed path of edges of `S`. For a switching
`S` of `N`, this is the clade below `y` in the tree `S`: deleting the edge of `S` into `y`
separates it from the other taxa of `N`. -/
noncomputable def cladeBelow (N : RootedNetwork) (S : Finset (ℕ × ℕ)) (y : ℕ) : Finset ℕ := by
  classical
  exact N.taxa.filter fun a => Relation.ReflTransGen (fun u v => (u, v) ∈ S) y (N.leaf a)

/-- A taxon is in the clade below `y` iff it is a taxon of `N` whose leaf is reached from `y` along
edges of `S`. -/
theorem mem_cladeBelow {N : RootedNetwork} {S : Finset (ℕ × ℕ)} {y a : ℕ} :
    a ∈ N.cladeBelow S y ↔
      a ∈ N.taxa ∧ Relation.ReflTransGen (fun u v => (u, v) ∈ S) y (N.leaf a) := by
  classical
  unfold cladeBelow
  exact Finset.mem_filter

section Switching

variable {N : RootedNetwork} {S : Finset (ℕ × ℕ)}

/-- Let `(x, y)` and `(a, b)` be distinct edges of a switching `S`. Then `a` is below `y` in `S` iff
`b` is: a directed path of `S` from `y` to `b` ends with the only edge of `S` into `b`, which is
`(a, b)`, and it is not the edge `(x, y)`. -/
theorem below_iff_of_switching_edge (hN : N.RootedBinaryLevelOne) (hS : N.Switching S)
    {x y a b : ℕ} (hxy : (x, y) ∈ S) (hab : (a, b) ∈ S) (hne : (a, b) ≠ (x, y)) :
    Relation.ReflTransGen (fun u v => (u, v) ∈ S) y a ↔
      Relation.ReflTransGen (fun u v => (u, v) ∈ S) y b := by
  constructor
  · intro h
    exact h.tail hab
  · intro h
    rcases h.cases_tail with h | ⟨c, hc, hcb⟩
    · subst h
      have hax : a = x := switching_incoming_unique hN hS hab hxy
      subst hax
      exact absurd rfl hne
    · have hca := switching_incoming_unique hN hS hcb hab
      subst hca
      exact hc

/-- After deleting the edge `(x, y)` of a switching `S` from its undirected graph, two adjacent
vertices both lie below `y` in `S`, or neither does. -/
theorem switching_cut_adj_below_iff (hN : N.RootedBinaryLevelOne) (hS : N.Switching S)
    {x y a b : ℕ} (hxy : (x, y) ∈ S)
    (hadj : (({N with edges := S}).underlying.deleteEdges {s(x, y)}).Adj a b) :
    Relation.ReflTransGen (fun u v => (u, v) ∈ S) y a ↔
      Relation.ReflTransGen (fun u v => (u, v) ∈ S) y b := by
  obtain ⟨⟨_, hab | hba⟩, hcut⟩ := SimpleGraph.deleteEdges_adj.mp hadj
  · apply below_iff_of_switching_edge hN hS hxy hab
    intro h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact hcut rfl
  · apply (below_iff_of_switching_edge hN hS hxy hba _).symm
    intro h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact hcut (Sym2.eq_swap)

/-- Deleting the edge `(x, y)` of a switching `S` of a rooted binary level-1 network `N` from the
undirected graph of `S` leaves two components: the vertices below `y` in `S`, and the others. Two
vertices of `N` are connected after the deletion iff both or neither lie below `y`. The vertices
below `y` are joined to `y` by their directed paths from `y`, which do not use `(x, y)` since `N`
is acyclic; the others are joined to the root by their directed paths from the root, which do not
pass through `y`. -/
theorem switching_cut_reachable_iff (hN : N.RootedBinaryLevelOne) (hS : N.Switching S)
    {x y : ℕ} (hxy : (x, y) ∈ S) {a b : ℕ} (ha : a ∈ N.vertices) (hb : b ∈ N.vertices) :
    (({N with edges := S}).underlying.deleteEdges {s(x, y)}).Reachable a b ↔
      (Relation.ReflTransGen (fun u v => (u, v) ∈ S) y a ↔
        Relation.ReflTransGen (fun u v => (u, v) ∈ S) y b) := by
  let G := ({N with edges := S}).underlying.deleteEdges {s(x, y)}
  -- an edge of `S` other than `(x, y)` is an edge of `G`
  have hedge {c d : ℕ} (hcd : (c, d) ∈ S) (hne : (c, d) ≠ (x, y)) : G.Adj c d := by
    refine SimpleGraph.deleteEdges_adj.mpr ⟨⟨edge_ne hN (hS.1 hcd), Or.inl hcd⟩, ?_⟩
    intro hmem
    exact hne (directed_edge_eq_of_sym2_eq hN (hS.1 hcd) (hS.1 hxy)
      (Set.mem_singleton_iff.mp hmem))
  -- the vertices below `y` are connected to `y`
  have hinside {c : ℕ} (hc : Relation.ReflTransGen (fun u v => (u, v) ∈ S) y c) :
      G.Reachable y c := by
    induction hc with
    | refl => exact .refl _
    | @tail c d hyc hcd ih =>
      refine ih.trans (hedge hcd ?_).reachable
      intro h
      have hc : c = x := (Prod.mk.inj h).1
      have hpath := Relation.ReflTransGen.mono (fun u v huv => hS.1 huv) _ _ hyc
      rw [hc] at hpath
      exact hN.2.2.1 y (Relation.TransGen.tail' hpath (hS.1 hxy))
  -- the other vertices are connected to the root
  have houtside {c : ℕ} (hc : Relation.ReflTransGen (fun u v => (u, v) ∈ S) N.root c) :
      ¬Relation.ReflTransGen (fun u v => (u, v) ∈ S) y c → G.Reachable N.root c := by
    induction hc with
    | refl => exact fun _ => .refl _
    | @tail c d _ hcd ih =>
      intro hyd
      have hyc : ¬Relation.ReflTransGen (fun u v => (u, v) ∈ S) y c :=
        fun h => hyd (h.tail hcd)
      refine (ih hyc).trans (hedge hcd ?_).reachable
      intro h
      have hd : d = y := (Prod.mk.inj h).2
      exact hyd (hd ▸ .refl)
  constructor
  · rintro ⟨walk⟩
    clear ha hb
    induction walk with
    | nil => exact Iff.rfl
    | cons hadj _ ih => exact (switching_cut_adj_below_iff hN hS hxy hadj).trans ih
  · intro hab
    by_cases hya : Relation.ReflTransGen (fun u v => (u, v) ∈ S) y a
    · exact (hinside hya).symm.trans (hinside (hab.mp hya))
    · have hyb : ¬Relation.ReflTransGen (fun u v => (u, v) ∈ S) y b := fun h => hya (hab.mpr h)
      exact (houtside (switching_reachable hN hS ha) hya).symm.trans
        (houtside (switching_reachable hN hS hb) hyb)

/-- Deleting the edge `(x, y)` of a switching `S` separates the two sides of the quartet `q`, whose
taxa are taxa of `N`, iff the clade below `y` in `S` cuts `q`. -/
theorem switching_cut_separates_iff (hN : N.RootedBinaryLevelOne) (hS : N.Switching S)
    {x y : ℕ} (hxy : (x, y) ∈ S) (q : Quartet) (hq : q.taxa ⊆ N.taxa) :
    N.Separates (({N with edges := S}).underlying.deleteEdges {s(x, y)}) q ↔
      q.cutBy (N.cladeBelow S y) = true := by
  have hleaf (a : ℕ) (ha : a ∈ N.taxa) : N.leaf a ∈ N.vertices :=
    (hN.2.2.2.2.2.2.2.1 a ha).1
  have reach (a b : ℕ) (ha : a ∈ N.taxa) (hb : b ∈ N.taxa) :
      (({N with edges := S}).underlying.deleteEdges {s(x, y)}).Reachable (N.leaf a)
          (N.leaf b) ↔
        (a ∈ N.cladeBelow S y ↔ b ∈ N.cladeBelow S y) := by
    rw [switching_cut_reachable_iff hN hS hxy (hleaf a ha) (hleaf b hb), mem_cladeBelow,
      mem_cladeBelow]
    simp only [ha, hb, true_and]
  have hfirst (a : ℕ) (ha : a ∈ q.sides.1) : a ∈ N.taxa := hq (q.sides_subset_taxa.1 ha)
  have hsecond (a : ℕ) (ha : a ∈ q.sides.2) : a ∈ N.taxa := hq (q.sides_subset_taxa.2 ha)
  have hbool : q.cutBy (N.cladeBelow S y) = true ↔
      ((∀ a ∈ q.sides.1, a ∈ N.cladeBelow S y) ∧
          (∀ b ∈ q.sides.2, b ∉ N.cladeBelow S y) ∨
        (∀ a ∈ q.sides.1, a ∉ N.cladeBelow S y) ∧
          (∀ b ∈ q.sides.2, b ∈ N.cladeBelow S y)) := by
    simp only [Quartet.cutBy, decide_eq_true_eq, Finset.subset_iff, Finset.disjoint_left]
    tauto
  rw [hbool, ← Realization.side_partition_iff q.sides_nonempty.1 q.sides_nonempty.2
    (· ∈ N.cladeBelow S y)]
  constructor
  · rintro ⟨hAA, hBB, hAB⟩
    exact ⟨fun a ha b hb => (reach a b (hfirst a ha) (hfirst b hb)).mp (hAA a ha b hb),
      fun a ha b hb => (reach a b (hsecond a ha) (hsecond b hb)).mp (hBB a ha b hb),
      fun a ha b hb h => hAB a ha b hb ((reach a b (hfirst a ha) (hsecond b hb)).mpr h)⟩
  · rintro ⟨hAA, hBB, hAB⟩
    exact ⟨fun a ha b hb => (reach a b (hfirst a ha) (hfirst b hb)).mpr (hAA a ha b hb),
      fun a ha b hb => (reach a b (hsecond a ha) (hsecond b hb)).mpr (hBB a ha b hb),
      fun a ha b hb h => hAB a ha b hb ((reach a b (hfirst a ha) (hsecond b hb)).mp h)⟩

end Switching

/-- Definition 1 by clades: a rooted binary level-1 network `N` displays the quartet `q` if and
only if the taxa of `q` are taxa of `N` and, for some switching `S` of `N` and some edge `(x, y)`
of `S`, the clade below `y` in `S` cuts `q`. -/
theorem displays_iff_cladeBelow {N : RootedNetwork} (hN : N.RootedBinaryLevelOne)
    (q : Quartet) :
    N.DisplaysQuartet q ↔ q.taxa ⊆ N.taxa ∧
      ∃ S, N.Switching S ∧ ∃ x y, (x, y) ∈ S ∧ q.cutBy (N.cladeBelow S y) = true := by
  constructor
  · rintro ⟨hq, S, hS, edge, hedge, hsep⟩
    refine ⟨hq, S, hS, ?_⟩
    induction edge using Sym2.inductionOn with
    | _ a b =>
      rcases hedge.2 with hab | hba
      · exact ⟨a, b, hab, (switching_cut_separates_iff hN hS hab q hq).mp hsep⟩
      · refine ⟨b, a, hba, (switching_cut_separates_iff hN hS hba q hq).mp ?_⟩
        rwa [Sym2.eq_swap]
  · rintro ⟨hq, S, hS, x, y, hxy, hcut⟩
    exact ⟨hq, S, hS, s(x, y), ⟨edge_ne hN (hS.1 hxy), Or.inl hxy⟩,
      (switching_cut_separates_iff hN hS hxy q hq).mpr hcut⟩

/-- Definition 1 by clades of tree edges: as `displays_iff_cladeBelow`, with the edge `(x, y)`
entering a vertex `y` of indegree 1 (a tree vertex or a leaf), not a reticulation. -/
theorem displays_iff_treeEdge_cladeBelow {N : RootedNetwork} (hN : N.RootedBinaryLevelOne)
    (q : Quartet) :
    N.DisplaysQuartet q ↔ q.taxa ⊆ N.taxa ∧
      ∃ S, N.Switching S ∧ ∃ x y, (x, y) ∈ S ∧ N.indegree y = 1 ∧
        q.cutBy (N.cladeBelow S y) = true := by
  rw [displays_iff_cladeBelow hN q]
  constructor
  · rintro ⟨hq, S, hS, x, y, hxy, hcut⟩
    refine ⟨hq, S, hS, ?_⟩
    -- Descend from `y` along the edges of `S` out of reticulations, which keep the clade, until a
    -- vertex of indegree 1. The number of strict ancestors of the vertex increases at each step.
    suffices h : ∀ n, ∀ x y, (x, y) ∈ S → N.vertices.card - N.dagRank y = n →
        q.cutBy (N.cladeBelow S y) = true →
        ∃ x y, (x, y) ∈ S ∧ N.indegree y = 1 ∧ q.cutBy (N.cladeBelow S y) = true from
      h _ x y hxy rfl hcut
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro x y hxy hn hcut
      have hyN : y ∈ N.vertices := (hN.2.1 _ (hS.1 hxy)).2
      have hyr : y ≠ N.root := by
        intro h
        have hpos : 0 < N.indegree N.root :=
          Finset.card_pos.mpr ⟨(x, y), Finset.mem_filter.mpr ⟨hS.1 hxy, h⟩⟩
        rw [hN.2.2.2.1] at hpos
        omega
      rcases hN.2.2.2.2.2.2.2.2.2.1 y hyN hyr with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨_, hout⟩
      · exact ⟨x, y, hxy, h1, hcut⟩
      · exact ⟨x, y, hxy, h1, hcut⟩
      · -- `y` is a reticulation, with one edge `(y, z)` out of it
        have hleaf_ne (a : ℕ) (ha : a ∈ N.taxa) : N.leaf a ≠ y := by
          intro h
          have h0 := (hN.2.2.2.2.2.2.2.1 a ha).2.2
          rw [h, hout] at h0
          omega
        have hout_unique {z z' : ℕ} (hz : (y, z) ∈ N.edges) (hz' : (y, z') ∈ N.edges) :
            z = z' := by
          have hcard : (N.edges.filter (fun e => e.1 = y)).card ≤ 1 := by
            change N.outdegree y ≤ 1
            omega
          have := Finset.card_le_one.mp hcard (y, z) (Finset.mem_filter.mpr ⟨hz, rfl⟩)
            (y, z') (Finset.mem_filter.mpr ⟨hz', rfl⟩)
          exact (Prod.mk.inj this).2
        -- the clade below `y` is nonempty: it contains a side of `q`
        obtain ⟨a, ha⟩ : (N.cladeBelow S y).Nonempty := by
          by_contra hempty
          rw [Finset.not_nonempty_iff_eq_empty] at hempty
          rw [hempty] at hcut
          simp only [Quartet.cutBy, Finset.subset_empty, Finset.disjoint_empty_right,
            and_true, decide_eq_true_eq] at hcut
          rcases hcut with h | h
          · exact (Finset.nonempty_iff_ne_empty.mp q.sides_nonempty.1) h
          · exact (Finset.nonempty_iff_ne_empty.mp q.sides_nonempty.2) h
        obtain ⟨haN, hya⟩ := mem_cladeBelow.mp ha
        rcases hya.cases_head with h | ⟨z, hyz, _⟩
        · exact absurd h.symm (hleaf_ne a haN)
        · -- the edge `(y, z)` of `S` has the same clade below its head
          have hclade : N.cladeBelow S z = N.cladeBelow S y := by
            ext b
            rw [mem_cladeBelow, mem_cladeBelow]
            constructor
            · rintro ⟨hb, hzb⟩
              exact ⟨hb, Relation.ReflTransGen.head hyz hzb⟩
            · rintro ⟨hb, hyb⟩
              refine ⟨hb, ?_⟩
              rcases hyb.cases_head with h | ⟨z', hyz', hz'b⟩
              · exact absurd h.symm (hleaf_ne b hb)
              · rwa [hout_unique (hS.1 hyz) (hS.1 hyz')]
          have hlt : N.dagRank y < N.dagRank z := dagRank_lt hN (hS.1 hyz)
          have hle : N.dagRank z ≤ N.vertices.card := by
            classical
            unfold dagRank
            exact Finset.card_filter_le _ _
          exact ih _ (by omega) y z hyz rfl (hclade ▸ hcut)
  · rintro ⟨hq, S, hS, x, y, hxy, _, hcut⟩
    exact ⟨hq, S, hS, x, y, hxy, hcut⟩

end RootedNetwork

end Camus
