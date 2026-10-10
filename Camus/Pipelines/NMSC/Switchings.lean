module

public import Camus.Pipelines.NMSC.Trees

/-!
# The trees of a network by the clades below the vertices of its switchings

Definition 1 builds the trees 𝒯 of a rooted binary level-1 network `N` from its switchings: delete
one of the two edges into each reticulation, in each of the possible ways, and clean up. This file
describes the clades of the tree of a switching `S` without the clean-up: they are the sets of taxa
below the vertices of `N` in `S` (`DisplayedSubdivision.clades_toFinset_eq`). So the trees of `N`,
as families of clades, are the families `N.vertices.image (N.cladeBelow S)` over the switchings
`S` of `N` (`RootedNetwork.exists_builtOn_clades`, `RootedNetwork.BuiltOn.exists_switching_clades`).
For the graph of a network `N` of the NMSC, this reduces the comparison of its trees with the
displayed trees of `N` (`Brooqs.Net.displayed`) to the clades below the vertices of its switchings
(`NMSC.exists_builtOn_of_switching_clades`), and gives the recovery of Section 3.2 through the tree
of every switching (`NMSC.nmsc_recovery_switching`).

The switchings of `N` differ by the edge kept into each reticulation. Exchanging the edge `g` of a
switching `S` into a vertex for the other edge `d` into it gives a switching
(`RootedNetwork.Switching.exchange`), whose clades are those of `S` with the clade below `d.2` moved
from below the tail of `g` to below the tail of `d`, a subtree prune and regraft
(`RootedNetwork.cladeBelow_exchange`, `RootedNetwork.cladeBelow_exchange_below`).

## Main results

* `DisplayedSubdivision.clades_toFinset_eq`: the clades of the tree of a switching are the clades
  below the vertices.
* `RootedNetwork.exists_builtOn_clades`, `RootedNetwork.BuiltOn.exists_switching_clades`: the
  trees of `N` in the sense of Definition 1, by their clades, are those of its switchings.
* `RootedNetwork.Switching.exchange`, `RootedNetwork.cladeBelow_exchange`,
  `RootedNetwork.cladeBelow_exchange_below`: exchanging the edge kept into a reticulation moves the
  clade below it.
* `NMSC.exists_builtOn_of_switching_clades`: a displayed tree of `N` is the family of clades of a
  tree of the graph of `N` as soon as it is the family of clades below the vertices of a switching.
* `NMSC.nmsc_recovery_switching`: Sections 3.2 to 3.4 under the NMSC through the tree of every
  switching of the graph of `N`, with an outgroup.
-/

@[expose] public section

namespace Camus

namespace DisplayedSubdivision

variable {t : PhyloTree} {N : RootedNetwork} {S : Finset (ℕ × ℕ)}

/-- The clades of the tree `t` of a switching `S` of `N` are the sets of taxa below the vertices of
`N` in `S`: below the image of a vertex `p` of `t` and below the interior vertices of the wire above
it lie the taxa of the clade of `p` (`DisplayedSubdivision.cladeBelow_original`,
`DisplayedSubdivision.cladeBelow_interior`), and below the vertices of the root wire all the taxa
(`DisplayedSubdivision.cladeBelow_rootWire`). -/
theorem clades_toFinset_eq (H : DisplayedSubdivision t N S) :
    t.clades.toFinset = N.vertices.image (N.cladeBelow S) := by
  have ht := H.wellLabelled
  have hroot : [] ∈ t.nodes := t.root_mem_nodes
  ext C
  simp only [List.mem_toFinset, Finset.mem_image]
  constructor
  · intro hC
    obtain ⟨p, hp, rfl⟩ := NMSC.exists_of_mem_clades hC
    refine ⟨H.original p, ?_, H.cladeBelow_original ht hp⟩
    rw [H.vertices_covered]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp))
  · rintro ⟨v, hv, rfl⟩
    rw [H.vertices_covered] at hv
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_biUnion, Finset.mem_erase] at hv
    rcases hv with (⟨p, hp, rfl⟩ | ⟨p, ⟨hp0, hp⟩, hv⟩) | hv
    · rw [H.cladeBelow_original ht hp]
      exact NMSC.taxaAt_mem_clades hp
    · rw [H.cladeBelow_interior ht hp hp0 hv]
      exact NMSC.taxaAt_mem_clades hp
    · rw [H.cladeBelow_rootWire (List.dropLast_subset _ (List.mem_toFinset.1 hv)),
        H.taxa_preserved, ← PhyloTree.taxaAt_nil]
      exact NMSC.taxaAt_mem_clades hroot

end DisplayedSubdivision

namespace RootedNetwork

variable {N : RootedNetwork}

/-- Definition 1 by the clades below the vertices: every switching `S` of a rooted binary level-1
network `N` gives a tree on which `N` is built, whose clades are the sets of taxa below the vertices
of `N` in `S`. -/
theorem exists_builtOn_clades (hN : N.RootedBinaryLevelOne) {S : Finset (ℕ × ℕ)}
    (hS : N.Switching S) :
    ∃ t : PhyloTree, N.BuiltOn t ∧ t.clades.toFinset = N.vertices.image (N.cladeBelow S) := by
  obtain ⟨t, -, -, hb, ⟨H⟩⟩ := builtOn_of_switching hN hS
  exact ⟨t, hb, H.clades_toFinset_eq⟩

/-- Every tree on which `N` is built, in the sense of Definition 1, is the tree of a switching `S`,
and its clades are the sets of taxa below the vertices of `N` in `S`. -/
theorem BuiltOn.exists_switching_clades {t : PhyloTree} (h : N.BuiltOn t) :
    ∃ S, N.Switching S ∧ t.clades.toFinset = N.vertices.image (N.cladeBelow S) := by
  obtain ⟨-, S, ⟨H⟩⟩ := h
  exact ⟨S, H.switching, H.clades_toFinset_eq⟩

/-! ### Exchanging the edge into a reticulation -/

/-- Exchanging the edge of a switching into a vertex for the other edge of `N` into it gives a
switching. -/
theorem Switching.exchange {S : Finset (ℕ × ℕ)} (hS : N.Switching S) {g d : ℕ × ℕ}
    (hg : g ∈ S) (hd : d ∈ N.edges \ S) (hgd : g.2 = d.2) :
    N.Switching (insert d (S.erase g)) := by
  classical
  have hdS : d ∉ S := (Finset.mem_sdiff.1 hd).2
  refine ⟨Finset.insert_subset (Finset.mem_sdiff.1 hd).1
    ((Finset.erase_subset _ _).trans hS.1), fun v hv hvr => ?_⟩
  rw [Finset.filter_insert, Finset.filter_erase]
  by_cases hdv : d.2 = v
  · have hgv : g.2 = v := hgd.trans hdv
    simp only [hdv, ↓reduceIte]
    have hnot : d ∉ (S.filter fun e => e.2 = v).erase g := fun h =>
      hdS (Finset.mem_filter.1 (Finset.mem_of_mem_erase h)).1
    rw [Finset.card_insert_of_notMem hnot,
      Finset.card_erase_of_mem (Finset.mem_filter.2 ⟨hg, hgv⟩), hS.2 v hv hvr]
  · simp only [hdv, ↓reduceIte]
    have hnot : g ∉ S.filter fun e => e.2 = v := fun h =>
      hdv (hgd.symm.trans (Finset.mem_filter.1 h).2)
    rw [Finset.erase_eq_of_notMem hnot]
    exact hS.2 v hv hvr

/-- A directed path of `S ⊆ N.edges` followed by an edge of `N` back to its start would be a
directed cycle of `N`. -/
theorem false_of_reach_of_edge (hN : N.RootedBinaryLevelOne) {S : Finset (ℕ × ℕ)}
    (hSN : S ⊆ N.edges) {a b : ℕ} (hab : Relation.ReflTransGen (fun u v => (u, v) ∈ S) a b)
    (hba : (b, a) ∈ N.edges) : False :=
  hN.2.2.1 a (Relation.TransGen.tail'
    (Relation.ReflTransGen.mono (r := fun u v => (u, v) ∈ S) (p := fun u v => (u, v) ∈ N.edges)
      (fun _ _ h => hSN h) a b hab) hba)

/-- In a switching, the edge into a vertex is unique. -/
theorem Switching.eq_of_edge (hN : N.RootedBinaryLevelOne) {S : Finset (ℕ × ℕ)}
    (hS : N.Switching S) {y z x : ℕ} (hy : (y, x) ∈ S) (hz : (z, x) ∈ S) : y = z := by
  classical
  have hxV : x ∈ N.vertices := (hN.2.1 _ (hS.1 hy)).2
  have hxr : x ≠ N.root := by
    intro h
    have h0 := hN.2.2.2.1
    have hpos : 0 < N.indegree N.root :=
      Finset.card_pos.2 ⟨(y, x), Finset.mem_filter.2 ⟨hS.1 hy, h⟩⟩
    omega
  have h1 := Finset.card_le_one.1 (hS.2 x hxV hxr).le (y, x) (Finset.mem_filter.2 ⟨hy, rfl⟩)
    (z, x) (Finset.mem_filter.2 ⟨hz, rfl⟩)
  exact congrArg Prod.fst h1

/-- In a switching, the vertices from which a vertex `x` is reached form a chain: two of them are
reached one from the other. -/
theorem Switching.reach_total (hN : N.RootedBinaryLevelOne) {S : Finset (ℕ × ℕ)}
    (hS : N.Switching S) {v w x : ℕ} (hv : Relation.ReflTransGen (fun u v => (u, v) ∈ S) v x)
    (hw : Relation.ReflTransGen (fun u v => (u, v) ∈ S) w x) :
    Relation.ReflTransGen (fun u v => (u, v) ∈ S) v w ∨
      Relation.ReflTransGen (fun u v => (u, v) ∈ S) w v := by
  induction hv with
  | refl => exact Or.inr hw
  | @tail y x hvy hyx ih =>
    rcases hw.cases_tail with rfl | ⟨z, hwz, hzx⟩
    · exact Or.inl (hvy.tail hyx)
    · obtain rfl := hS.eq_of_edge hN hzx hyx
      exact ih hwz

variable {S : Finset (ℕ × ℕ)} {g d : ℕ × ℕ}

/-- After the exchange of `g` for `d`, the vertices reached from the common head `d.2` are those
reached before: a path from `d.2` never uses an edge into `d.2`. -/
theorem reach_exchange_head (hgd : g.2 = d.2) {x : ℕ} :
    Relation.ReflTransGen (fun u v => (u, v) ∈ insert d (S.erase g)) d.2 x ↔
      Relation.ReflTransGen (fun u v => (u, v) ∈ S) d.2 x := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | @tail y x _ hyx ih =>
      rcases Finset.mem_insert.1 hyx with h | h
      · obtain rfl : x = d.2 := congrArg Prod.snd h
        exact .refl
      · exact ih.tail (Finset.mem_of_mem_erase h)
  · intro h
    induction h with
    | refl => exact .refl
    | @tail y x _ hyx ih =>
      by_cases hg' : (y, x) = g
      · obtain rfl : x = d.2 := (congrArg Prod.snd hg').trans hgd
        exact .refl
      · exact ih.tail (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hg', hyx⟩))

/-- After the exchange of `g` for `d`, a vertex not reached from `d.2` is reached from `v` iff it
was before: a path to it uses neither edge into `d.2`. -/
theorem reach_exchange_outside (hgd : g.2 = d.2) {v x : ℕ}
    (hx : ¬Relation.ReflTransGen (fun u v => (u, v) ∈ S) d.2 x) :
    Relation.ReflTransGen (fun u v => (u, v) ∈ insert d (S.erase g)) v x ↔
      Relation.ReflTransGen (fun u v => (u, v) ∈ S) v x := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | @tail y x _ hyx ih =>
      rcases Finset.mem_insert.1 hyx with h | h
      · obtain rfl : x = d.2 := congrArg Prod.snd h
        exact absurd .refl hx
      · have hyS := Finset.mem_of_mem_erase h
        exact (ih fun hy => hx (hy.tail hyS)).tail hyS
  · intro h
    induction h with
    | refl => exact .refl
    | @tail y x _ hyx ih =>
      by_cases hg' : (y, x) = g
      · obtain rfl : x = d.2 := (congrArg Prod.snd hg').trans hgd
        exact absurd .refl hx
      · exact (ih fun hy => hx (hy.tail hyx)).tail
          (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hg', hyx⟩))

/-- In a switching `S`, a vertex `v` not below the head `r` of the edge `g ∈ S` reaches a vertex
below `r` iff it reaches the tail of `g`. -/
theorem Switching.reach_below_iff (hN : N.RootedBinaryLevelOne) (hS : N.Switching S)
    (hg : g ∈ S) {v x : ℕ} (hv : ¬Relation.ReflTransGen (fun u v => (u, v) ∈ S) g.2 v)
    (hx : Relation.ReflTransGen (fun u v => (u, v) ∈ S) g.2 x) :
    Relation.ReflTransGen (fun u v => (u, v) ∈ S) v x ↔
      Relation.ReflTransGen (fun u v => (u, v) ∈ S) v g.1 := by
  constructor
  · intro h
    rcases hS.reach_total hN h hx with h' | h'
    · rcases h'.cases_tail with h'' | ⟨z, hvz, hzr⟩
      · exact absurd (h'' ▸ .refl) hv
      · obtain rfl := hS.eq_of_edge hN hzr hg
        exact hvz
    · exact absurd h' hv
  · intro h
    exact (h.tail hg).trans hx

open Classical in
/-- **Exchanging the edge into a vertex moves the clade below it.** Let `S` be a switching of `N`,
and `g ∈ S` and `d ∈ N.edges \ S` two edges into the vertex `d.2`. In the switching with `d` in
place of `g`, the clade below a vertex `v` that is not below `d.2` loses the taxa below `d.2`, and
gains them back iff `v` reaches the tail `d.1` of `d`: the part of `S` below `d.2` is moved from
below `g.1` to below `d.1`. -/
theorem cladeBelow_exchange (hN : N.RootedBinaryLevelOne) (hS : N.Switching S) (hg : g ∈ S)
    (hd : d ∈ N.edges \ S) (hgd : g.2 = d.2) {v : ℕ}
    (hv : ¬Relation.ReflTransGen (fun u v => (u, v) ∈ S) d.2 v) :
    N.cladeBelow (insert d (S.erase g)) v =
      (N.cladeBelow S v \ N.cladeBelow S d.2) ∪
        (if Relation.ReflTransGen (fun u v => (u, v) ∈ S) v d.1 then N.cladeBelow S d.2
          else ∅) := by
  have hS' := hS.exchange hg hd hgd
  have hdN : (d.1, d.2) ∈ N.edges := by rw [Prod.mk.eta]; exact (Finset.mem_sdiff.1 hd).1
  have hd' : d ∈ insert d (S.erase g) := Finset.mem_insert_self _ _
  -- the tail of `d` is not below its head
  have hd1 : ¬Relation.ReflTransGen (fun u v => (u, v) ∈ S) d.2 d.1 := fun h =>
    false_of_reach_of_edge hN hS.1 h hdN
  -- `v` is not below `d.2` after the exchange either
  have hv' : ¬Relation.ReflTransGen (fun u v => (u, v) ∈ insert d (S.erase g)) d.2 v :=
    fun h => hv ((reach_exchange_head hgd).1 h)
  ext a
  by_cases ha : Relation.ReflTransGen (fun u v => (u, v) ∈ S) d.2 (N.leaf a)
  -- a taxon below `d.2` is below `v` iff `v` reaches the tail of `d`
  · have ha' : Relation.ReflTransGen (fun u v => (u, v) ∈ insert d (S.erase g)) d.2
        (N.leaf a) := (reach_exchange_head hgd).2 ha
    have hiff := (hS'.reach_below_iff hN hd' hv' ha').trans (reach_exchange_outside hgd hd1)
    split_ifs with h
    · simp only [RootedNetwork.mem_cladeBelow, Finset.mem_union, Finset.mem_sdiff, hiff]
      tauto
    · simp only [RootedNetwork.mem_cladeBelow, Finset.mem_union, Finset.mem_sdiff,
        Finset.notMem_empty, or_false, hiff]
      tauto
  -- a taxon not below `d.2` is below `v` iff it was
  · have hiff := reach_exchange_outside (S := S) (v := v) hgd ha
    split_ifs with h
    · simp only [RootedNetwork.mem_cladeBelow, Finset.mem_union, Finset.mem_sdiff, hiff]
      tauto
    · simp only [RootedNetwork.mem_cladeBelow, Finset.mem_union, Finset.mem_sdiff,
        Finset.notMem_empty, or_false, hiff]
      tauto

/-- Exchanging the edge into a vertex does not change the clades below the vertices below it. -/
theorem cladeBelow_exchange_below (hN : N.RootedBinaryLevelOne) (hS : N.Switching S) (hg : g ∈ S)
    (hd : d ∈ N.edges \ S) (hgd : g.2 = d.2) {v : ℕ}
    (hv : Relation.ReflTransGen (fun u v => (u, v) ∈ S) d.2 v) :
    N.cladeBelow (insert d (S.erase g)) v = N.cladeBelow S v := by
  have hS' := hS.exchange hg hd hgd
  have hdN : (d.1, d.2) ∈ N.edges := by rw [Prod.mk.eta]; exact (Finset.mem_sdiff.1 hd).1
  have hgN : (g.1, g.2) ∈ N.edges := by rw [Prod.mk.eta]; exact hS.1 hg
  have hv' := (reach_exchange_head hgd).2 hv
  -- a path from `v` does not use `d`, which would close a cycle through `d.2`
  have h₁ : ∀ {x : ℕ}, Relation.ReflTransGen (fun u v => (u, v) ∈ insert d (S.erase g)) v x →
      Relation.ReflTransGen (fun u v => (u, v) ∈ S) v x := by
    intro x h
    induction h with
    | refl => exact .refl
    | @tail y x hvy hyx ih =>
      rcases Finset.mem_insert.1 hyx with h | h
      · have hy : y = d.1 := congrArg Prod.fst h
        exact absurd (false_of_reach_of_edge hN hS'.1 (hv'.trans (hy ▸ hvy)) hdN) id
      · exact ih.tail (Finset.mem_of_mem_erase h)
  -- nor `g`
  have h₂ : ∀ {x : ℕ}, Relation.ReflTransGen (fun u v => (u, v) ∈ S) v x →
      Relation.ReflTransGen (fun u v => (u, v) ∈ insert d (S.erase g)) v x := by
    intro x h
    induction h with
    | refl => exact .refl
    | @tail y x hvy hyx ih =>
      by_cases hg' : (y, x) = g
      · have hy : y = g.1 := congrArg Prod.fst hg'
        exact absurd (false_of_reach_of_edge hN hS.1 (hgd ▸ hv.trans (hy ▸ hvy)) hgN) id
      · exact ih.tail (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hg', hyx⟩))
  ext a
  simp only [RootedNetwork.mem_cladeBelow]
  exact and_congr_right fun _ => ⟨h₁, h₂⟩

end RootedNetwork

namespace NMSC

open Finset Filter Topology MeasureTheory ProbabilityTheory Coalescent Algorithm1

variable {L : Finset ℕ}

/-- A displayed tree `K` of `N` is the family of clades of a tree of the graph
`Realization.graph (baseTree N) (pairs N)` of `N`, in the sense of Definition 1, as soon as some
switching of the graph has the clusters of `K` as its clades below the vertices. -/
theorem exists_builtOn_of_switching_clades {N : Brooqs.Net L} (hN : N.WellFormed)
    {K : Finset (Finset L)} {S : Finset (ℕ × ℕ)}
    (hS : (Realization.graph (baseTree N) (pairs N)).Switching S)
    (hK : (Realization.graph (baseTree N) (pairs N)).vertices.image
        ((Realization.graph (baseTree N) (pairs N)).cladeBelow S) =
      K.image (Finset.map (Coalescent.label L))) :
    ∃ T : PhyloTree, (Realization.graph (baseTree N) (pairs N)).BuiltOn T ∧
      T.clades.toFinset = K.image (Finset.map (Coalescent.label L)) := by
  obtain ⟨T, hT, hc⟩ := RootedNetwork.exists_builtOn_clades (graph_anchoredExtension hN).1 hS
  exact ⟨T, hT, hc.trans hK⟩

section Genes

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  [MeasurableSpace (Finset (Finset L))] [MeasurableSingletonClass (Finset (Finset L))]

open DynamicProgramming in
/-- **Sections 3.2 to 3.4 under the NMSC, through the tree of every switching.** Under the
hypotheses of `NMSC.nmsc_recovery_builtOn` (an outgroup leaf `z` child of the root of the graph
`Nr = Realization.graph (baseTree N) (pairs N)` of `N`), every switching `S` of `Nr` gives a tree
`T` of `Nr` (Definition 1) whose clades are the sets of taxa below the vertices of `Nr` in `S`, and
if `Nr` is identifiable under inclusion among the networks built on `T`, then almost surely, for
all large numbers `n` of genes, every network built on `T` with the best score for the output `Q` of
Quartet Filtering, with the fewest reticulations among them, is isomorphic to `Nr`. -/
theorem nmsc_recovery_switching {N : Brooqs.Net L} (hN : N.WellFormed)
    (htaxa : ∀ x : L, x ∈ N.taxa) (hna : NoAnomaly N) (G : ℕ → Ω → Finset (Finset L))
    (hind : iIndepFun G P) (hid : ∀ n, IdentDistrib (G n) (G 0) P P)
    (hlaw : ∀ T, P.real (G 0 ⁻¹' {T}) = N.geneTreeDist id T) {t : ℝ} (ht : 0 < t)
    (ht₀ : t < threshold N) {z : ℕ} (hz : z ∈ (Realization.graph (baseTree N) (pairs N)).taxa)
    (hzr : ((Realization.graph (baseTree N) (pairs N)).root,
        (Realization.graph (baseTree N) (pairs N)).leaf z) ∈
      (Realization.graph (baseTree N) (pairs N)).edges)
    {S : Finset (ℕ × ℕ)} (hS : (Realization.graph (baseTree N) (pairs N)).Switching S) :
    ∃ T : PhyloTree, (Realization.graph (baseTree N) (pairs N)).BuiltOn T ∧
      T.clades.toFinset = (Realization.graph (baseTree N) (pairs N)).vertices.image
        ((Realization.graph (baseTree N) (pairs N)).cladeBelow S) ∧
      ((∀ R : RootedNetwork, R.AnchoredExtension T →
        (∀ q, (Realization.graph (baseTree N) (pairs N)).DisplaysQuartet q →
          R.DisplaysQuartet q) →
        R.reticulationCount ≤ (Realization.graph (baseTree N) (pairs N)).reticulationCount →
        Nonempty (R.Iso (Realization.graph (baseTree N) (pairs N)))) →
      ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ R : RootedNetwork, R.AnchoredExtension T →
        (∀ R' : RootedNetwork, R'.AnchoredExtension T →
          score (filterQuartets t (geneQuartets (fun i => G i ω) n))
              (repertoire (filterQuartets t (geneQuartets (fun i => G i ω) n)) R') ≤
            score (filterQuartets t (geneQuartets (fun i => G i ω) n))
              (repertoire (filterQuartets t (geneQuartets (fun i => G i ω) n)) R)) →
        (∀ R' : RootedNetwork, R'.AnchoredExtension T →
          (∀ R'' : RootedNetwork, R''.AnchoredExtension T →
            score (filterQuartets t (geneQuartets (fun i => G i ω) n))
                (repertoire (filterQuartets t (geneQuartets (fun i => G i ω) n)) R'') ≤
              score (filterQuartets t (geneQuartets (fun i => G i ω) n))
                (repertoire (filterQuartets t (geneQuartets (fun i => G i ω) n)) R')) →
          R.reticulationCount ≤ R'.reticulationCount) →
        Nonempty (R.Iso (Realization.graph (baseTree N) (pairs N)))) := by
  -- the tree of the switching, on which the graph is built (Definition 1)
  obtain ⟨T, hT, hc⟩ := RootedNetwork.exists_builtOn_clades (graph_anchoredExtension hN).1 hS
  -- and the recovery through it
  exact ⟨T, hT, hc, fun identifiable => nmsc_recovery_builtOn hN htaxa hna G hind hid hlaw ht
    ht₀ hz hzr T hT identifiable⟩

end Genes

end NMSC

end Camus
