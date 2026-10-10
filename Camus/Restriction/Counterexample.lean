module

public import Camus.Restriction.Saturation
public import Camus.Galled.Counterexamples
public import Camus.Preliminaries.Lemmas
public import Camus.Network.Completeness.Footprints
public import Camus.Preliminaries.Lemma1.Unique

/-!
# Section 2.4: no network with three reticulations displays `AC|BD`

The bound at three reticulations in the counterexample to the monotonicity claim of Section 2.4
(the report's E5). Let `T = (A,(B,(D,C)))` (`Counterexamples.smallConstraint`, with `A = 0`,
`B = 1`, `C = 2`, `D = 3`) and `Q = {AC|BD}` (`Counterexamples.oneQuartet`). Every network built on
`T` with exactly three reticulations, the maximum `n − 1`, displays no quartet of `Q`. The networks with two reticulations are in
`Camus/Restriction/Witness.lean`.

## Main results

* `Counterexamples.small_single_display_footprint`: if adding one edge to `T` gives a network that
  displays `AC|BD`, the cycle of that edge passes through the vertices `(B,(D,C))` and `(D,C)`.
* `Counterexamples.small_exact_three_not_display`: no canonical network of three added edges on `T`
  displays `AC|BD`.
* `Counterexamples.graph_exact_three_score_zero`: every network built on `T` with exactly three
  reticulations displays no quartet of `Q`.

## Proof

`AC|BD` is not a quartet of `T`. If the canonical network of a family `E` of three added edges
displays it, then by Lemma 1 (`DynamicProgramming.novel_disjoint_union`, which uses Observation 2)
a single edge `e ∈ E` satisfies it. The paths `A`–`C` and `B`–`D` of `T` share the vertices
`(B,(D,C))` and `(D,C)`, and every vertex shared by the two paths lies on the cycle of `e`
(`RootedNetwork.single_novel_pair_vertex_on_cycle`). But with `3 = n − 1` edges the cycle of `e`
meets `T` only in its target (`EdgeAbove.saturated_footprint`): a contradiction. A network built on
`T` is isomorphic to the canonical network of its added edges (`SupportSubdivision.canonical_iso`),
which carries the result over to every network built on `T`.
-/

@[expose] public section

namespace Camus.Counterexamples

open DynamicProgramming

private theorem small_wellLabelled : smallConstraint.WellLabelled := by decide

private theorem site_leaf {t : PhyloTree} {N : RootedNetwork} {S : Finset (ℕ×ℕ)}
    (H : SupportSubdivision t N S) {p : Address} {a : ℕ}
    (hp : p ∈ t.nodes) (hpa : t.nodeAt p = some (.leaf a)) : H.site (N.leaf a) = p := by
  rw [←H.leaves_preserved p hp a hpa]
  exact H.site_original hp

private theorem canonical_fundamentalCycle_support {t : PhyloTree} (ht : t.WellLabelled)
    {E : Finset Pair} (hE : EdgeAbove.CycleSeparated t E) {e : Pair} (he : e ∈ E)
    (hd : (Realization.donor t e,Realization.recipient t e) ∈
      (Realization.graph t E).edges \ Realization.supportEdges t E) :
    (RootedNetwork.fundamentalCycle (Realization.levelOne t ht E hE)
      (Realization.support t ht E hE).switching hd).support.toFinset ⊆
        Realization.cycleVertices t e := by
  let hN := Realization.levelOne t ht E hE
  let H := Realization.support t ht E hE
  have hp : (RootedNetwork.supportPath hN H.switching hd).val =
      (Realization.cycleSupportPath t E hE e he).val := by
    exact Subtype.mk.inj ((Realization.support_acyclic t E hE).subsingleton_path _ _ |>.elim
      (RootedNetwork.supportPath hN H.switching hd)
      (Realization.cycleSupportPath t E hE e he))
  have hc : RootedNetwork.fundamentalCycle hN H.switching hd =
      Realization.fundamentalCycle t E hE e he := by
    unfold RootedNetwork.fundamentalCycle Realization.fundamentalCycle
    rw [hp]
  rw [hc]
  exact Realization.fundamentalCycle_support_subset t E hE e he

/-- If the network obtained from `T = (A,(B,(D,C)))` by adding one edge above the candidate pair
`e` displays `AC|BD`, then the cycle of `e` passes through the vertices `(B,(D,C))` (address
`[true]`) and `(D,C)` (address `[true,true]`) of `T`. Both vertices lie on the paths `A`–`C` and
`B`–`D` of `T`, and a vertex shared by the two paths lies on every cycle that produces the quartet
(`RootedNetwork.single_novel_pair_vertex_on_cycle`). -/
theorem small_single_display_footprint {e : Pair}
    (he : e ∈ EdgeAbove.candidates smallConstraint)
    (hq : (Realization.graph smallConstraint {e}).DisplaysQuartet (q0123 1)) :
    [true] ∈ EdgeAbove.footprint smallConstraint e ∧
      [true,true] ∈ EdgeAbove.footprint smallConstraint e := by
  classical
  let t := smallConstraint
  let N := Realization.graph t {e}
  let S := Realization.supportEdges t {e}
  have hE : EdgeAbove.CycleSeparated t {e} := ⟨Finset.singleton_subset_iff.mpr he,by simp⟩
  let hN := Realization.levelOne t small_wellLabelled {e} hE
  let H := Realization.support t small_wellLabelled {e} hE
  have hleaf (a : ℕ) (ha : a ∈ t.taxa) : N.leaf a ∈ N.vertices :=
    (hN.2.2.2.2.2.2.2.1 a ha).1
  -- the paths `A`–`C` and `B`–`D` of the support tree
  obtain ⟨p,hp,_⟩ := RootedNetwork.switching_existsUnique_path hN H.switching
    (hleaf 0 (by decide)) (hleaf 2 (by decide))
  obtain ⟨r,hr,_⟩ := RootedNetwork.switching_existsUnique_path hN H.switching
    (hleaf 1 (by decide)) (hleaf 3 (by decide))
  have hs0 : H.site (N.leaf 0) = [false] := site_leaf H (by decide) (by decide)
  have hs1 : H.site (N.leaf 1) = [true,false] := site_leaf H (by decide) (by decide)
  have hs2 : H.site (N.leaf 2) = [true,true,true] := site_leaf H (by decide) (by decide)
  have hs3 : H.site (N.leaf 3) = [true,true,false] := site_leaf H (by decide) (by decide)
  -- both paths pass through the vertices `(B,(D,C))` and `(D,C)`
  have hp1 : Address.code [true] ∈ p.support := by
    have hx := H.support_path_crosses_parent (a := [true,true]) p.reverse
      (by rw [hs2]; decide) (by rw [hs0]; decide)
    simpa [H,Realization.support,parent] using hx
  have hr1 : Address.code [true] ∈ r.support := by
    have hx := H.support_path_crosses_parent (a := [true,true]) r.reverse
      (by rw [hs3]; decide) (by rw [hs1]; decide)
    simpa [H,Realization.support,parent] using hx
  have hp2 : Address.code [true,true] ∈ p.support := by
    have hx := H.support_path_crosses_parent (a := [true,true,true]) p.reverse
      (by rw [hs2]) (by rw [hs0]; decide)
    simpa [H,Realization.support,parent] using hx
  have hr2 : Address.code [true,true] ∈ r.support := by
    have hx := H.support_path_crosses_parent (a := [true,true,false]) r.reverse
      (by rw [hs3]) (by rw [hs1]; decide)
    simpa [H,Realization.support,parent] using hx
  let d := (Realization.donor t e,Realization.recipient t e)
  have hd : d ∈ N.edges \ S := by
    rw [Realization.nonSupportEdges t {e} hE.1]
    simp [d]
  have hrawEq : {N with edges := insert d S} = N := by
    unfold N Realization.graph S d
    congr 1
    simp [Finset.union_comm]
  have hraw : ({N with edges := insert d S}).DisplaysQuartet (q0123 1) := hrawEq.symm ▸ hq
  have hnot : (q0123 1).induced t ≠ true := by decide
  have hs : (q0123 1).sides = ({0,2},{1,3}) := by decide
  -- a vertex shared by the two paths lies on the cycle of the added edge
  have hcyc1 := RootedNetwork.single_novel_pair_vertex_on_cycle small_wellLabelled hN H
    (q0123 1) hnot hs p hp r hr hp1 hr1 hd hraw
  have hcyc2 := RootedNetwork.single_novel_pair_vertex_on_cycle small_wellLabelled hN H
    (q0123 1) hnot hs p hp r hr hp2 hr2 hd hraw
  -- and the vertices of `T` on that cycle are those of `EdgeAbove.footprint t e`
  have hsub := canonical_fundamentalCycle_support small_wellLabelled hE (by simp : e ∈ ({e} : Finset Pair)) hd
  constructor
  · exact (Realization.code_mem_cycleVertices_iff (show [true] ∈ t.nodes by decide)).mp
      (hsub (List.mem_toFinset.mpr hcyc1))
  · exact (Realization.code_mem_cycleVertices_iff (show [true,true] ∈ t.nodes by decide)).mp
      (hsub (List.mem_toFinset.mpr hcyc2))

/-- For a cycle-separated family `E` of three added edges on `T = (A,(B,(D,C)))`, the canonical network `Realization.graph t E` does not display
`AC|BD`. -/
theorem small_exact_three_not_display
    {E : Finset Pair} (hE : EdgeAbove.CycleSeparated smallConstraint E) (hc : E.card = 3) :
    ¬(Realization.graph smallConstraint E).DisplaysQuartet (q0123 1) := by
  classical
  intro hq
  -- `AC|BD` is not a quartet of `T`, so the network satisfies it
  have hn : q0123 1 ∈ novel smallConstraint oneQuartet (Realization.graph smallConstraint E) :=
    (mem_novel_iff smallConstraint small_wellLabelled oneQuartet _ _).mpr
      ⟨by simp [oneQuartet],hq,by decide⟩
  -- by Lemma 1, a single edge `e ∈ E` satisfies it
  rw [(novel_disjoint_union smallConstraint small_wellLabelled oneQuartet E hE).1] at hn
  obtain ⟨e,he,hqe⟩ := Finset.mem_biUnion.mp hn
  have hsingle := (mem_novel_iff smallConstraint small_wellLabelled oneQuartet _ _).mp hqe
  -- with `3 = n − 1` edges, the cycle of `e` meets `T` only in its target
  have hf := EdgeAbove.saturated_footprint hE
    (show E.card = smallConstraint.internalNodes.card by simpa [smallConstraint,PhyloTree.internalNodes] using hc) he
  -- but it passes through the two vertices `(B,(D,C))` and `(D,C)`
  obtain ⟨h1,h2⟩ := small_single_display_footprint (hE.1 he) hsingle.2.1
  rw [hf] at h1 h2
  have hbad : ([true] : Address) = [true,true] :=
    (Finset.mem_singleton.mp h1).trans (Finset.mem_singleton.mp h2).symm
  exact (by decide : ([true] : Address) ≠ [true,true]) hbad

/-- E5 (Section 2.4), the bound at three reticulations. Every network built on
`T = (A,(B,(D,C)))` with exactly three reticulations displays no quartet of `Q = {AC|BD}`: its score is `0`. -/
theorem graph_exact_three_score_zero
    (N : RootedNetwork) (hN : N.AnchoredExtension smallConstraint)
    (hr : N.reticulationCount = 3) : score oneQuartet (DynamicProgramming.repertoire oneQuartet N) = 0 := by
  classical
  -- `N` is isomorphic to the canonical network of its three added edges
  obtain ⟨S,⟨H⟩⟩ := hN.2
  have hE := H.extracted_separated hN.1
  obtain ⟨i⟩ := H.canonical_iso hN.1
  have hcanon := Realization.levelOne smallConstraint small_wellLabelled H.extracted hE
  have hc : H.extracted.card = 3 := by
    rw [←Realization.reticulationCount_eq_card smallConstraint H.extracted hE,
      ←i.reticulationCount_eq hN.1 hcanon]
    exact hr
  have hn : ¬N.DisplaysQuartet (q0123 1) := fun hq =>
    small_exact_three_not_display hE hc ((i.displays_iff hN.1 hcanon _).mp hq)
  simp [oneQuartet,score,DynamicProgramming.repertoire,hn]

end Camus.Counterexamples
