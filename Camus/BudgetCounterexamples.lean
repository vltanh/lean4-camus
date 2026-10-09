module

public import Camus.BudgetSaturation
public import Camus.Counterexamples
public import Camus.QuartetAttribution
public import Camus.GraphCompletenessFootprints
public import Camus.QuartetAttributionUnique

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

/-- The crossing quartet in the comb has two shared original vertices on its
within-pair support paths. A singleton producing cycle must contain both. -/
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
  obtain ⟨p,hp,_⟩ := RootedNetwork.switching_existsUnique_path hN H.switching
    (hleaf 0 (by decide)) (hleaf 2 (by decide))
  obtain ⟨r,hr,_⟩ := RootedNetwork.switching_existsUnique_path hN H.switching
    (hleaf 1 (by decide)) (hleaf 3 (by decide))
  have hs0 : H.site (N.leaf 0) = [false] := site_leaf H (by decide) (by decide)
  have hs1 : H.site (N.leaf 1) = [true,false] := site_leaf H (by decide) (by decide)
  have hs2 : H.site (N.leaf 2) = [true,true,true] := site_leaf H (by decide) (by decide)
  have hs3 : H.site (N.leaf 3) = [true,true,false] := site_leaf H (by decide) (by decide)
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
  have hcyc1 := RootedNetwork.single_novel_pair_vertex_on_cycle small_wellLabelled hN H
    (q0123 1) hnot hs p hp r hr hp1 hr1 hd hraw
  have hcyc2 := RootedNetwork.single_novel_pair_vertex_on_cycle small_wellLabelled hN H
    (q0123 1) hnot hs p hp r hr hp2 hr2 hd hraw
  have hsub := canonical_fundamentalCycle_support small_wellLabelled hE (by simp : e ∈ ({e} : Finset Pair)) hd
  constructor
  · exact (Realization.code_mem_cycleVertices_iff (show [true] ∈ t.nodes by decide)).mp
      (hsub (List.mem_toFinset.mpr hcyc1))
  · exact (Realization.code_mem_cycleVertices_iff (show [true,true] ∈ t.nodes by decide)).mp
      (hsub (List.mem_toFinset.mpr hcyc2))

/-- The universal exact-three upper bound in the canonical directed graph class.
The sole cited dependency is the user-authorized Observation 2. -/
theorem small_exact_three_not_display
    (observation2 : External.WarnowTabatabaeeEvansObservation2)
    {E : Finset Pair} (hE : EdgeAbove.CycleSeparated smallConstraint E) (hc : E.card = 3) :
    ¬(Realization.graph smallConstraint E).DisplaysQuartet (q0123 1) := by
  classical
  intro hq
  have hn : q0123 1 ∈ novel smallConstraint oneQuartet (Realization.graph smallConstraint E) :=
    (mem_novel_iff smallConstraint small_wellLabelled oneQuartet _ _).mpr
      ⟨by simp [oneQuartet],hq,by decide⟩
  rw [(novel_disjoint_union observation2 smallConstraint small_wellLabelled oneQuartet E hE).1] at hn
  obtain ⟨e,he,hqe⟩ := Finset.mem_biUnion.mp hn
  have hsingle := (mem_novel_iff smallConstraint small_wellLabelled oneQuartet _ _).mp hqe
  have hf := EdgeAbove.saturated_footprint hE
    (show E.card = smallConstraint.internalNodes.card by simpa [smallConstraint,PhyloTree.internalNodes] using hc) he
  obtain ⟨h1,h2⟩ := small_single_display_footprint (hE.1 he) hsingle.2.1
  rw [hf] at h1 h2
  have hbad : ([true] : Address) = [true,true] :=
    (Finset.mem_singleton.mp h1).trans (Finset.mem_singleton.mp h2).symm
  exact (by decide : ([true] : Address) ≠ [true,true]) hbad

/-- Every actual anchored directed level-1 extension at exact budget three
scores zero on the counterexample's quartet. This excludes all other optimizers,
not just the particular triangle witness used in the block model. -/
theorem graph_exact_three_score_zero
    (observation2 : External.WarnowTabatabaeeEvansObservation2)
    (N : RootedNetwork) (hN : N.AnchoredExtension smallConstraint)
    (hr : N.reticulationCount = 3) : score oneQuartet (DynamicProgramming.repertoire oneQuartet N) = 0 := by
  classical
  obtain ⟨S,⟨H⟩⟩ := hN.2
  have hE := H.extracted_separated hN.1
  obtain ⟨i⟩ := H.canonical_iso hN.1
  have hcanon := Realization.levelOne smallConstraint small_wellLabelled H.extracted hE
  have hc : H.extracted.card = 3 := by
    rw [←Realization.reticulationCount_eq_card smallConstraint H.extracted hE,
      ←i.reticulationCount_eq hN.1 hcanon]
    exact hr
  have hn : ¬N.DisplaysQuartet (q0123 1) := fun hq =>
    small_exact_three_not_display observation2 hE hc ((i.displays_iff hN.1 hcanon _).mp hq)
  simp [oneQuartet,score,DynamicProgramming.repertoire,hn]

end Camus.Counterexamples
