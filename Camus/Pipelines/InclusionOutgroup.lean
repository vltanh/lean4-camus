module

public import Camus.Pipelines.SNP

/-!
# Section 3.2: the deeper donor, with an outgroup

Section 3.2 runs its SNP pipeline "provided we have an outgroup": the tree returned by ASTRAL "will
be rooted using the outgroup and then passed to CAMUS". The deeper-donor example of
`Camus/Pipelines/Inclusion.lean` has no outgroup: in `((A,B),(C,(F,(D,E))))` no leaf is a child of
the root, and the cycle of the added edge passes through the root. This file gives the example
with an outgroup. Take the tree `(O,((A,B),(C,(F,(D,E)))))` (`Counterexamples.outgroupTree`), with
the outgroup `O = 6` a child of the root, and add one edge inside the ingroup, from above the
cherry `(D,E)` to above `A` (`Counterexamples.outgroupShallowNet`), or from above `D` to above `A`
(`Counterexamples.outgroupDeepNet`). The cycles of both networks avoid their root
(`Counterexamples.outgroup_root_not_on_cycle`), and the leaf of `O` is a child of the root
(`Counterexamples.outgroup_leaf_child`). As in the example without an outgroup, the second network
displays every quartet that the first displays and one more, `AD|EF`, so it is optimal for every
multiset version of the quartets of the first, with the fewest reticulations among the optimal
networks, and it is not isomorphic to the first. Inside the model of Warnow, Tabatabaee and Evans,
this holds with probability tending to 1 (`snp_outgroup_tendsto`).

The facts used about single-edge networks `T + e` are stated for every tree: two networks that
differ in one displayed quartet are not isomorphic (`Realization.single_not_iso`); if `T + e'`
displays every quartet that `T + e` displays, and `T + e` displays a quartet that `T` does not
induce, then `T + e'` is optimal for every multiset version of the quartets of `T + e`, with the
fewest reticulations (`Realization.single_optimal_fewest`); and the vertices on the cycles of
`T + e` are those of the cycle γ(u, w) (`Realization.mem_cycleVertices_of_cycle`), so that the root
lies on no cycle when it is not in the footprint of `e` (`Realization.root_not_on_cycle`).

## Main results

* `Realization.single_not_iso`, `Realization.single_optimal_fewest`,
  `Realization.root_not_on_cycle`: single-edge networks.
* `Counterexamples.outgroupTree`, `Counterexamples.outgroupShallowNet`,
  `Counterexamples.outgroupDeepNet`: the example with an outgroup.
* `Counterexamples.outgroup_leaf_child`, `Counterexamples.outgroup_root_not_on_cycle`: the
  outgroup is a child of the root, and the root lies on no cycle.
* `Counterexamples.outgroupDeep_optimal_fewest`, `Counterexamples.outgroupDeep_not_iso`: the
  deeper donor is optimal with the fewest reticulations, and not isomorphic to the true network.
* `snp_outgroup_tendsto`: the report's E7 in WTE's model, with an outgroup.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology

namespace Camus

namespace Realization

open DynamicProgramming

variable {t : PhyloTree} {e e' : Pair}

/-- The family `{e}` of one admissible pair is feasible. -/
theorem single_separated (he : e ∈ EdgeAbove.candidates t) :
    EdgeAbove.CycleSeparated t {e} :=
  ⟨Finset.singleton_subset_iff.mpr he, by simp⟩

/-- `T + e` is built on `T`. -/
theorem single_anchored (ht : t.WellLabelled) (he : e ∈ EdgeAbove.candidates t) :
    (graph t {e}).AnchoredExtension t :=
  ⟨levelOne t ht _ (single_separated he), ⟨_, ⟨support t ht _ (single_separated he)⟩⟩⟩

/-- `T + e` has one reticulation. -/
theorem single_reticulationCount (he : e ∈ EdgeAbove.candidates t) :
    (graph t {e}).reticulationCount = 1 := by
  rw [reticulationCount_eq_card t _ (single_separated he), Finset.card_singleton]

/-- If `T + e'` displays a quartet that `T + e` does not, the two networks are not isomorphic:
isomorphic networks display the same quartets. -/
theorem single_not_iso (ht : t.WellLabelled) (he : e ∈ EdgeAbove.candidates t)
    (he' : e' ∈ EdgeAbove.candidates t) {q : Quartet} (h' : (graph t {e'}).DisplaysQuartet q)
    (h : ¬ (graph t {e}).DisplaysQuartet q) : IsEmpty ((graph t {e'}).Iso (graph t {e})) :=
  ⟨fun i => h ((i.displays_iff (single_anchored ht he').1 (single_anchored ht he).1 q).mp h')⟩

/-- Let `T + e'` display every quartet that `T + e` displays, and let `T + e` display a quartet
`qs` that `T` does not induce. If `Q` is a multiset version of the quartets displayed by `T + e`,
then `T + e'` displays as many quartets of `Q` as any network built on `T`, and has the fewest
reticulations among the networks built on `T` that do: it has one, and a network built on `T`
with none is isomorphic to `T` (`tree_identifiable`), which does not display `qs`. -/
theorem single_optimal_fewest (ht : t.WellLabelled) (he : e ∈ EdgeAbove.candidates t)
    (he' : e' ∈ EdgeAbove.candidates t)
    (hincl : ∀ q, (graph t {e}).DisplaysQuartet q → (graph t {e'}).DisplaysQuartet q)
    {qs : Quartet} (hqs : (graph t {e}).DisplaysQuartet qs) (hnot : qs.induced t = false)
    (Q : Multiset Quartet) (hQ : ∀ q, q ∈ Q ↔ (graph t {e}).DisplaysQuartet q) :
    (∀ R : RootedNetwork, R.AnchoredExtension t →
        score Q (repertoire Q R) ≤ score Q (repertoire Q (graph t {e'}))) ∧
      (∀ R : RootedNetwork, R.AnchoredExtension t →
        (∀ R' : RootedNetwork, R'.AnchoredExtension t →
          score Q (repertoire Q R') ≤ score Q (repertoire Q R)) →
        (graph t {e'}).reticulationCount ≤ R.reticulationCount) := by
  classical
  -- `T + e'` displays every quartet of `Q`, so its score is `|Q|`, the largest possible
  have hdeep : score Q (repertoire Q (graph t {e'})) = Q.card := by
    apply (score_eq_card_iff Q _).mpr
    intro q hq
    simp only [repertoire, Finset.mem_filter]
    exact ⟨hq, hincl q ((hQ q).mp (Multiset.mem_toFinset.mp hq))⟩
  refine ⟨fun R _ => hdeep ▸ score_le_card _ _, ?_⟩
  intro R hR hopt
  rw [single_reticulationCount he']
  -- an optimal `R` displays every quartet of `Q`
  have hRscore : score Q (repertoire Q R) = Q.card :=
    le_antisymm (score_le_card _ _) (hdeep ▸ hopt _ (single_anchored ht he'))
  have hall : ∀ q, (graph t {e}).DisplaysQuartet q → R.DisplaysQuartet q := by
    intro q hq
    have hmem := (score_eq_card_iff Q _).mp hRscore (Multiset.mem_toFinset.mpr ((hQ q).mpr hq))
    simp only [repertoire, Finset.mem_filter] at hmem
    exact hmem.2
  -- with no reticulation, `R` would be isomorphic to `T`, which does not display `qs`
  by_contra hzero
  have hbase : EdgeAbove.CycleSeparated t ∅ := by simp [EdgeAbove.CycleSeparated]
  have hT : ∀ q, (graph t ∅).DisplaysQuartet q → R.DisplaysQuartet q := by
    intro q hq
    have hind := (baseline_displays_iff t ht q).mp hq
    apply hall q
    rw [single_displays_iff ht he]
    exact ⟨((Quartet.induced_iff_taxaAt q t).mp hind).1, Or.inl hind⟩
  obtain ⟨i⟩ := tree_identifiable t ht R hR hT (by
    rw [reticulationCount_eq_card t ∅ hbase, Finset.card_empty]
    omega)
  have hTq := (i.displays_iff hR.1 (levelOne t ht ∅ hbase) qs).mp (hall qs hqs)
  rw [baseline_displays_iff t ht, hnot] at hTq
  exact Bool.false_ne_true hTq

/-- Every vertex on a cycle of `Realization.graph t E`, for a cycle-separated family `E`, is a
vertex of the cycle γ(u, w) of some pair `(u, w)` of `E`: every edge of the cycle lies on the
fundamental cycle of a pair (`Realization.cycle_edge_in_fundamental`). -/
theorem mem_cycleVertices_of_cycle {E : Finset Pair} (hE : EdgeAbove.CycleSeparated t E) {v w : ℕ}
    (c : (graph t E).underlying.Walk v v) (hc : c.IsCycle) (hw : w ∈ c.support) :
    ∃ f ∈ E, w ∈ cycleVertices t f := by
  obtain ⟨r, hr, hwr⟩ := (SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil
    hc.not_nil).mp hw
  obtain ⟨f, hf, hrf⟩ := cycle_edge_in_fundamental hE c hc hr
  exact ⟨f, hf, fundamentalCycle_support_subset t E hE f hf
    (List.mem_toFinset.mpr (SimpleGraph.Walk.mem_support_of_mem_edges hrf hwr))⟩

/-- If the root of `T` is in the footprint of no pair of `E`, the root of `Realization.graph t E`
lies on no cycle. -/
theorem root_not_on_cycle {E : Finset Pair} (hE : EdgeAbove.CycleSeparated t E)
    (hroot : ∀ f ∈ E, ([] : Address) ∉ EdgeAbove.footprint t f) {v : ℕ}
    (c : (graph t E).underlying.Walk v v) (hc : c.IsCycle) : (graph t E).root ∉ c.support := by
  intro hmem
  obtain ⟨f, hf, hroot'⟩ := mem_cycleVertices_of_cycle hE c hc hmem
  exact hroot f hf ((code_mem_cycleVertices_iff t.root_mem_nodes).mp hroot')

end Realization

namespace Counterexamples

open DynamicProgramming

/-- The seven-leaf tree `(O,((A,B),(C,(F,(D,E)))))`: the outgroup `O = 6`, a child of the root,
and the ingroup `donorTree`. -/
def outgroupTree : PhyloTree := .fork (.leaf 6) donorTree

/-- The pair `((D,E), A)` inside the ingroup: an edge from above the cherry `(D,E)` to above `A`.
Its target is the root of the ingroup. -/
def outgroupShallowPair : Pair := ([true, true, true, true], [true, false, false])

/-- The pair `(D, A)` inside the ingroup. Its donor `D` lies below the donor `(D,E)` of
`outgroupShallowPair`. -/
def outgroupDeepPair : Pair := ([true, true, true, true, false], [true, false, false])

/-- The network `T + ((D,E), A)` on the tree with an outgroup, the true network of the
example. -/
noncomputable abbrev outgroupShallowNet : RootedNetwork :=
  Realization.graph outgroupTree {outgroupShallowPair}

/-- The network `T + (D, A)` on the tree with an outgroup. -/
noncomputable abbrev outgroupDeepNet : RootedNetwork :=
  Realization.graph outgroupTree {outgroupDeepPair}

/-- The leaf labels of `(O,((A,B),(C,(F,(D,E)))))` are distinct. -/
theorem outgroupTree_wellLabelled : outgroupTree.WellLabelled := by decide

/-- An edge can be added above `((D,E), A)`. -/
theorem outgroupShallowPair_mem : outgroupShallowPair ∈ EdgeAbove.candidates outgroupTree := by
  decide

/-- An edge can be added above `(D, A)`. -/
theorem outgroupDeepPair_mem : outgroupDeepPair ∈ EdgeAbove.candidates outgroupTree := by
  decide

/-- The outgroup is a child of the root of the tree. -/
theorem outgroupTree_child : outgroupTree.nodeAt [false] = some (.leaf 6) := rfl

/-- `outgroupShallowNet` is built on the tree. -/
theorem outgroupShallowNet_anchored : outgroupShallowNet.AnchoredExtension outgroupTree :=
  Realization.single_anchored outgroupTree_wellLabelled outgroupShallowPair_mem

/-- `outgroupDeepNet` is built on the tree. -/
theorem outgroupDeepNet_anchored : outgroupDeepNet.AnchoredExtension outgroupTree :=
  Realization.single_anchored outgroupTree_wellLabelled outgroupDeepPair_mem

/-- The root of `outgroupShallowNet` lies on no cycle: the cycle of its added edge has the root
of the ingroup at its top. -/
theorem outgroup_root_not_on_cycle {v : ℕ} (c : outgroupShallowNet.underlying.Walk v v)
    (hc : c.IsCycle) : outgroupShallowNet.root ∉ c.support := by
  refine Realization.root_not_on_cycle (Realization.single_separated outgroupShallowPair_mem)
    ?_ c hc
  intro f hf
  rw [Finset.mem_singleton.mp hf]
  decide

/-- The leaf of the outgroup is a child of the root of `outgroupShallowNet`: no added edge
subdivides the edge of the tree above it. -/
theorem outgroup_leaf_child :
    (outgroupShallowNet.root, outgroupShallowNet.leaf 6) ∈ outgroupShallowNet.edges := by
  have hleaf : Realization.leafAddress outgroupTree 6 = [false] :=
    Realization.leafAddress_eq outgroupTree_wellLabelled outgroupTree_child
  change (Address.code [], Address.code (Realization.leafAddress outgroupTree 6)) ∈
    Realization.supportEdges outgroupTree {outgroupShallowPair} ∪ _
  rw [hleaf]
  refine Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨[false], by decide, ?_⟩)
  simp [Realization.wire, Realization.outerEndpoints, Realization.ghostEndpoints, wireEdges,
    outgroupShallowPair, parent]

/-- Every quartet displayed by `outgroupShallowNet` is displayed by `outgroupDeepNet`: the pair
`((D,E), A)` is a cross pair, and `D` lies below `(D,E)` (`Realization.deeper_donor_displays`). -/
theorem outgroup_subset_deep (q : Quartet) :
    outgroupShallowNet.DisplaysQuartet q → outgroupDeepNet.DisplaysQuartet q :=
  (Realization.deeper_donor_displays (u₂ := [true, true, true, true, false])
    outgroupTree_wellLabelled outgroupShallowPair_mem (by decide) (by decide) (by decide)
    (by decide)).2 q

/-- `outgroupDeepNet` displays `AD|EF`. -/
theorem outgroup_witness_deep : outgroupDeepNet.DisplaysQuartet witnessQuartet := by
  rw [Realization.single_displays_iff outgroupTree_wellLabelled outgroupDeepPair_mem]
  decide +kernel

/-- `outgroupShallowNet` does not display `AD|EF`. -/
theorem outgroup_witness_not_shallow : ¬ outgroupShallowNet.DisplaysQuartet witnessQuartet := by
  rw [Realization.single_displays_iff outgroupTree_wellLabelled outgroupShallowPair_mem]
  decide +kernel

/-- `outgroupShallowNet` displays `AD|BC`, which the tree does not induce. -/
theorem outgroup_satisfied : outgroupShallowNet.DisplaysQuartet satisfiedQuartet ∧
    satisfiedQuartet.induced outgroupTree = false := by
  refine ⟨?_, by decide⟩
  rw [Realization.single_displays_iff outgroupTree_wellLabelled outgroupShallowPair_mem]
  decide +kernel

/-- `outgroupDeepNet` and `outgroupShallowNet` are not isomorphic. -/
theorem outgroupDeep_not_iso : IsEmpty (outgroupDeepNet.Iso outgroupShallowNet) :=
  Realization.single_not_iso outgroupTree_wellLabelled outgroupShallowPair_mem
    outgroupDeepPair_mem outgroup_witness_deep outgroup_witness_not_shallow

/-- If `Q` is a multiset version of the quartets displayed by `outgroupShallowNet`, then
`outgroupDeepNet` displays as many quartets of `Q` as any network built on the tree, and has the
fewest reticulations among the networks built on the tree that do. -/
theorem outgroupDeep_optimal_fewest (Q : Multiset Quartet)
    (hQ : ∀ q, q ∈ Q ↔ outgroupShallowNet.DisplaysQuartet q) :
    (∀ R : RootedNetwork, R.AnchoredExtension outgroupTree →
        score Q (DynamicProgramming.repertoire Q R) ≤
          score Q (DynamicProgramming.repertoire Q outgroupDeepNet)) ∧
      (∀ R : RootedNetwork, R.AnchoredExtension outgroupTree →
        (∀ R' : RootedNetwork, R'.AnchoredExtension outgroupTree →
          score Q (DynamicProgramming.repertoire Q R') ≤
            score Q (DynamicProgramming.repertoire Q R)) →
        outgroupDeepNet.reticulationCount ≤ R.reticulationCount) :=
  Realization.single_optimal_fewest outgroupTree_wellLabelled outgroupShallowPair_mem
    outgroupDeepPair_mem outgroup_subset_deep outgroup_satisfied.1 outgroup_satisfied.2 Q hQ

end Counterexamples

variable {σ : Type*} [Fintype σ] [DecidableEq σ] [Nontrivial σ] {Ω : Type*} [MeasurableSpace Ω]

open DynamicProgramming in
/-- Section 3.2, the report's E7 in WTE's model, with an outgroup: take for the true network
`Counterexamples.outgroupShallowNet`, built on the tree `(O,((A,B),(C,(F,(D,E)))))` whose
outgroup `O` is a child of the root, any site model on it with at least two states, and
independent sites with its law. Then the probability that `Counterexamples.outgroupDeepNet`,
which is built on the same tree and not isomorphic to the true network, displays as many quartets
of `Q_m` as any network built on the tree, with the fewest reticulations among those, tends
to 1. -/
theorem snp_outgroup_tendsto (M : External.SiteModel Counterexamples.outgroupShallowNet σ)
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → External.SiteHistory Counterexamples.outgroupShallowNet σ)
    (hind : iIndepFun X μ) (hid : ∀ n, IdentDistrib (X n) (X 0) μ μ)
    (hlaw : μ.map (X 0) = M.law Counterexamples.outgroupShallowNet_anchored.1) :
    Tendsto (fun m => μ {ω |
      (∀ R : RootedNetwork, R.AnchoredExtension Counterexamples.outgroupTree →
        score (External.sampleQuartets X m ω) (repertoire (External.sampleQuartets X m ω) R) ≤
          score (External.sampleQuartets X m ω)
            (repertoire (External.sampleQuartets X m ω) Counterexamples.outgroupDeepNet)) ∧
      (∀ R : RootedNetwork, R.AnchoredExtension Counterexamples.outgroupTree →
        (∀ R' : RootedNetwork, R'.AnchoredExtension Counterexamples.outgroupTree →
          score (External.sampleQuartets X m ω) (repertoire (External.sampleQuartets X m ω) R') ≤
            score (External.sampleQuartets X m ω)
              (repertoire (External.sampleQuartets X m ω) R)) →
        Counterexamples.outgroupDeepNet.reticulationCount ≤ R.reticulationCount) ∧
      IsEmpty (Counterexamples.outgroupDeepNet.Iso Counterexamples.outgroupShallowNet)})
      atTop (𝓝 1) := by
  -- the support of `Q_m` is `Q(N_r)` with probability tending to 1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (External.support_tendsto M Counterexamples.outgroupShallowNet_anchored.1 X hind hid hlaw)
    tendsto_const_nhds (fun m => measure_mono fun ω hω => ?_) fun _ => prob_le_one
  -- on that event, the deeper donor is optimal with the fewest reticulations
  exact ⟨(Counterexamples.outgroupDeep_optimal_fewest _ hω).1,
    (Counterexamples.outgroupDeep_optimal_fewest _ hω).2, Counterexamples.outgroupDeep_not_iso⟩

end Camus
