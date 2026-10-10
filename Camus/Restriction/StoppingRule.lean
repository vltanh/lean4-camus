module

public import Camus.Restriction.Backtracking
public import Camus.Network.SingleEdge

/-!
# Section 2.4: the stopping rule can stop before a better score

Section 2.4 of the paper computes the array `M[v, k]` "in order of increasing k, dynamically adding
new columns to our matrix, until we no longer get an improvement in score", where `m` is "the
number of reticulations after which the score does not improve". Read as the claim that the score
does not improve after the first `k` at which it stops improving, this is false, both for exact
numbers of reticulations (as the array computes them) and for "at most k" reticulations.

Let `T = (A,(B,(C,(D,(E,(F,(G,H)))))))` be the caterpillar on eight leaves (`A = 0`, …, `H = 7`,
`Counterexamples.caterpillar`) and `Q = {AF|CG, AF|CG, AC|BD, AE|DF, AH|FG}`
(`Counterexamples.stopQuartets`). The best number of quartets of `Q` displayed by a network built
on `T` is `0` with no reticulation, `2` with one, `2` with two, and `3` with three, whether
"with `k`" means exactly `k` or at most `k` reticulations:
* one edge: the edge above `(A, F)` satisfies `AF|CG`, of multiplicity `2`, and no edge satisfies
  more than two quartets of `Q`, counted with multiplicity;
* two edges: the cycle of an edge that satisfies two quartets of `Q` (counted with multiplicity)
  passes through the vertices `(C,(D,…))`, `(D,(E,…))` and `(F,(G,H))` of `T`, and the cycle of an
  edge that satisfies a quartet of `Q` passes through one of them; so two edges with disjoint
  cycles satisfy at most two quartets of `Q`;
* three edges: the edges above `(A, C)`, `((D,(E,(F,(G,H)))), E)` and `((F,(G,H)), H)` have
  vertex-disjoint cycles and satisfy `AC|BD`, `AE|DF` and `AH|FG`.

So the rule stops with `m = 1` and score `2`, while three reticulations give `3`, the best score of
any network built on `T` (`not_exactStoppingRule`, `not_atMostStoppingRule`). For every array of
the recurrence the root rows of `k = 0, 1, 2, 3` are `{0}`, `{2}`, `{2}`, `{3}`
(`Counterexamples.caterpillar_root_rows`), and the rule applied to them stops at `m = 1`
(`Counterexamples.caterpillar_array_stops`).

## Main results

* `bestExact`, `bestAtMost`: the best score with exactly, and with at most, `k` reticulations.
* `StopsAt`: the stopping rule on a sequence of scores.
* `ExactStoppingRule`, `AtMostStoppingRule`: the score does not improve after the point where the
  rule stops, for the two readings.
* `not_exactStoppingRule`, `not_atMostStoppingRule`: both claims are false.
* `Counterexamples.caterpillar_scores`: the best scores of the counterexample.
* `Counterexamples.caterpillar_root_rows`, `Counterexamples.caterpillar_array_stops`: the root rows
  of the array for the counterexample, and where the rule stops on them.

## Proof

The weight `s_e` of Equation (1) of each of the 140 admissible pairs of `T` is computed through
`DynamicProgramming.edgeWeight_eq_satisfies` (`Counterexamples.stop_weight_table`, by `decide`):
every weight is at most `2`; the cycle of every pair of weight `2` passes through the three
vertices `(C,(D,…))`, `(D,(E,…))` and `(F,(G,H))` of `T` (`Counterexamples.stopHubs`), and the cycle
of every pair of positive weight passes through one of them. In a cycle-separated family, a pair
of weight `2` leaves weight `0` to the other pairs (`Counterexamples.stop_value_of_heavy`), and the
pairs of positive weight pass through distinct hubs (`Counterexamples.stop_value_of_light`). So a
cycle-separated family has value at most `3`, and at most `2` if it has at most two pairs
(`Counterexamples.stop_value_le_three`, `Counterexamples.stop_value_le_two`).
By Lemma 1 (`DynamicProgramming.novel_score_value`) and the reduction of a network built on `T` to
the canonical network of its added edges (`SupportSubdivision.canonical_iso`), a network built on
`T` displays as many quartets of `Q` as the value of its family of added edges, since `T` displays
none of them (`Counterexamples.stop_network_score`).
-/

@[expose] public section

namespace Camus

open DynamicProgramming

/-- The best number of quartets of `Q`, counted with multiplicity, displayed by a network built on
`T` with exactly `k` reticulations, and `0` if there is no such network. -/
noncomputable def bestExact (t : PhyloTree) (Q : Multiset Quartet) (k : ℕ) : ℕ :=
  sSup {s | ∃ N : RootedNetwork, N.AnchoredExtension t ∧ N.reticulationCount = k ∧
    score Q (repertoire Q N) = s}

/-- The best number of quartets of `Q`, counted with multiplicity, displayed by a network built on
`T` with at most `k` reticulations. -/
noncomputable def bestAtMost (t : PhyloTree) (Q : Multiset Quartet) (k : ℕ) : ℕ :=
  sSup {s | ∃ N : RootedNetwork, N.AnchoredExtension t ∧ N.reticulationCount ≤ k ∧
    score Q (repertoire Q N) = s}

/-- Section 2.4's stopping rule on the scores `s 0, s 1, …` of the columns: columns are added "until
we no longer get an improvement in score", and `m` is "the number of reticulations after which the
score does not improve". The rule stops at `m` if the score improves at each column before `m`, and
does not improve from `m` to `m + 1`. -/
def StopsAt (s : ℕ → ℕ) (m : ℕ) : Prop :=
  (∀ j < m, s j < s (j + 1)) ∧ s (m + 1) ≤ s m

/-- Section 2.4's stopping rule, for exact numbers of reticulations, as the array of Section 2.4
computes them: for every well-labelled tree `T` and multiset `Q`, if the rule stops at `m` on the
best scores with exactly `k` reticulations, then the score does not improve after `m`: no network
built on `T` with `j ≥ m` reticulations displays more quartets of `Q` than the best network with
exactly `m`. For a fixed `T` the number of quartets of `Q` displayed and the number satisfied
differ by the number of quartets of `Q` that `T` induces, so the claim reads the same for
either. -/
def ExactStoppingRule : Prop :=
  ∀ t : PhyloTree, t.WellLabelled → ∀ (Q : Multiset Quartet) (m : ℕ),
    StopsAt (bestExact t Q) m → ∀ j, m ≤ j → bestExact t Q j ≤ bestExact t Q m

/-- Section 2.4's stopping rule, for "at most k" reticulations: for every well-labelled tree `T`
and multiset `Q`, if the rule stops at `m` on the best scores with at most `k` reticulations, then
no network built on `T` displays more quartets of `Q` than the best network with at most `m`
reticulations. -/
def AtMostStoppingRule : Prop :=
  ∀ t : PhyloTree, t.WellLabelled → ∀ (Q : Multiset Quartet) (m : ℕ),
    StopsAt (bestAtMost t Q) m → ∀ j, bestAtMost t Q j ≤ bestAtMost t Q m

/-- A family of admissible pairs whose cycles meet `T` in pairwise disjoint sets is
cycle-separated. -/
theorem EdgeAbove.separated_of_pairwise {t : PhyloTree} {E : Finset Pair}
    (h1 : E ⊆ EdgeAbove.candidates t)
    (h2 : ∀ e ∈ E, ∀ f ∈ E, e ≠ f →
      Disjoint (EdgeAbove.footprint t e) (EdgeAbove.footprint t f)) :
    EdgeAbove.CycleSeparated t E :=
  ⟨h1, fun e he f hf hne => h2 e he f hf hne⟩

namespace Counterexamples

/-- The caterpillar `T = (A,(B,(C,(D,(E,(F,(G,H)))))))` on eight leaves, with `A = 0`, …, `H = 7`.
Its internal vertices are the root and the vertices `[true]`, `[true,true]`, …, of the spine. -/
def caterpillar : PhyloTree :=
  .fork (.leaf 0) (.fork (.leaf 1) (.fork (.leaf 2) (.fork (.leaf 3)
    (.fork (.leaf 4) (.fork (.leaf 5) (.fork (.leaf 6) (.leaf 7)))))))

/-- The quartet `AF|CG` on the taxa `{0, 2, 5, 6}`. -/
def stopAF : Quartet := ⟨0, 2, 5, 6, by decide, by decide, by decide, 1⟩

/-- The quartet `AC|BD` on the taxa `{0, 1, 2, 3}`. -/
def stopAC : Quartet := ⟨0, 1, 2, 3, by decide, by decide, by decide, 1⟩

/-- The quartet `AE|DF` on the taxa `{0, 3, 4, 5}`. -/
def stopAE : Quartet := ⟨0, 3, 4, 5, by decide, by decide, by decide, 1⟩

/-- The quartet `AH|FG` on the taxa `{0, 5, 6, 7}`. -/
def stopAH : Quartet := ⟨0, 5, 6, 7, by decide, by decide, by decide, 2⟩

/-- `Q = {AF|CG, AF|CG, AC|BD, AE|DF, AH|FG}`: the quartet `AF|CG` has multiplicity `2`. -/
def stopQuartets : Multiset Quartet :=
  {stopAF, stopAF, stopAC, stopAE, stopAH}

/-- The pair `(A, F)`: the edge added above it satisfies `AF|CG`. -/
def stopHeavyPair : Pair := ([false], [true,true,true,true,true,false])

/-- The pair `(G, H)`: the edge added above it forms a triangle at `(G,H)`. -/
def stopCherryPair : Pair :=
  ([true,true,true,true,true,true,false], [true,true,true,true,true,true,true])

/-- The pairs `(A, C)`, `((D,(E,(F,(G,H)))), E)` and `((F,(G,H)), H)`: the edges added above them
satisfy `AC|BD`, `AE|DF` and `AH|FG`. -/
def stopLightPairs : Finset Pair :=
  {([false], [true,true,false]), ([true,true,true], [true,true,true,true,false]),
    ([true,true,true,true,true], [true,true,true,true,true,true,true])}

/-- The vertices `(C,(D,…))`, `(D,(E,…))` and `(F,(G,H))` of `T`. The cycle of every edge that
satisfies a quartet of `Q` passes through one of them. -/
def stopHubs : Finset Address :=
  {[true,true], [true,true,true], [true,true,true,true,true]}

/-- The weight `s_e` of Equation (1) in computable form
(`DynamicProgramming.edgeWeight_eq_satisfies`): the sum over the distinct quartets `q` of `Q` of
δ_T(q, e). -/
def stopWeightSum (e : Pair) : ℕ :=
  ∑ q ∈ stopQuartets.toFinset,
    if EdgeAbove.satisfies caterpillar e q = true then stopQuartets.count q else 0

/-- The leaves of `T` have distinct labels. -/
theorem caterpillar_wellLabelled : caterpillar.WellLabelled := by decide

/-- The weights `s_e` (Equation (1)) of `Q` on `T`. -/
noncomputable abbrev stopWeight : Pair → ℕ := edgeWeight caterpillar stopQuartets

/-- Equation (1), computably, on `T`. -/
theorem stopWeight_eq {e : Pair} (he : e ∈ EdgeAbove.candidates caterpillar) :
    stopWeight e = stopWeightSum e :=
  edgeWeight_eq_satisfies caterpillar_wellLabelled he stopQuartets

/-- The weights of the 140 admissible pairs of `T`: each is at most `2`; the cycle of a pair of
weight `2` passes through the three hubs, and the cycle of a pair of positive weight through one of
them. -/
theorem stop_weight_table : ∀ e ∈ EdgeAbove.candidates caterpillar,
    stopWeightSum e ≤ 2 ∧
      (stopWeightSum e = 2 → stopHubs ⊆ EdgeAbove.footprint caterpillar e) ∧
      (1 ≤ stopWeightSum e → ∃ x ∈ stopHubs, x ∈ EdgeAbove.footprint caterpillar e) := by
  decide +kernel

/-- The weights of the admissible pairs of `T`, as in `stop_weight_table`. -/
theorem stopWeight_facts {e : Pair} (he : e ∈ EdgeAbove.candidates caterpillar) :
    stopWeight e ≤ 2 ∧ (stopWeight e = 2 → stopHubs ⊆ EdgeAbove.footprint caterpillar e) ∧
      (1 ≤ stopWeight e → ∃ x ∈ stopHubs, x ∈ EdgeAbove.footprint caterpillar e) := by
  rw [stopWeight_eq he]
  exact stop_weight_table e he

/-- A pair of weight `2` in a cycle-separated family leaves weight `0` to the others: their cycles
avoid the hubs. -/
theorem stop_value_of_heavy {E : Finset Pair} (hE : EdgeAbove.CycleSeparated caterpillar E)
    {e : Pair} (he : e ∈ E) (h2 : stopWeight e = 2) : value stopWeight E = 2 := by
  classical
  have hzero : ∀ f ∈ E.erase e, stopWeight f = 0 := by
    intro f hf
    obtain ⟨hne, hfE⟩ := Finset.mem_erase.mp hf
    by_contra hpos
    obtain ⟨x, hx, hxf⟩ := (stopWeight_facts (hE.1 hfE)).2.2 (by omega)
    have hxe := (stopWeight_facts (hE.1 he)).2.1 h2 hx
    exact Finset.disjoint_left.mp (hE.2 he hfE (Ne.symm hne)) hxe hxf
  have hsum := Finset.add_sum_erase E stopWeight he
  rw [Finset.sum_eq_zero hzero, h2] at hsum
  change ∑ f ∈ E, stopWeight f = 2
  omega

/-- A cycle-separated family of pairs of weight at most `1` has value at most its number of pairs,
and at most `3`: its pairs of weight `1` pass through distinct hubs. -/
theorem stop_value_of_light {E : Finset Pair} (hE : EdgeAbove.CycleSeparated caterpillar E)
    (h1 : ∀ e ∈ E, stopWeight e ≤ 1) : value stopWeight E ≤ E.card ∧ value stopWeight E ≤ 3 := by
  classical
  constructor
  · calc value stopWeight E = ∑ e ∈ E, stopWeight e := rfl
      _ ≤ ∑ _e ∈ E, 1 := Finset.sum_le_sum h1
      _ = E.card := by simp
  · -- the pairs of positive weight, each counted at most once
    let P := E.filter (fun e => stopWeight e ≠ 0)
    have hP : value stopWeight E ≤ P.card := by
      rw [value, ← Finset.sum_filter_ne_zero]
      calc ∑ e ∈ P, stopWeight e ≤ ∑ _e ∈ P, 1 :=
            Finset.sum_le_sum (fun e he => h1 e (Finset.mem_filter.mp he).1)
        _ = P.card := by simp
    -- each passes through a hub
    let pick : Pair → Address := fun e =>
      if [true,true] ∈ EdgeAbove.footprint caterpillar e then [true,true]
      else if [true,true,true] ∈ EdgeAbove.footprint caterpillar e then [true,true,true]
      else [true,true,true,true,true]
    have hpick : ∀ e ∈ P, pick e ∈ stopHubs ∧ pick e ∈ EdgeAbove.footprint caterpillar e := by
      intro e he
      obtain ⟨heE, hne⟩ := Finset.mem_filter.mp he
      obtain ⟨x, hx, hxf⟩ := (stopWeight_facts (hE.1 heE)).2.2 (by omega)
      simp only [stopHubs, Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [pick]
      split_ifs with ha hb
      · exact ⟨by simp [stopHubs], ha⟩
      · exact ⟨by simp [stopHubs], hb⟩
      · refine ⟨by simp [stopHubs], ?_⟩
        rcases hx with rfl | rfl | rfl
        · exact (ha hxf).elim
        · exact (hb hxf).elim
        · exact hxf
    -- distinct pairs pass through distinct hubs, since their cycles are disjoint
    have hcard : P.card ≤ stopHubs.card := by
      apply Finset.card_le_card_of_injOn pick (fun e he => (hpick e he).1)
      intro e he f hf h
      by_contra hne
      have hef := hE.2 (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp hf).1 hne
      exact Finset.disjoint_left.mp hef (hpick e he).2 (by rw [h]; exact (hpick f hf).2)
    have h3 : stopHubs.card = 3 := by decide
    omega

/-- Every cycle-separated family of pairs of `T` has value at most `3`. -/
theorem stop_value_le_three {E : Finset Pair} (hE : EdgeAbove.CycleSeparated caterpillar E) :
    value stopWeight E ≤ 3 := by
  by_cases hheavy : ∃ e ∈ E, stopWeight e = 2
  · obtain ⟨e, he, h2⟩ := hheavy
    rw [stop_value_of_heavy hE he h2]
    omega
  · have h1 : ∀ e ∈ E, stopWeight e ≤ 1 := by
      intro e he
      have h := (stopWeight_facts (hE.1 he)).1
      have hne : stopWeight e ≠ 2 := fun h2 => hheavy ⟨e, he, h2⟩
      omega
    exact (stop_value_of_light hE h1).2

/-- A cycle-separated family of at most two pairs of `T` has value at most `2`. -/
theorem stop_value_le_two {E : Finset Pair} (hE : EdgeAbove.CycleSeparated caterpillar E)
    (hcard : E.card ≤ 2) : value stopWeight E ≤ 2 := by
  by_cases hheavy : ∃ e ∈ E, stopWeight e = 2
  · obtain ⟨e, he, h2⟩ := hheavy
    rw [stop_value_of_heavy hE he h2]
  · have h1 : ∀ e ∈ E, stopWeight e ≤ 1 := by
      intro e he
      have h := (stopWeight_facts (hE.1 he)).1
      have hne : stopWeight e ≠ 2 := fun h2 => hheavy ⟨e, he, h2⟩
      omega
    exact (stop_value_of_light hE h1).1.trans hcard

/-- `T` displays no quartet of `Q`. -/
theorem stop_baseline_repertoire :
    repertoire stopQuartets (Realization.graph caterpillar ∅) = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro q hq
  simp only [repertoire, Finset.mem_filter] at hq
  have hnot : ∀ q ∈ stopQuartets.toFinset, q.induced caterpillar = false := by decide
  have hd := (Realization.baseline_displays_iff caterpillar caterpillar_wellLabelled q).mp hq.2
  rw [hnot q hq.1] at hd
  exact Bool.false_ne_true hd

/-- The quartets of `Q` satisfied by a network are those it displays, since `T` displays none of
them: for `T` and `Q`, the numbers of quartets satisfied and displayed are the same. -/
theorem stop_novel_eq (N : RootedNetwork) :
    novel caterpillar stopQuartets N = repertoire stopQuartets N := by
  rw [novel, stop_baseline_repertoire, Finset.sdiff_empty]

/-- The canonical network of a cycle-separated family `E` of pairs of `T` is built on `T`, has
`|E|` reticulations, and displays as many quartets of `Q` as the value of `E`: by Lemma 1, the
quartets of `Q` it satisfies, as `T` displays none. -/
theorem stop_canonical_score {E : Finset Pair} (hE : EdgeAbove.CycleSeparated caterpillar E) :
    (Realization.graph caterpillar E).AnchoredExtension caterpillar ∧
      (Realization.graph caterpillar E).reticulationCount = E.card ∧
      score stopQuartets (repertoire stopQuartets (Realization.graph caterpillar E)) =
        value stopWeight E := by
  refine ⟨⟨Realization.levelOne caterpillar caterpillar_wellLabelled E hE,
      ⟨Realization.supportEdges caterpillar E,
        ⟨Realization.support caterpillar caterpillar_wellLabelled E hE⟩⟩⟩,
    Realization.reticulationCount_eq_card caterpillar E hE, ?_⟩
  rw [score_offset stopQuartets _ _
    (baseline_subset caterpillar caterpillar_wellLabelled stopQuartets E hE)]
  change _ + score stopQuartets (novel caterpillar stopQuartets (Realization.graph caterpillar E))
    = _
  rw [novel_score_value caterpillar caterpillar_wellLabelled stopQuartets E hE,
    stop_baseline_repertoire]
  simp [score]

/-- A network built on `T` displays as many quartets of `Q` as the value of its family of added
edges, which is cycle-separated and has one pair for each reticulation. -/
theorem stop_network_score {N : RootedNetwork} (hN : N.AnchoredExtension caterpillar) :
    ∃ E, EdgeAbove.CycleSeparated caterpillar E ∧ E.card = N.reticulationCount ∧
      score stopQuartets (repertoire stopQuartets N) = value stopWeight E := by
  classical
  -- `N` is isomorphic to the canonical network of its added edges
  obtain ⟨S, ⟨H⟩⟩ := hN.2
  have hF := H.extracted_separated hN.1
  have hNF := Realization.levelOne caterpillar caterpillar_wellLabelled H.extracted hF
  obtain ⟨i⟩ := H.canonical_iso hN.1
  refine ⟨H.extracted, hF, ?_, ?_⟩
  · rw [i.reticulationCount_eq hN.1 hNF, Realization.reticulationCount_eq_card _ _ hF]
  · rw [repertoire_iso stopQuartets hN.1 hNF i]
    exact (stop_canonical_score hF).2.2

/-- The value of a family of admissible pairs of `T`, in computable form. -/
theorem stop_value_eq {E : Finset Pair} (h1 : E ⊆ EdgeAbove.candidates caterpillar) :
    value stopWeight E = ∑ e ∈ E, stopWeightSum e :=
  Finset.sum_congr rfl (fun _ he => stopWeight_eq (h1 he))

/-- One edge: the pair `(A, F)` is admissible and has weight `2`. -/
theorem stop_heavy_family :
    EdgeAbove.CycleSeparated caterpillar {stopHeavyPair} ∧
      ({stopHeavyPair} : Finset Pair).card = 1 ∧ value stopWeight {stopHeavyPair} = 2 := by
  have h1 : ({stopHeavyPair} : Finset Pair) ⊆ EdgeAbove.candidates caterpillar := by
    decide +kernel
  refine ⟨EdgeAbove.separated_of_pairwise h1 (by decide +kernel), rfl, ?_⟩
  rw [stop_value_eq h1]
  decide +kernel

/-- Two edges: the pairs `(A, F)` and `(G, H)` have disjoint cycles, and the triangle at `(G,H)`
has weight `0`. -/
theorem stop_heavy_cherry_family :
    EdgeAbove.CycleSeparated caterpillar {stopHeavyPair, stopCherryPair} ∧
      ({stopHeavyPair, stopCherryPair} : Finset Pair).card = 2 ∧
      value stopWeight {stopHeavyPair, stopCherryPair} = 2 := by
  have h1 : ({stopHeavyPair, stopCherryPair} : Finset Pair) ⊆ EdgeAbove.candidates caterpillar := by
    decide +kernel
  refine ⟨EdgeAbove.separated_of_pairwise h1 (by decide +kernel), by decide, ?_⟩
  rw [stop_value_eq h1]
  decide +kernel

/-- Three edges: the pairs `(A, C)`, `((D,(E,(F,(G,H)))), E)` and `((F,(G,H)), H)` have
vertex-disjoint cycles and weight `1` each. -/
theorem stop_light_family :
    EdgeAbove.CycleSeparated caterpillar stopLightPairs ∧ stopLightPairs.card = 3 ∧
      value stopWeight stopLightPairs = 3 := by
  have h1 : stopLightPairs ⊆ EdgeAbove.candidates caterpillar := by decide +kernel
  refine ⟨EdgeAbove.separated_of_pairwise h1 (by decide +kernel), by decide, ?_⟩
  rw [stop_value_eq h1]
  decide +kernel

/-- The best scores for `T = (A,(B,(C,(D,(E,(F,(G,H)))))))` and
`Q = {AF|CG, AF|CG, AC|BD, AE|DF, AH|FG}`, counted with multiplicity. Since `T` displays no quartet
of `Q`, the quartets of `Q` displayed by a network are those it satisfies (`stop_novel_eq`).
* `T` itself displays no quartet of `Q`, and neither does any network built on `T` with no
  reticulation;
* some network built on `T` with exactly one reticulation displays `2`;
* some network built on `T` with exactly two reticulations displays `2`;
* some network built on `T` with exactly three reticulations displays `3`;
* every network built on `T` with at most two reticulations displays at most `2`;
* every network built on `T` displays at most `3`. -/
theorem caterpillar_scores :
    (∃ N : RootedNetwork, N.AnchoredExtension caterpillar ∧ N.reticulationCount = 0 ∧
      score stopQuartets (repertoire stopQuartets N) = 0) ∧
    (∀ N : RootedNetwork, N.AnchoredExtension caterpillar → N.reticulationCount = 0 →
      score stopQuartets (repertoire stopQuartets N) = 0) ∧
    (∃ N : RootedNetwork, N.AnchoredExtension caterpillar ∧ N.reticulationCount = 1 ∧
      score stopQuartets (repertoire stopQuartets N) = 2) ∧
    (∃ N : RootedNetwork, N.AnchoredExtension caterpillar ∧ N.reticulationCount = 2 ∧
      score stopQuartets (repertoire stopQuartets N) = 2) ∧
    (∃ N : RootedNetwork, N.AnchoredExtension caterpillar ∧ N.reticulationCount = 3 ∧
      score stopQuartets (repertoire stopQuartets N) = 3) ∧
    (∀ N : RootedNetwork, N.AnchoredExtension caterpillar → N.reticulationCount ≤ 2 →
      score stopQuartets (repertoire stopQuartets N) ≤ 2) ∧
    (∀ N : RootedNetwork, N.AnchoredExtension caterpillar →
      score stopQuartets (repertoire stopQuartets N) ≤ 3) := by
  have hempty : EdgeAbove.CycleSeparated caterpillar ∅ := by
    simp [EdgeAbove.CycleSeparated]
  obtain ⟨h0N, h0ret, h0score⟩ := stop_canonical_score hempty
  have hnet {E : Finset Pair} {k z : ℕ}
      (h : EdgeAbove.CycleSeparated caterpillar E ∧ E.card = k ∧ value stopWeight E = z) :
      ∃ N : RootedNetwork, N.AnchoredExtension caterpillar ∧ N.reticulationCount = k ∧
        score stopQuartets (repertoire stopQuartets N) = z := by
    obtain ⟨hN, hret, hscore⟩ := stop_canonical_score h.1
    exact ⟨_, hN, hret.trans h.2.1, hscore.trans h.2.2⟩
  refine ⟨⟨_, h0N, h0ret, by rw [h0score]; rfl⟩, ?_, hnet stop_heavy_family,
    hnet stop_heavy_cherry_family, hnet stop_light_family, ?_, ?_⟩
  · intro N hN hret
    obtain ⟨E, _, hEk, hscore⟩ := stop_network_score hN
    rw [hret, Finset.card_eq_zero] at hEk
    rw [hscore, hEk]
    rfl
  · intro N hN hret
    obtain ⟨E, hE, hEk, hscore⟩ := stop_network_score hN
    rw [hscore]
    exact stop_value_le_two hE (hEk ▸ hret)
  · intro N hN
    obtain ⟨E, hE, _, hscore⟩ := stop_network_score hN
    rw [hscore]
    exact stop_value_le_three hE

/-- The best scores with exactly `k` reticulations, for `k = 0, 1, 2, 3`: `0`, `2`, `2`, `3`. -/
theorem caterpillar_bestExact :
    bestExact caterpillar stopQuartets 0 = 0 ∧ bestExact caterpillar stopQuartets 1 = 2 ∧
      bestExact caterpillar stopQuartets 2 = 2 ∧ bestExact caterpillar stopQuartets 3 = 3 := by
  obtain ⟨h0, h0le, h1, h2, h3, hle2, hle3⟩ := caterpillar_scores
  refine ⟨IsGreatest.csSup_eq ⟨h0, ?_⟩, IsGreatest.csSup_eq ⟨h1, ?_⟩,
    IsGreatest.csSup_eq ⟨h2, ?_⟩, IsGreatest.csSup_eq ⟨h3, ?_⟩⟩
  · rintro s ⟨N, hN, hret, rfl⟩
    exact (h0le N hN hret).le
  · rintro s ⟨N, hN, hret, rfl⟩
    exact hle2 N hN (by omega)
  · rintro s ⟨N, hN, hret, rfl⟩
    exact hle2 N hN (by omega)
  · rintro s ⟨N, hN, -, rfl⟩
    exact hle3 N hN

/-- The best scores with at most `k` reticulations, for `k = 0, 1, 2, 3`: `0`, `2`, `2`, `3`. -/
theorem caterpillar_bestAtMost :
    bestAtMost caterpillar stopQuartets 0 = 0 ∧ bestAtMost caterpillar stopQuartets 1 = 2 ∧
      bestAtMost caterpillar stopQuartets 2 = 2 ∧ bestAtMost caterpillar stopQuartets 3 = 3 := by
  obtain ⟨⟨N0, hN0, hr0, hs0⟩, h0le, ⟨N1, hN1, hr1, hs1⟩, -, ⟨N3, hN3, hr3, hs3⟩, hle2, hle3⟩ :=
    caterpillar_scores
  refine ⟨IsGreatest.csSup_eq ⟨⟨N0, hN0, hr0.le, hs0⟩, ?_⟩,
    IsGreatest.csSup_eq ⟨⟨N1, hN1, hr1.le, hs1⟩, ?_⟩,
    IsGreatest.csSup_eq ⟨⟨N1, hN1, by omega, hs1⟩, ?_⟩,
    IsGreatest.csSup_eq ⟨⟨N3, hN3, hr3.le, hs3⟩, ?_⟩⟩
  · rintro s ⟨N, hN, hret, rfl⟩
    exact (h0le N hN (by omega)).le
  · rintro s ⟨N, hN, hret, rfl⟩
    exact hle2 N hN (by omega)
  · rintro s ⟨N, hN, hret, rfl⟩
    exact hle2 N hN hret
  · rintro s ⟨N, hN, -, rfl⟩
    exact hle3 N hN

/-- The root rows of every array of the recurrence of Section 2.4 for `T` and `Q`, with the weights
`s_e` of Equation (1): `M[r][0] = {0}`, `M[r][1] = {2}`, `M[r][2] = {2}` and `M[r][3] = {3}`. -/
theorem caterpillar_root_rows (M : Address → ℕ → Finset ℕ)
    (hM : BudgetDP.Array caterpillar stopWeight M) :
    M [] 0 = {0} ∧ M [] 1 = {2} ∧ M [] 2 = {2} ∧ M [] 3 = {3} := by
  have hfeas {E : Finset Pair} (hE : EdgeAbove.CycleSeparated caterpillar E) :
      FeasibleBelow caterpillar [] E := ⟨hE, fun _ _ => List.nil_prefix⟩
  obtain ⟨hH, hHc, hHv⟩ := stop_heavy_family
  obtain ⟨hC, hCc, hCv⟩ := stop_heavy_cherry_family
  obtain ⟨hL, hLc, hLv⟩ := stop_light_family
  refine ⟨BudgetDP.root_row_eq_singleton hM (feasible_empty _ _) rfl rfl ?_,
    BudgetDP.root_row_eq_singleton hM (hfeas hH) hHc hHv ?_,
    BudgetDP.root_row_eq_singleton hM (hfeas hC) hCc hCv ?_,
    BudgetDP.root_row_eq_singleton hM (hfeas hL) hLc hLv ?_⟩
  · intro F _ hF
    rw [Finset.card_eq_zero.mp hF]
    rfl
  · exact fun F hF hFk => stop_value_le_two hF.1 (by omega)
  · exact fun F hF hFk => stop_value_le_two hF.1 (by omega)
  · exact fun F hF _ => stop_value_le_three hF.1

/-- Section 2.4's stopping rule on the array, for `T` and `Q`: filling the columns in order of
increasing `k` until the score no longer improves stops at `m = 1`, with score `2`, while the
column of `k = 3` holds `3`. -/
theorem caterpillar_array_stops (M : Address → ℕ → Finset ℕ)
    (hM : BudgetDP.Array caterpillar stopWeight M) :
    StopsAt (fun k => (M [] k).sup id) 1 ∧ (M [] 1).sup id < (M [] 3).sup id := by
  obtain ⟨h0, h1, h2, h3⟩ := caterpillar_root_rows M hM
  refine ⟨⟨fun j hj => ?_, ?_⟩, ?_⟩
  · obtain rfl : j = 0 := by omega
    change (M [] 0).sup id < (M [] 1).sup id
    simp [h0, h1]
  · change (M [] 2).sup id ≤ (M [] 1).sup id
    simp [h1, h2]
  · simp [h1, h3]

end Counterexamples

/-- Section 2.4's stopping rule can stop before a better score, for exact numbers of
reticulations. For `T = (A,(B,(C,(D,(E,(F,(G,H)))))))` and
`Q = {AF|CG, AF|CG, AC|BD, AE|DF, AH|FG}`, the best scores with exactly `0, 1, 2, 3` reticulations
are `0, 2, 2, 3`: the rule stops at `m = 1`, and three reticulations give a better score. -/
theorem not_exactStoppingRule : ¬ ExactStoppingRule := by
  intro h
  obtain ⟨h0, h1, h2, h3⟩ := Counterexamples.caterpillar_bestExact
  have hstop :
      StopsAt (bestExact Counterexamples.caterpillar Counterexamples.stopQuartets) 1 := by
    refine ⟨fun j hj => ?_, ?_⟩
    · obtain rfl : j = 0 := by omega
      change bestExact _ _ 0 < bestExact _ _ 1
      rw [h0, h1]
      omega
    · change bestExact _ _ 2 ≤ bestExact _ _ 1
      rw [h2, h1]
  have h31 := h _ Counterexamples.caterpillar_wellLabelled _ 1 hstop 3 (by omega)
  rw [h3, h1] at h31
  omega

/-- Section 2.4's stopping rule can stop before a better score, for "at most k" reticulations. For
the same `T` and `Q`, the best scores with at most `0, 1, 2, 3` reticulations are `0, 2, 2, 3`: the
rule stops at `m = 1`, and a network with three reticulations displays more quartets of `Q`. -/
theorem not_atMostStoppingRule : ¬ AtMostStoppingRule := by
  intro h
  obtain ⟨h0, h1, h2, h3⟩ := Counterexamples.caterpillar_bestAtMost
  have hstop :
      StopsAt (bestAtMost Counterexamples.caterpillar Counterexamples.stopQuartets) 1 := by
    refine ⟨fun j hj => ?_, ?_⟩
    · obtain rfl : j = 0 := by omega
      change bestAtMost _ _ 0 < bestAtMost _ _ 1
      rw [h0, h1]
      omega
    · change bestAtMost _ _ 2 ≤ bestAtMost _ _ 1
      rw [h2, h1]
  have h31 := h _ Counterexamples.caterpillar_wellLabelled _ 1 hstop 3
  rw [h3, h1] at h31
  omega

end Camus
