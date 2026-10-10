module

public import Camus.Pipelines.Counterexample

/-!
# Section 3.2: the true network need not be the unique optimum

Section 3.2 of the paper argues that the SNP pipeline recovers the true network `N`: once the
constraint tree `t` is one of `N`'s displayed trees and `Q` is a multiset version of `Q(N_r)`,
"CAMUS will add the correct reticulations and return N, since this is the unique network that can
satisfy all the quartets in Q(N_r), and hence N will be the unique solution to CAMUS'
optimization problem". This is false (the report's E7): a network that displays more quartets
than `N` ties it, since the objective only counts the quartets of `Q`.

## Main results

* `UniqueOptimum` (defined with the shared definitions in `Camus/Defs.lean`): the claim. If `N` is built on `t` and the quartets of `Q` are exactly those that
  `N` displays, then every network built on `t` that displays as many quartets of `Q` as any other
  is isomorphic to `N`.
* `not_uniqueOptimum`: the claim fails. The five-leaf tree `T = (O,((B,A),(D,C)))`, as a network
  with no added edge, displays its five quartets; the network obtained by adding one edge above
  `(A, C)` is built on `T` and displays them too, so it is optimal, but it has a reticulation and
  `T` has none (`Counterexamples.graph_uniqueness_counterexample`).
* `camus_may_add_edge`: on this input the dynamic program itself may return the network with the
  added edge: every weight is zero, so a backtracking trace may take either branch at the vertex
  above `A` and `C`.
* `recovery`: the claim holds with two more hypotheses: `N` is identifiable under inclusion (every
  network built on `t` that displays every quartet `N` displays, with no more reticulations than
  `N`, is isomorphic to `N`), and the optimal network has the fewest reticulations among the
  optimal networks built on `t`.
* `tree_identifiable`: the tree itself satisfies the first of these hypotheses, so `recovery`
  applies to the counterexample, and there selects the tree.

Optimality is measured by the number of quartets of `Q` displayed. For a fixed `t` it differs from
the number of quartets satisfied (CAMUS's objective in Theorem 1) by the number of quartets of `Q`
that `t` induces, so both objectives have the same optimal networks.
-/

@[expose] public section

namespace Camus

open DynamicProgramming

/-- Section 3.2's uniqueness claim is false (the report's E7). Take for `t` and for the true
network the five-leaf tree `(O,((B,A),(D,C)))`, and for `Q` its five quartets. The network obtained
by adding one edge above `(A, C)` is built on `t`, displays the five quartets, and so is optimal,
but it has one reticulation and the true network none, so the two are not isomorphic. -/
theorem not_uniqueOptimum : ¬ UniqueOptimum := by
  intro h
  obtain ⟨hN, hP, hN0, hP1, -, hPscore⟩ := Counterexamples.graph_uniqueness_counterexample
  have hQ (q : Quartet) : q ∈ Counterexamples.data ↔
      (Realization.graph Counterexamples.constraint ∅).DisplaysQuartet q := by
    rw [Realization.baseline_displays_iff _ Counterexamples.constraint_wellLabelled,
      Counterexamples.data_is_exact]
  obtain ⟨i⟩ := h _ Counterexamples.constraint_wellLabelled _ hN _ hQ _ hP
    (fun R _ => hPscore ▸ score_le_card _ _)
  have := i.reticulationCount_eq hP.1 hN.1
  omega

namespace Counterexamples

/-- On the input of `not_uniqueOptimum`, every weight of Equation (1) is zero: the tree `T`
already displays every quartet of `data`, so no single added edge satisfies one. -/
theorem edgeWeight_data (e : Pair) : edgeWeight constraint data e = 0 := by
  classical
  unfold edgeWeight
  apply Finset.sum_eq_zero
  intro q _
  have hn : q ∉ novel constraint data (Realization.graph constraint {e}) := by
    intro h
    simp only [novel, Finset.mem_sdiff] at h
    apply h.2
    rw [graphData_exact]
    exact (Finset.mem_filter.mp h.1).1
  simp [hn]

/-- With a zero array, the hanging-subproblem sums of Equations (4) and (5) are zero. -/
theorem sdp_zero (e : Pair) : sdp constraint (fun _ => 0) e = 0 := by
  unfold sdp sdpGhost sdpCross
  split_ifs <;> simp

/-- On the input of `not_uniqueOptimum`, the zero array satisfies the recurrence. -/
theorem array_data : Array constraint (edgeWeight constraint data) (fun _ => 0) := by
  intro v hv
  obtain ⟨sub, hsub⟩ := (PhyloTree.mem_nodes_iff _ _).mp hv
  rw [hsub]
  cases sub with
  | leaf a => rfl
  | fork l r =>
    have hs : s constraint (edgeWeight constraint data) (fun _ => 0) v = 0 := by
      unfold s
      apply le_antisymm _ (Nat.zero_le _)
      apply Finset.sup_le
      intro e _
      simp [edgeWeight_data, sdp_zero]
    change (0 : ℕ) = max (0 + 0) _
    rw [hs]
    rfl

/-- On the input of `not_uniqueOptimum`, backtracking through the zero array may take, at the
vertex above `A` and `C`, the branch that adds the edge above `(A, C)`: its value `0` ties with
the branch that adds nothing. -/
theorem trace_extraPair :
    Trace constraint (edgeWeight constraint data) (fun _ => 0) [] {extraPair} := by
  have hhang : hanging constraint extraPair =
      {[true, false, false], [true, false, true], [true, true, false], [true, true, true]} := by
    decide
  have hg := Trace.gall (t := constraint) (weight := edgeWeight constraint data)
    (M := fun _ => 0) [true] extraPair (fun _ => ∅) (by decide)
    (by
      intro r hr
      rw [hhang] at hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [Trace.leaf _ 1 rfl, Trace.leaf _ 0 rfl, Trace.leaf _ 3 rfl, Trace.leaf _ 2 rfl])
    (by simp [edgeWeight_data, sdp_zero])
  have hf := Trace.fork (t := constraint) (weight := edgeWeight constraint data)
    (M := fun _ => 0) [] (.leaf 4) (.fork (.fork (.leaf 1) (.leaf 0)) (.fork (.leaf 3) (.leaf 2)))
    ∅ _ rfl (Trace.leaf [false] 4 rfl) hg rfl
  have hE : (∅ : Finset Pair) ∪ insert extraPair
      ((hanging constraint extraPair).biUnion fun _ => ∅) = {extraPair} := by
    ext x
    simp
  rw [hE] at hf
  exact hf

end Counterexamples

/-- Section 3.2: the dynamic program itself may return a network other than the true one. On
the input of `not_uniqueOptimum`, where the true network is the tree `T` with no added edge and
`Q` its five quartets, the recurrence has a solution `M` and a backtracking trace through it that
adds the edge above `(A, C)`, so that the output has one reticulation. -/
theorem camus_may_add_edge :
    ∃ M, Array Counterexamples.constraint
        (edgeWeight Counterexamples.constraint Counterexamples.data) M ∧
      Trace Counterexamples.constraint
        (edgeWeight Counterexamples.constraint Counterexamples.data) M []
        {Counterexamples.extraPair} ∧
      (Realization.graph Counterexamples.constraint {Counterexamples.extraPair}).reticulationCount
        = 1 :=
  ⟨_, Counterexamples.array_data, Counterexamples.trace_extraPair,
    Counterexamples.graph_uniqueness_counterexample.2.2.2.1⟩

/-- Section 3.2, corrected. Let the network `N` be built on `t`, and let the quartets of `Q` be
exactly those that `N` displays. Assume that `N` is identifiable under inclusion: every network
built on `t` that displays every quartet that `N` displays, with no more reticulations than `N`, is
isomorphic to `N`. Then every network `P` built on `t` that displays as many quartets of `Q` as any
network built on `t`, and has the fewest reticulations among such networks, is isomorphic to
`N`. -/
theorem recovery (t : PhyloTree) (N : RootedNetwork) (hN : N.AnchoredExtension t)
    (Q : Multiset Quartet) (hQ : ∀ q, q ∈ Q ↔ N.DisplaysQuartet q)
    (identifiable : ∀ P : RootedNetwork, P.AnchoredExtension t →
      (∀ q, N.DisplaysQuartet q → P.DisplaysQuartet q) →
      P.reticulationCount ≤ N.reticulationCount → Nonempty (P.Iso N))
    (P : RootedNetwork) (hP : P.AnchoredExtension t)
    (optimal : ∀ R : RootedNetwork, R.AnchoredExtension t →
      score Q (repertoire Q R) ≤ score Q (repertoire Q P))
    (fewest : ∀ R : RootedNetwork, R.AnchoredExtension t →
      (∀ R' : RootedNetwork, R'.AnchoredExtension t →
        score Q (repertoire Q R') ≤ score Q (repertoire Q R)) →
      P.reticulationCount ≤ R.reticulationCount) :
    Nonempty (P.Iso N) := by
  classical
  -- `N` displays every quartet of `Q`, so it attains the largest possible score, `|Q|`
  have hNscore : score Q (repertoire Q N) = Q.card := by
    apply (score_eq_card_iff Q _).mpr
    intro q hq
    simp only [repertoire, Finset.mem_filter]
    exact ⟨hq, (hQ q).mp (Multiset.mem_toFinset.mp hq)⟩
  -- so `N` is optimal, and the optimal `P` attains `|Q|` too
  have hNopt : ∀ R : RootedNetwork, R.AnchoredExtension t →
      score Q (repertoire Q R) ≤ score Q (repertoire Q N) :=
    fun R _ => hNscore ▸ score_le_card _ _
  have hPscore : score Q (repertoire Q P) = Q.card :=
    le_antisymm (score_le_card _ _) (hNscore ▸ optimal N hN)
  -- hence `P` displays every quartet that `N` displays
  have hincl : ∀ q, N.DisplaysQuartet q → P.DisplaysQuartet q := by
    intro q hq
    have hmem := (score_eq_card_iff Q _).mp hPscore (Multiset.mem_toFinset.mpr ((hQ q).mpr hq))
    simp only [repertoire, Finset.mem_filter] at hmem
    exact hmem.2
  -- and has no more reticulations than the optimal `N`
  exact identifiable P hP hincl (fewest N hN hNopt)

/-- The tree `T`, as the network with no added edge, satisfies the hypothesis `identifiable` of
`recovery`: every network built on `T` with no reticulation is isomorphic to it. So `recovery`
applies to every input whose quartets are those of `T`, and there the network with the fewest
reticulations among the optimal ones is `T` itself, as the paper's Section 3.2 intends. -/
theorem tree_identifiable (t : PhyloTree) (ht : t.WellLabelled) :
    ∀ P : RootedNetwork, P.AnchoredExtension t →
      (∀ q, (Realization.graph t ∅).DisplaysQuartet q → P.DisplaysQuartet q) →
      P.reticulationCount ≤ (Realization.graph t ∅).reticulationCount →
      Nonempty (P.Iso (Realization.graph t ∅)) := by
  intro P hP _ hcount
  have hb : EdgeAbove.CycleSeparated t ∅ := by simp [EdgeAbove.CycleSeparated]
  obtain ⟨S, ⟨H⟩⟩ := hP.2
  have hF := H.extracted_separated hP.1
  obtain ⟨i⟩ := H.canonical_iso hP.1
  -- the number of reticulations of `P` is the number of its non-tree edges, here `0`
  have hzero : H.extracted.card = 0 := by
    have h := i.reticulationCount_eq hP.1 (Realization.levelOne t ht H.extracted hF)
    rw [Realization.reticulationCount_eq_card t H.extracted hF] at h
    rw [Realization.reticulationCount_eq_card t ∅ hb, Finset.card_empty] at hcount
    omega
  rw [Finset.card_eq_zero.mp hzero] at i
  exact ⟨i⟩

end Camus
