module

public import Camus.Preliminaries.Lemmas
public import Camus.DP.Correctness

/-!
# Theorem 1: the dynamic program is optimal

This file proves Theorem 1 (Section 2.2). Let `T` be a well-labelled tree and `Q` a multiset of
quartets. For any array `M` satisfying the recurrence (Equations (2)–(5), with the weights `s_e` of
Equation (1)) and any backtracking trace `E` from the root, the network `Realization.graph t E` is
built on `T`, satisfies `M[root]` quartets of `Q`, and satisfies at least as many quartets of `Q` as
any network built on `T`. The theorem is conditional on Observation 2 of Warnow, Tabatabaee and
Evans (2025), through Lemma 1.

## Main results

* `theorem1`: Theorem 1.
* `DynamicProgramming.novel_score_value`: by Lemma 1, the number of quartets of `Q` satisfied by
  the canonical network of a cycle-separated family `E` is the sum of the weights `s_e`, `e ∈ E`.
* `DynamicProgramming.edgeWeight_score`: `s_e` is the number of quartets of `Q` satisfied by
  `T + e` (Equation (1)).
* `DynamicProgramming.repertoire_iso`: isomorphic networks display the same quartets.

## Proof (the paper's)

The paper's proof has three steps; the formal proof adds a fourth, (d).

(a) The output is a level-1 network extending `T`. The trace `E` is feasible below the root, that
is, cycle-separated (`DynamicProgramming.trace_correct`, by `DynamicProgramming.fork_feasible` and
`DynamicProgramming.gall_feasible`). So `Realization.graph t E` is a rooted binary level-1 network
(`Realization.levelOne`) with `T` as support (`Realization.support`).

(b) `M[root]` is the number of quartets of `Q` satisfied by the output. The total weight of `E` is
`M[root]` (`DynamicProgramming.trace_correct`), and by Lemma 1 the number of quartets satisfied by
the output is the total weight of its edges (`DynamicProgramming.novel_score_value`, from
`DynamicProgramming.novel_disjoint_union` and Equation (1), `DynamicProgramming.edgeWeight_score`).
The paper also notes that by Lemma 1 the weights `s_e` can be computed independently; here they are
defined from the single-edge networks (`DynamicProgramming.edgeWeight`).

(c) Optimality, by strong induction over subtrees, using Lemma 2 and Equations (4)–(5):
`DynamicProgramming.array_upper` (see `Camus/DP/Correctness.lean`) bounds the total weight of every
family feasible below the root by `M[root]`.

(d) The paper identifies a network extending `T` with its set of added edges. Formally, a network
`N` built on `T`, with support subdivision `H`, is reduced to its family of pairs `H.extracted`.
This family is cycle-separated (`SupportSubdivision.extracted_separated`), and `N` is isomorphic to
its canonical network (`SupportSubdivision.canonical_iso`), so the two display the same quartets
(`DynamicProgramming.repertoire_iso`). By Lemma 1 and (c), `N` satisfies at most `M[root]`
quartets of `Q`.

Lemma 1 is used in (b) and (d), to identify the number of satisfied quartets with the total weight
of the added edges; the paper invokes it inside the induction to rule out double counting.

The last conclusion of `theorem1` compares the total number of quartets of `Q` displayed (the score
of Section 2.2). Every network built on `T` displays the quartets of `Q` induced by `T`
(`DynamicProgramming.baseline_subset`), so this number is the number of quartets of `Q` induced by
`T`, the same for all networks built on `T`, plus the number of satisfied quartets (`score_offset`).
-/

@[expose] public section

namespace Camus

namespace DynamicProgramming

/-- Equation (1): `s_e(u, w)` (`edgeWeight t Q e`) is the number of quartets of `Q`, counted with
multiplicity, satisfied by `T + e`, the network obtained by adding an edge above `e = (u, w)`. -/
theorem edgeWeight_score (t : PhyloTree) (Q : Multiset Quartet) (e : Pair) :
    edgeWeight t Q e = score Q (novel t Q (Realization.graph t {e})) := by
  exact (equation1 Q _).symm

/-- Lemma 1 as a count: for a cycle-separated family `E`, the number of quartets of `Q` (counted
with multiplicity) satisfied by `Realization.graph t E` is the sum of the weights `s_e`
(Equation (1)) over `e ∈ E`. Conditional on Observation 2. -/
theorem novel_score_value
    (observation2 : External.WarnowTabatabaeeEvansObservation2)
    (t : PhyloTree) (ht : t.WellLabelled) (Q : Multiset Quartet)
    (E : Finset Pair) (hE : EdgeAbove.CycleSeparated t E) :
    score Q (novel t Q (Realization.graph t E)) = value (edgeWeight t Q) E := by
  -- Lemma 1: the satisfied quartets are the disjoint union of those satisfied by the edges.
  obtain ⟨hunion, hdisjoint⟩ := novel_disjoint_union observation2 t ht Q E hE
  rw [hunion, score_disjoint_union Q E _ hdisjoint]
  apply Finset.sum_congr rfl
  intro e he
  exact (edgeWeight_score t Q e).symm

/-- Two isomorphic rooted binary level-1 networks display the same quartets of `Q`. -/
theorem repertoire_iso {N P : RootedNetwork} (Q : Multiset Quartet)
    (hN : N.RootedBinaryLevelOne) (hP : P.RootedBinaryLevelOne) (i : N.Iso P) :
    repertoire Q N = repertoire Q P := by
  classical
  ext q
  simp only [repertoire, Finset.mem_filter]
  exact and_congr_right (fun _ => i.displays_iff hN hP q)

end DynamicProgramming

/-- **Theorem 1** (`mthst9`). Let `T` be a well-labelled tree and `Q` a multiset of quartets. Let
`M` satisfy the recurrence of Section 2.2 (Equations (2)–(5), with the weights `s_e` of
Equation (1)), and let `E` be a backtracking trace of `M` from the root. Then the network
`Realization.graph t E`, obtained by adding the edges of `E` to `T`:
* is built on `T`: it is a rooted binary level-1 network with `T` as support;
* satisfies `M[root]` quartets of `Q`, counted with multiplicity;
* satisfies at least as many quartets of `Q` as any network built on `T`;
* displays at least as many quartets of `Q` as any network built on `T`. For a network built on
  `T`, the number of quartets of `Q` displayed is the number satisfied plus the number induced by
  `T`.

Conditional on Observation 2 of Warnow, Tabatabaee and Evans (2025). -/
theorem theorem1 (observation2 : External.WarnowTabatabaeeEvansObservation2)
    (t : PhyloTree) (ht : t.WellLabelled) (Q : Multiset Quartet)
    (M : Address → ℕ) (hM : DynamicProgramming.Array t (DynamicProgramming.edgeWeight t Q) M)
    (E : Finset DynamicProgramming.Pair)
    (trace : DynamicProgramming.Trace t (DynamicProgramming.edgeWeight t Q) M [] E) :
    (Realization.graph t E).AnchoredExtension t ∧
      score Q (DynamicProgramming.novel t Q (Realization.graph t E)) = M [] ∧
      (∀ N : RootedNetwork, N.AnchoredExtension t →
        score Q (DynamicProgramming.novel t Q N) ≤
          score Q (DynamicProgramming.novel t Q (Realization.graph t E))) ∧
      (∀ N : RootedNetwork, N.AnchoredExtension t →
        score Q (DynamicProgramming.repertoire Q N) ≤
          score Q (DynamicProgramming.repertoire Q (Realization.graph t E))) := by
  classical
  -- (a)–(c) for edge weights: `E` is feasible below the root with total weight `M[root]`, and
  -- every feasible family has total weight at most `M[root]`.
  obtain ⟨hE, hvalue, hupper⟩ := DynamicProgramming.trace_optimal t
    (DynamicProgramming.edgeWeight t Q) M hM (PhyloTree.root_mem_nodes t) trace
  -- (a) The network of the feasible family `E` is a rooted binary level-1 network.
  have hNE := Realization.levelOne t ht E hE.1
  -- (b) By Lemma 1, it satisfies as many quartets as the total weight of `E`, which is `M[root]`.
  have hscoreE := (DynamicProgramming.novel_score_value observation2 t ht Q E hE.1).trans hvalue
  -- (d) A network `N` built on `T` satisfies at most `M[root]` quartets.
  have hnovel : ∀ N : RootedNetwork, N.AnchoredExtension t →
      score Q (DynamicProgramming.novel t Q N) ≤
        score Q (DynamicProgramming.novel t Q (Realization.graph t E)) := by
    intro N hN
    obtain ⟨S, ⟨H⟩⟩ := hN.2
    -- Its family of pairs is cycle-separated, and `N` is isomorphic to the canonical network of
    -- this family, so the two satisfy the same quartets.
    have hF := H.extracted_separated hN.1
    have hNF := Realization.levelOne t ht H.extracted hF
    obtain ⟨i⟩ := H.canonical_iso hN.1
    have hrep := DynamicProgramming.repertoire_iso Q hN.1 hNF i
    have hnovelEq : DynamicProgramming.novel t Q N =
        DynamicProgramming.novel t Q (Realization.graph t H.extracted) := by
      unfold DynamicProgramming.novel
      rw [hrep]
    -- By Lemma 1 their number is the total weight of the family, at most `M[root]` by (c).
    rw [hnovelEq, DynamicProgramming.novel_score_value observation2 t ht Q H.extracted hF, hscoreE]
    exact hupper H.extracted ⟨hF, fun _ _ => List.nil_prefix⟩
  -- (a) The output is built on `T`, with the canonical support subdivision.
  refine ⟨⟨hNE, ⟨Realization.supportEdges t E, ⟨Realization.support t ht E hE.1⟩⟩⟩,
    hscoreE, hnovel, ?_⟩
  -- Displayed quartets: both networks display the quartets of `Q` induced by `T`, so their totals
  -- are that number plus the number of satisfied quartets.
  intro N hN
  obtain ⟨S, ⟨H⟩⟩ := hN.2
  have hF := H.extracted_separated hN.1
  have hNF := Realization.levelOne t ht H.extracted hF
  obtain ⟨i⟩ := H.canonical_iso hN.1
  have hrep := DynamicProgramming.repertoire_iso Q hN.1 hNF i
  have hbaseN : DynamicProgramming.repertoire Q (Realization.graph t ∅) ⊆
      DynamicProgramming.repertoire Q N := by
    rw [hrep]
    exact DynamicProgramming.baseline_subset t ht Q H.extracted hF
  have hbaseE := DynamicProgramming.baseline_subset t ht Q E hE.1
  rw [score_offset Q _ _ hbaseN, score_offset Q _ _ hbaseE]
  exact Nat.add_le_add_left (hnovel N hN) _

end Camus
