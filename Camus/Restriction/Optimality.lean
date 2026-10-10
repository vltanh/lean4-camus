module

public import Camus.Restriction.Construction
public import Camus.DP.Theorem1
public import Camus.Network.Reticulations

/-!
# Section 2.4: the networks `N_k` are optimal

Section 2.4 of the paper asks for networks `N_1, …, N_m` such that all are level-1, all contain
`T`, `N_k` has exactly `k` non-tree edges, and each maximizes the number of quartets of `Q` subject
to these constraints. This file proves this for the formalization's recurrence (`BudgetDP.Array`)
with the weights `s_e` of Equation (1), assuming Observation 2 of Warnow–Tabatabaee–Evans, which
enters through Lemma 1: the root row `M[r][k]` holds the number of quartets satisfied by a network
built on `T` with exactly `k` reticulations, and no network built on `T` with exactly `k`
reticulations satisfies more. The paper's stopping rule (add columns until the score stops
improving) is not formalized.

## Main results

* `BudgetDP.exact_graph_optimal`: the networks `N_k`.
* `BudgetDP.high_budget_empty`: rows of budget larger than `n − 1` are empty, so at most `n − 1`
  columns are needed.
* `BudgetDP.array_row_card`: every row has at most one value.
* `BudgetDP.allocated_source_score`: a distribution of the budget over the subtrees hanging off a
  cycle is scored by Equation (4) or (5) evaluated on the allocated rows.
-/

@[expose] public section

namespace Camus.BudgetDP

open DynamicProgramming

/-- Every knapsack row has at most one value. -/
 theorem forest_row_card (M : Address → ℕ → Finset ℕ) (rs : List Address) (k : ℕ) :
    (forest M rs k).card ≤ 1 := by
  cases rs with
  | nil => simp only [forest]; split_ifs <;> simp
  | cons r rs => exact best_card_le_one _

/-- Every row of an array satisfying the recurrence has at most one value. -/
 theorem array_row_card (t : PhyloTree) (w : Pair → ℕ) (M : Address → ℕ → Finset ℕ)
    (hM : Array t w M) {v : Address} (hv : v ∈ t.nodes) (k : ℕ) :
    (M v k).card ≤ 1 := by
  rw [hM v hv k]
  exact best_card_le_one _

/-- If `z ∈ M[v][k]`, the maximum of the row is `z`. -/
 theorem row_sup_eq (t : PhyloTree) (w : Pair → ℕ) (M : Address → ℕ → Finset ℕ)
    (hM : Array t w M) {v : Address} (hv : v ∈ t.nodes) {k z : ℕ} (hz : z ∈ M v k) :
    (M v k).sup id=z := by
  apply Nat.le_antisymm
  · apply Finset.sup_le
    intro x hx
    rw [hM v hv k] at hx hz
    exact (mem_best.mp hz).2 x (mem_best.mp hx).1
  · exact Finset.le_sup (f := id) hz

/-- A distribution of the budget over the subtrees `r` hanging off the cycle of `e`, with budget
`b r` and value `s r ∈ M[r][b r]`, has total value `s_dp` of Equation (4) or (5) (`sdp`), evaluated
with `M[r]` replaced by the value of row `b r` (`DynamicProgramming.hanging_score`). -/
 theorem allocated_source_score (t : PhyloTree) (w : Pair → ℕ)
    (M : Address → ℕ → Finset ℕ) (hM : Array t w M)
    {e : Pair} (he : EdgeAbove.Admissible t e) (b s : Address → ℕ)
    (hs : ∀ r ∈ hanging t e, s r ∈ M r (b r)) :
    (∑ r ∈ hanging t e, s r) =
      DynamicProgramming.sdp t (fun r => (M r (b r)).sup id) e := by
  rw [DynamicProgramming.hanging_score t _ e he]
  apply Finset.sum_congr rfl
  intro r hr
  exact (row_sup_eq t w M hM (Finset.mem_filter.mp hr).1 (hs r hr)).symm

/-- Section 2.4: the networks `N_k`. Let `M` satisfy the recurrence `BudgetDP.Array` with the
weights `s_e` of Equation (1), and assume Observation 2 of Warnow–Tabatabaee–Evans. For every value
`z` in the root row `M[r][k]` there is a family `E` of added edges whose canonical network
`Realization.graph t E` is built on `T`, has exactly `k` reticulations and satisfies `z` quartets of
`Q` (with multiplicity); every network built on `T` with exactly `k` reticulations satisfies at
most `z` quartets of `Q`, and displays at most as many as `Realization.graph t E`. The recurrence is
the formalization's own (the paper gives none), following the paper's description of `M[v, k]`. -/
 theorem exact_graph_optimal (observation2 : External.WarnowTabatabaeeEvansObservation2)
    (t : PhyloTree) (ht : t.WellLabelled) (Q : Multiset Quartet)
    (M : Address → ℕ → Finset ℕ) (hM : Array t (edgeWeight t Q) M)
    {k z : ℕ} (hz : z ∈ M [] k) :
    ∃ E : Finset Pair,
      (Realization.graph t E).AnchoredExtension t ∧
      (Realization.graph t E).reticulationCount=k ∧
      score Q (novel t Q (Realization.graph t E))=z ∧
      (∀ N : RootedNetwork, N.AnchoredExtension t → N.reticulationCount=k →
        score Q (novel t Q N) ≤ z) ∧
      (∀ N : RootedNetwork, N.AnchoredExtension t → N.reticulationCount=k →
        score Q (repertoire Q N) ≤ score Q (repertoire Q (Realization.graph t E))) := by
  classical
  -- `z` is the value of a feasible family `E` of `k` edges, and no such family has a larger value
  obtain ⟨E,hE,hEk,hEz,hupper⟩ := exact_optimal t (edgeWeight t Q) M hM t.root_mem_nodes hz
  have hNE := Realization.levelOne t ht E hE.1
  -- by Lemma 1, the canonical network of `E` satisfies `value E = z` quartets
  have hscoreE := (novel_score_value observation2 t ht Q E hE.1).trans hEz
  -- a network built on `T` is isomorphic to the canonical network of its added edges, which has
  -- as many reticulations and satisfies as many quartets
  have hnovel N (hN : N.AnchoredExtension t) (hNk : N.reticulationCount=k) :
      score Q (novel t Q N) ≤ z := by
    obtain ⟨S,⟨H⟩⟩ := hN.2
    have hF := H.extracted_separated hN.1
    have hNF := Realization.levelOne t ht H.extracted hF
    obtain ⟨i⟩ := H.canonical_iso hN.1
    have hrep := repertoire_iso Q hN.1 hNF i
    have hnovelEq : novel t Q N=novel t Q (Realization.graph t H.extracted) := by
      unfold novel
      rw [hrep]
    have hcard : H.extracted.card=k := by
      rw [← Realization.reticulationCount_eq_card t H.extracted hF,
        ← i.reticulationCount_eq hN.1 hNF,hNk]
    rw [hnovelEq,novel_score_value observation2 t ht Q H.extracted hF]
    exact hupper H.extracted ⟨hF,fun _ _=>List.nil_prefix⟩ hcard
  refine ⟨E,⟨hNE,⟨Realization.supportEdges t E,⟨Realization.support t ht E hE.1⟩⟩⟩,
    (Realization.reticulationCount_eq_card t E hE.1).trans hEk,hscoreE,hnovel,?_⟩
  -- the quartets displayed are those of `T` and those satisfied, and every network built on `T`
  -- displays the quartets of `T`
  intro N hN hNk
  obtain ⟨S,⟨H⟩⟩ := hN.2
  have hF := H.extracted_separated hN.1
  have hNF := Realization.levelOne t ht H.extracted hF
  obtain ⟨i⟩ := H.canonical_iso hN.1
  have hrep := repertoire_iso Q hN.1 hNF i
  have hbaseN : repertoire Q (Realization.graph t ∅) ⊆ repertoire Q N := by
    rw [hrep]
    exact baseline_subset t ht Q H.extracted hF
  have hbaseE := baseline_subset t ht Q E hE.1
  rw [score_offset Q _ _ hbaseN,score_offset Q _ _ hbaseE]
  have hle : score Q (novel t Q N) ≤ score Q (novel t Q (Realization.graph t E)) := by
    rw [hscoreE]
    exact hnovel N hN hNk
  exact Nat.add_le_add_left hle _

/-- Section 2.4: "a level-1 phylogenetic network on n leaves will not have more than n−1
reticulations". If `M` satisfies the recurrence, the rows of budget `k > n − 1` are empty, so the
array needs at most `n − 1` budget columns. -/
 theorem high_budget_empty (t : PhyloTree) (w : Pair → ℕ) (M : Address → ℕ → Finset ℕ)
    (hM : Array t w M) {v : Address} (hv : v ∈ t.nodes) {k : ℕ}
    (hk : t.labels.length-1 < k) : M v k=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨E,hE,hEk,_⟩ := (array_correct t w M hM hv).1 k z hz
  have hbound := EdgeAbove.separated_card_bound hE.1
  omega

end Camus.BudgetDP
