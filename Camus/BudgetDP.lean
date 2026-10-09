module

public import Camus.BudgetDPConstruction
public import Camus.MainTheorem
public import Camus.ReticulationBudget

@[expose] public section

namespace Camus.BudgetDP

open DynamicProgramming

 theorem row_sup_eq (t : PhyloTree) (w : Pair → ℕ) (M : Address → ℕ → Finset ℕ)
    (hM : Array t w M) {v : Address} (hv : v ∈ t.nodes) {k z : ℕ} (hz : z ∈ M v k) :
    (M v k).sup id=z := by
  apply Nat.le_antisymm
  · apply Finset.sup_le
    intro x hx
    rw [hM v hv k] at hx hz
    exact (mem_best.mp hz).2 x (mem_best.mp hx).1
  · exact Finset.le_sup (f := id) hz

/-- Each knapsack allocation is literally evaluated by Eq. 4 or Eq. 5 for
that allocation's subtree rows. This invokes the proved source-equations
hanging-forest bridge, preserving endpoint and ghost-donor cases. -/
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

/-- Correctness of §2.4's exact-count DP, using knapsack allocations across the
source's Eq. 4/5 subproblems. For each feasible row the output is an actual
root-preserving level-1 graph with exactly k reticulations, maximizing novel
and total weighted quartet support over every graph extension at count k.
This theorem makes no monotonicity or early-stopping assertion. -/
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
  obtain ⟨E,hE,hEk,hEz,hupper⟩ := exact_optimal t (edgeWeight t Q) M hM t.root_mem_nodes hz
  have hNE := Realization.levelOne t ht E hE.1
  have hscoreE := (novel_score_value observation2 t ht Q E hE.1).trans hEz
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

/-- Rows beyond the proved n−1 reticulation bound are empty. Thus the logical
array indexed by all naturals needs only finitely many budget columns. -/
 theorem high_budget_empty (t : PhyloTree) (w : Pair → ℕ) (M : Address → ℕ → Finset ℕ)
    (hM : Array t w M) {v : Address} (hv : v ∈ t.nodes) {k : ℕ}
    (hk : t.labels.length-1 < k) : M v k=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨E,hE,hEk,_⟩ := (array_correct t w M hM hv).1 k z hz
  have hbound := EdgeAbove.separated_card_bound hE.1
  omega

end Camus.BudgetDP
