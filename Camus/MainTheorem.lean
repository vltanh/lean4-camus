module

public import Camus.QuartetAttribution
public import Camus.PackingTheorem

@[expose] public section

namespace Camus

namespace DynamicProgramming

theorem edgeWeight_score (t : PhyloTree) (Q : Multiset Quartet) (e : Pair) :
    edgeWeight t Q e = score Q (novel t Q (Realization.graph t {e})) := by
  exact (equation1 Q _).symm

theorem novel_score_value
    (observation2 : External.WarnowTabatabaeeEvansObservation2)
    (t : PhyloTree) (ht : t.WellLabelled) (Q : Multiset Quartet)
    (E : Finset Pair) (hE : EdgeAbove.CycleSeparated t E) :
    score Q (novel t Q (Realization.graph t E)) = value (edgeWeight t Q) E := by
  obtain ⟨hunion, hdisjoint⟩ := novel_disjoint_union observation2 t ht Q E hE
  rw [hunion, score_disjoint_union Q E _ hdisjoint]
  apply Finset.sum_congr rfl
  intro e he
  exact (edgeWeight_score t Q e).symm

theorem repertoire_iso {N P : RootedNetwork} (Q : Multiset Quartet)
    (hN : N.RootedBinaryLevelOne) (hP : P.RootedBinaryLevelOne) (i : N.Iso P) :
    repertoire Q N = repertoire Q P := by
  classical
  ext q
  simp only [repertoire, Finset.mem_filter]
  exact and_congr_right (fun _ => i.displays_iff hN hP q)

end DynamicProgramming

/-- Theorem 1 (`mthst9`): the CAMUS recurrence and its backtracking return a
rooted level-1 extension maximizing observed quartet support over EVERY anchored
rooted level-1 graph extension. The only unproved cited result is explicitly
named Observation 2. The proof follows the paper's decomposition and strong
induction, with Lemmas 1–2 and Equations 2–5 as its route. -/
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
  obtain ⟨hE, hvalue, hupper⟩ := DynamicProgramming.trace_optimal t
    (DynamicProgramming.edgeWeight t Q) M hM (PhyloTree.root_mem_nodes t) trace
  have hNE := Realization.levelOne t ht E hE.1
  have hscoreE := (DynamicProgramming.novel_score_value observation2 t ht Q E hE.1).trans hvalue
  have hnovel : ∀ N : RootedNetwork, N.AnchoredExtension t →
      score Q (DynamicProgramming.novel t Q N) ≤
        score Q (DynamicProgramming.novel t Q (Realization.graph t E)) := by
    intro N hN
    obtain ⟨S, ⟨H⟩⟩ := hN.2
    have hF := H.extracted_separated ht hN.1
    have hNF := Realization.levelOne t ht H.extracted hF
    obtain ⟨i⟩ := H.canonical_iso ht hN.1
    have hrep := DynamicProgramming.repertoire_iso Q hN.1 hNF i
    have hnovelEq : DynamicProgramming.novel t Q N =
        DynamicProgramming.novel t Q (Realization.graph t H.extracted) := by
      unfold DynamicProgramming.novel
      rw [hrep]
    rw [hnovelEq, DynamicProgramming.novel_score_value observation2 t ht Q H.extracted hF, hscoreE]
    exact hupper H.extracted ⟨hF, fun _ _ => List.nil_prefix⟩
  refine ⟨⟨hNE, ⟨Realization.supportEdges t E, ⟨Realization.support t ht E hE.1⟩⟩⟩,
    hscoreE, hnovel, ?_⟩
  intro N hN
  obtain ⟨S, ⟨H⟩⟩ := hN.2
  have hF := H.extracted_separated ht hN.1
  have hNF := Realization.levelOne t ht H.extracted hF
  obtain ⟨i⟩ := H.canonical_iso ht hN.1
  have hrep := DynamicProgramming.repertoire_iso Q hN.1 hNF i
  have hbaseN : DynamicProgramming.repertoire Q (Realization.graph t ∅) ⊆
      DynamicProgramming.repertoire Q N := by
    rw [hrep]
    exact DynamicProgramming.baseline_subset t ht Q H.extracted hF
  have hbaseE := DynamicProgramming.baseline_subset t ht Q E hE.1
  rw [score_offset Q _ _ hbaseN, score_offset Q _ _ hbaseE]
  exact Nat.add_le_add_left (hnovel N hN) _

end Camus
