module

public import Camus.GraphProperties
public import Camus.DynamicProgramming

@[expose] public section

namespace Camus

/-- Lemma 1 (`mthst2`) for an arbitrary rooted graph with an anchored support
switching. The single-pair realization is Definition 3's T+e. Completeness and
suppression bridges justify this representation; attribution is not assumed.
The only cited hypothesis is precisely the named literature Observation 2. -/
theorem lemma1 (observation2 : External.WarnowTabatabaeeEvansObservation2)
    (t : PhyloTree) (ht : t.WellLabelled) (N : RootedNetwork)
    (hN : N.RootedBinaryLevelOne) (S : Finset (ℕ × ℕ))
    (H : SupportSubdivision t N S) (q : Quartet)
    (hq : N.DisplaysQuartet q) (hnot : q.induced t ≠ true) :
    ∃! e, e ∈ N.edges \ S ∧
      (Realization.graph t {H.pairOf e}).DisplaysQuartet q := by
  sorry

/-- Directed-graph bridge for Lemma 2: two non-tree edges with the same original LCA target
would yield cycles sharing that vertex. This uses the concrete footprint bridge
and the paper's shared-target contradiction. -/
theorem lemma2 (t : PhyloTree) (ht : t.WellLabelled) (N : RootedNetwork)
    (hN : N.RootedBinaryLevelOne) (S : Finset (ℕ × ℕ))
    (H : SupportSubdivision t N S) {e f : ℕ × ℕ}
    (he : e ∈ N.edges \ S) (hf : f ∈ N.edges \ S)
    (htarget : EdgeAbove.target (H.pairOf e) = EdgeAbove.target (H.pairOf f)) : e = f := by
  sorry

namespace DynamicProgramming

/-- Set-valued disjoint-union consequence of Lemma 1. This proof must use the
numbered Lemma 1, rather than bypass it through an assumed score identity. -/
theorem novel_disjoint_union
    (observation2 : External.WarnowTabatabaeeEvansObservation2)
    (t : PhyloTree) (ht : t.WellLabelled) (Q : Multiset Quartet)
    (E : Finset Pair) (hE : EdgeAbove.CycleSeparated t E) :
    novel t Q (Realization.graph t E) =
        E.biUnion (fun e => novel t Q (Realization.graph t {e})) ∧
      (E : Set Pair).Pairwise (fun e f =>
        Disjoint (novel t Q (Realization.graph t {e}))
          (novel t Q (Realization.graph t {f}))) := by
  sorry

theorem baseline_subset (t : PhyloTree) (ht : t.WellLabelled)
    (Q : Multiset Quartet) (E : Finset Pair) (hE : EdgeAbove.CycleSeparated t E) :
    repertoire Q (Realization.graph t ∅) ⊆ repertoire Q (Realization.graph t E) := by
  sorry

end DynamicProgramming
end Camus
