module

public import Camus.Network.RootAbove.Main
public import Camus.Restriction.Optimality

/-!
# Theorem 1 and Section 2.4 over the networks built on `T` of Definition 1

Theorem 1 and the optimality of the networks of Section 2.4 compare the output of the dynamic
program with the networks built on `T` with the root of `T` at the root
(`RootedNetwork.AnchoredExtension`), the class over which the dynamic program optimizes. Definition
1 also calls `N` built on `T` when its root lies above the root of `T` (`RootedNetwork.BuiltOn`).
Every such network has the same number of reticulations and displays the same quartets as a
network built on `T` with the root kept (`RootedNetwork.BuiltOn.exists_anchored`), so both results
hold over Definition 1's class. A quartet satisfied by `N` is one that `N` displays and `T` does
not induce (`DynamicProgramming.novel t Q N`); this depends on `T`, and not on the position of the
root of `T` in `N`.

## Main results

* `theorem1_builtOn`: Theorem 1 over Definition 1's networks built on `T`.
* `BudgetDP.exact_graph_optimal_builtOn`: the networks `N_k` of Section 2.4 are optimal among
  Definition 1's networks built on `T` with exactly `k` reticulations.
* `RootedNetwork.builtOn_reticulation_bound`: Section 2.4's bound of `n − 1` reticulations.

## Proof

The paper's proof of Theorem 1 ranges over the networks obtained by adding edges with targets in
`T`, and Section 2.2 excludes an edge that begins above the root of `T`. A network built on `T` in
the sense of Definition 1 whose root lies above the root of `T` has such an edge. The proofs here
replace the network by one built on `T` with the root kept, with the same displayed quartets and
the same number of reticulations (`RootedNetwork.BuiltOn.exists_anchored`), and apply `theorem1`
and `BudgetDP.exact_graph_optimal`, which follow the paper.
-/

@[expose] public section

namespace Camus

namespace DynamicProgramming

/-- Networks that display the same quartets display the same quartets of `Q`. -/
theorem repertoire_congr_displays (Q : Multiset Quartet) {N P : RootedNetwork}
    (h : ∀ q, N.DisplaysQuartet q ↔ P.DisplaysQuartet q) : repertoire Q N = repertoire Q P := by
  classical
  ext q
  simp only [repertoire, Finset.mem_filter]
  exact and_congr_right (fun _ => h q)

/-- Networks that display the same quartets satisfy the same quartets of `Q`. -/
theorem novel_congr_displays (t : PhyloTree) (Q : Multiset Quartet) {N P : RootedNetwork}
    (h : ∀ q, N.DisplaysQuartet q ↔ P.DisplaysQuartet q) : novel t Q N = novel t Q P := by
  unfold novel
  rw [repertoire_congr_displays Q h]

end DynamicProgramming

open DynamicProgramming in
/-- **Theorem 1** (`mthst9`), over the networks built on `T` of Definition 1, whose root may lie
above the root of `T`. Let `T` be a well-labelled tree and `Q` a multiset of quartets. Let `M`
satisfy the recurrence of Section 2.2 (Equations (2)–(5), with the weights `s_e` of Equation (1)),
and let `E` be a backtracking trace of `M` from the root. Then the network `Realization.graph t E`:
* is built on `T` with the root of `T` at its root, hence built on `T` in the sense of
  Definition 1 (`RootedNetwork.AnchoredExtension.builtOn`);
* satisfies `M[root]` quartets of `Q`, counted with multiplicity;
* satisfies at least as many quartets of `Q` as any network built on `T` in the sense of
  Definition 1;
* displays at least as many quartets of `Q` as any network built on `T` in the sense of
  Definition 1.

Departure from the paper: the paper's proof does not consider networks whose root lies above the
root of `T`, whose edge beginning above the root of `T` has no pair in Pairs(r). The proof applies
`theorem1` to the network built on `T` with the root kept that has the quartets of `N`
(`RootedNetwork.BuiltOn.exists_anchored`). -/
theorem theorem1_builtOn
    (t : PhyloTree) (ht : t.WellLabelled) (Q : Multiset Quartet)
    (M : Address → ℕ) (hM : Array t (edgeWeight t Q) M)
    (E : Finset Pair) (trace : Trace t (edgeWeight t Q) M [] E) :
    (Realization.graph t E).AnchoredExtension t ∧
      score Q (novel t Q (Realization.graph t E)) = M [] ∧
      (∀ N : RootedNetwork, N.BuiltOn t →
        score Q (novel t Q N) ≤ score Q (novel t Q (Realization.graph t E))) ∧
      (∀ N : RootedNetwork, N.BuiltOn t →
        score Q (repertoire Q N) ≤ score Q (repertoire Q (Realization.graph t E))) := by
  obtain ⟨hanchored, hscore, hnovel, hrep⟩ := theorem1 t ht Q M hM E trace
  refine ⟨hanchored, hscore, ?_, ?_⟩
  -- a network built on `T` has the quartets of a network built on `T` with the root kept
  · intro N hN
    obtain ⟨N', hN', _, hq⟩ := hN.exists_anchored ht
    rw [novel_congr_displays t Q hq]
    exact hnovel N' hN'
  · intro N hN
    obtain ⟨N', hN', _, hq⟩ := hN.exists_anchored ht
    rw [repertoire_congr_displays Q hq]
    exact hrep N' hN'

namespace BudgetDP

open DynamicProgramming

/-- Section 2.4: the networks `N_k`, over the networks built on `T` of Definition 1. Let `M`
satisfy the recurrence `BudgetDP.Array` with the weights `s_e` of Equation (1). For every value
`z` in the root row `M[r][k]` there is a family `E` of added edges whose canonical network
`Realization.graph t E` is built on `T` with the root kept, has exactly `k` reticulations and
satisfies `z` quartets of `Q` (with multiplicity); every network built on `T` in the sense of
Definition 1 with exactly `k` reticulations satisfies at most `z` quartets of `Q`, and displays at
most as many as `Realization.graph t E`.

Departure from the paper: the paper does not consider networks whose root lies above the root of
`T`. The proof applies `BudgetDP.exact_graph_optimal` to the network built on `T` with the root
kept that has the reticulations and the quartets of `N` (`RootedNetwork.BuiltOn.exists_anchored`).
-/
theorem exact_graph_optimal_builtOn
    (t : PhyloTree) (ht : t.WellLabelled) (Q : Multiset Quartet)
    (M : Address → ℕ → Finset ℕ) (hM : Array t (edgeWeight t Q) M)
    {k z : ℕ} (hz : z ∈ M [] k) :
    ∃ E : Finset Pair,
      (Realization.graph t E).AnchoredExtension t ∧
      (Realization.graph t E).reticulationCount = k ∧
      score Q (novel t Q (Realization.graph t E)) = z ∧
      (∀ N : RootedNetwork, N.BuiltOn t → N.reticulationCount = k →
        score Q (novel t Q N) ≤ z) ∧
      (∀ N : RootedNetwork, N.BuiltOn t → N.reticulationCount = k →
        score Q (repertoire Q N) ≤ score Q (repertoire Q (Realization.graph t E))) := by
  obtain ⟨E, hanchored, hk, hscore, hnovel, hrep⟩ := exact_graph_optimal t ht Q M hM hz
  refine ⟨E, hanchored, hk, hscore, ?_, ?_⟩
  -- a network built on `T` has the reticulations and the quartets of a network built on `T` with
  -- the root kept
  · intro N hN hNk
    obtain ⟨N', hN', hret, hq⟩ := hN.exists_anchored ht
    rw [novel_congr_displays t Q hq]
    exact hnovel N' hN' (hret.trans hNk)
  · intro N hN hNk
    obtain ⟨N', hN', hret, hq⟩ := hN.exists_anchored ht
    rw [repertoire_congr_displays Q hq]
    exact hrep N' hN' (hret.trans hNk)

end BudgetDP

/-- Section 2.4: "a level-1 phylogenetic network on n leaves will not have more than n−1
reticulations", for the networks built on `T` of Definition 1. A network built on a well-labelled
tree `T` with `n` taxa in the sense of Definition 1 has at most `n − 1` reticulations: it has as
many as a network built on `T` with the root kept (`RootedNetwork.BuiltOn.exists_anchored`,
`RootedNetwork.anchored_reticulation_bound`). -/
theorem RootedNetwork.builtOn_reticulation_bound {t : PhyloTree} (ht : t.WellLabelled)
    {N : RootedNetwork} (hN : N.BuiltOn t) : N.reticulationCount ≤ t.taxa.card - 1 := by
  obtain ⟨N', hN', hret, _⟩ := hN.exists_anchored ht
  rw [← hret]
  exact RootedNetwork.anchored_reticulation_bound ht hN'

end Camus
