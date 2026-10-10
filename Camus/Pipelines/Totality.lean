module

public import Camus.Pipelines.Rooting
public import Camus.DP.Theorem1

/-!
# Section 3.2: the SNP pipeline always returns a network

Section 3.2 runs CAMUS on the multiset `Q` of the quartets of the SNPs, with the tree returned by
ASTRAL on `Q`, rooted at the outgroup, and says: "Note that for all inputs, this pipeline will
always return an output rooted level-1 phylogenetic network, since (i) ASTRAL always returns a
tree, (ii) we have an outgroup and hence can root the tree returned by ASTRAL, and (iii) CAMUS
always returns a level-1 network building on the given input tree." This file proves the three
steps and the conclusion, for every multiset `Q` and every finite set `X` of taxa that contains the
outgroup `z`.

The library's trees are rooted (`PhyloTree`) and stand for their unrooted forms through the
quartets they induce (`Quartet.induced`), so ASTRAL's problem is the maximization of the quartet
support score (`quartetSupport`) over the well-labelled trees on `X`, and rooting at the outgroup
replaces a tree by a tree with the same induced quartets whose root has the leaf `z` as a child
(`PhyloTree.reroot`).

## Main results

* `astral_total`: (i) some well-labelled tree on `X` has the maximum quartet support score.
* `astral_rooted`: (ii) rooted at the outgroup, a tree keeps its taxa, its quartets and its score,
  and its root has the outgroup leaf as a child.
* `camus_total`: (iii) CAMUS has an output on every well-labelled tree, and every output is a
  rooted binary level-1 network built on it.
* `snpPipeline_total`: the pipeline returns a rooted binary level-1 network built on the rooted
  tree of ASTRAL, for all inputs.

## Proof (the paper's)

1. ASTRAL solves its problem exactly, and the problem has a solution: the scores are at most `|Q|`
   (`quartetSupport_eq_card`) and some well-labelled tree on `X` exists
   (`PhyloTree.exists_wellLabelled`), so the maximum score is attained (`astral_total`).
2. The tree returned by ASTRAL can be rooted on the edge leading to the outgroup, with the same
   quartets (`PhyloTree.reroot_spec`), hence the same score (`PhyloTree.quartetSupport_reroot`).
3. The dynamic program has an array and a backtracking trace on every tree
   (`DynamicProgramming.exists_array_trace`), and its output is built on the input tree
   (`theorem1`).
-/

@[expose] public section

namespace Camus

open DynamicProgramming

/-- Section 3.2, (i): "ASTRAL always returns a tree". For every multiset `Q` of quartets and every
nonempty finite set `X` of taxa, some well-labelled tree on `X` has a quartet support score at least
that of every well-labelled tree on `X`. -/
theorem astral_total (Q : Multiset Quartet) {X : Finset ℕ} (hX : X.Nonempty) :
    ∃ T : PhyloTree, T.WellLabelled ∧ T.taxa = X ∧
      ∀ T' : PhyloTree, T'.WellLabelled → T'.taxa = X →
        quartetSupport Q T' ≤ quartetSupport Q T := by
  classical
  -- the scores of the trees on `X` are at most `|Q|`
  have hle : ∀ T, quartetSupport Q T ≤ Q.card := fun T => by
    rw [quartetSupport_eq_card]
    exact Multiset.card_le_card (Multiset.filter_le _ _)
  let V := (Finset.range (Q.card + 1)).filter
    (fun s => ∃ T : PhyloTree, T.WellLabelled ∧ T.taxa = X ∧ quartetSupport Q T = s)
  have hmem : ∀ T : PhyloTree, T.WellLabelled → T.taxa = X → quartetSupport Q T ∈ V :=
    fun T hT hTX => Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (hle T)), T, hT, hTX, rfl⟩
  -- some tree on `X` exists, so the maximum score is attained
  obtain ⟨T₀, hT₀, hT₀X⟩ := PhyloTree.exists_wellLabelled hX
  have hV : V.Nonempty := ⟨_, hmem T₀ hT₀ hT₀X⟩
  obtain ⟨-, T, hT, hTX, hTs⟩ := Finset.mem_filter.mp (V.max'_mem hV)
  exact ⟨T, hT, hTX, fun T' hT' hT'X => hTs ▸ V.le_max' _ (hmem T' hT' hT'X)⟩

/-- Section 3.2, (ii): "we have an outgroup and hence can root the tree returned by ASTRAL". A
well-labelled tree `T` with the outgroup `z` among its taxa, rooted on the edge leading to `z`
(`PhyloTree.reroot`), is a well-labelled tree with the taxa, the induced quartets and the quartet
support score of `T`; if `T` has a taxon other than `z`, the root of the rooted tree has the leaf
`z` as a child. -/
theorem astral_rooted (Q : Multiset Quartet) {T : PhyloTree} (hT : T.WellLabelled) {z : ℕ}
    (hz : z ∈ T.taxa) :
    (PhyloTree.reroot z T).WellLabelled ∧ (PhyloTree.reroot z T).taxa = T.taxa ∧
      (∀ q : Quartet, q.induced (PhyloTree.reroot z T) = q.induced T) ∧
      quartetSupport Q (PhyloTree.reroot z T) = quartetSupport Q T ∧
      ((∃ a ∈ T.taxa, a ≠ z) → ∃ R, PhyloTree.reroot z T = .fork (.leaf z) R) := by
  obtain ⟨hwl, htaxa, hq⟩ := PhyloTree.reroot_spec hT hz
  refine ⟨hwl, htaxa, hq, PhyloTree.quartetSupport_reroot Q hT hz, fun h2 => ?_⟩
  cases T with
  -- a single leaf has one taxon
  | leaf b =>
    obtain ⟨a, ha, haz⟩ := h2
    simp only [PhyloTree.taxa, PhyloTree.labels, List.toFinset_cons, List.toFinset_nil,
      insert_empty_eq, Finset.mem_singleton] at ha hz
    exact absurd (ha.trans hz.symm) haz
  | fork l r => exact PhyloTree.reroot_eq_fork z l r

/-- Section 3.2, (iii): "CAMUS always returns a level-1 network building on the given input tree".
For every well-labelled tree `T` and multiset `Q`, the recurrence of Section 2.2 has a solution with
a backtracking trace from the root, and every network returned by backtracking is a rooted binary
level-1 network built on `T`, with the root of `T` at its root. -/
theorem camus_total (T : PhyloTree) (hT : T.WellLabelled) (Q : Multiset Quartet) :
    (∃ M E, Array T (edgeWeight T Q) M ∧ Trace T (edgeWeight T Q) M [] E) ∧
      ∀ M E, Array T (edgeWeight T Q) M → Trace T (edgeWeight T Q) M [] E →
        (Realization.graph T E).AnchoredExtension T := by
  refine ⟨?_, fun M E hM hE => (theorem1 T hT Q M hM E hE).1⟩
  obtain ⟨M, hM, E, hE⟩ := exists_array_trace T (edgeWeight T Q)
  exact ⟨M, E, hM, hE⟩

/-- Section 3.2: "for all inputs, this pipeline will always return an output rooted level-1
phylogenetic network". Let `Q` be a multiset of quartets (the quartets of the SNPs) and `X` a
finite set of taxa that contains the outgroup `z`. Then ASTRAL has an output, a well-labelled tree
on `X` of maximum quartet support score. Every such tree `T`, rooted at the outgroup, is a
well-labelled tree on `X` with the quartets of `T` and the maximum score, whose root has the leaf
`z` as a child if `X` has another taxon. CAMUS, on that rooted tree and `Q`, has an output, and
every output is a rooted binary level-1 network built on the rooted tree, with the root of the tree
at the root of the network. -/
theorem snpPipeline_total (Q : Multiset Quartet) {X : Finset ℕ} {z : ℕ} (hz : z ∈ X) :
    (∃ T : PhyloTree, T.WellLabelled ∧ T.taxa = X ∧
      ∀ T' : PhyloTree, T'.WellLabelled → T'.taxa = X →
        quartetSupport Q T' ≤ quartetSupport Q T) ∧
    ∀ T : PhyloTree, T.WellLabelled → T.taxa = X →
      (∀ T' : PhyloTree, T'.WellLabelled → T'.taxa = X →
        quartetSupport Q T' ≤ quartetSupport Q T) →
      (PhyloTree.reroot z T).WellLabelled ∧ (PhyloTree.reroot z T).taxa = X ∧
        (∀ q : Quartet, q.induced (PhyloTree.reroot z T) = q.induced T) ∧
        (∀ T' : PhyloTree, T'.WellLabelled → T'.taxa = X →
          quartetSupport Q T' ≤ quartetSupport Q (PhyloTree.reroot z T)) ∧
        ((∃ a ∈ X, a ≠ z) → ∃ R, PhyloTree.reroot z T = .fork (.leaf z) R) ∧
        (∃ M E, Array (PhyloTree.reroot z T) (edgeWeight (PhyloTree.reroot z T) Q) M ∧
          Trace (PhyloTree.reroot z T) (edgeWeight (PhyloTree.reroot z T) Q) M [] E) ∧
        ∀ M E, Array (PhyloTree.reroot z T) (edgeWeight (PhyloTree.reroot z T) Q) M →
          Trace (PhyloTree.reroot z T) (edgeWeight (PhyloTree.reroot z T) Q) M [] E →
          (Realization.graph (PhyloTree.reroot z T) E).AnchoredExtension
            (PhyloTree.reroot z T) := by
  -- (i) ASTRAL returns a tree
  refine ⟨astral_total Q ⟨z, hz⟩, fun T hT hTX hmax => ?_⟩
  -- (ii) the tree is rooted at the outgroup
  obtain ⟨hwl, htaxa, hq, hscore, hfork⟩ := astral_rooted Q hT (hTX ▸ hz)
  -- (iii) CAMUS returns a network built on the rooted tree
  obtain ⟨hex, hall⟩ := camus_total _ hwl Q
  exact ⟨hwl, htaxa.trans hTX, hq, fun T' hT' hT'X => hscore ▸ hmax T' hT' hT'X,
    fun h2 => hfork (hTX ▸ h2), hex, hall⟩

end Camus
