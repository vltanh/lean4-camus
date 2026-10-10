module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-!
# Antiparallel arcs and subdivision

`GraphSubdivision.displays_iff` assumes that `P` is a rooted binary level-1 network, and its proof
uses that `P` is acyclic, so has no two antiparallel arcs `u → v`, `v → u`. This file shows by a
finite example what goes wrong with such arcs. If `P` has arcs `0 → 1` and `1 → 0`, both give the
single undirected edge `{0, 1}`; with leaves `2, 3` at `0` and `4, 5` at `1`, deleting this edge
separates `23|45`. Subdividing `0 → 1` only, by a vertex `6`, turns the edge into the triangle
`0–6–1–0`, and no single edge deletion separates `23|45` any more. So the cut comparison
`GraphSubdivision.separates_cut_iff` fails without acyclicity. The example is stated for the
underlying undirected graphs. It concerns a hypothesis of an auxiliary theorem, not a claim of
the paper.

## Main results

* `SubdivisionCounterexample.antiparallel_cut_counterexample`: deleting `{0, 1}` separates `23|45`
  before subdivision; no single edge deletion separates it after.
-/

@[expose] public section

namespace Camus.SubdivisionCounterexample

/-- The underlying undirected edges before subdivision. The antiparallel arcs `0 → 1` and `1 → 0`
both give the edge `{0, 1}`; the labelled leaves are `2, 3`, attached to `0`, and `4, 5`, attached
to `1`. -/
def sourceEdges : Finset (Sym2 (Fin 7)) :=
  {s(0,1), s(0,2), s(0,3), s(1,4), s(1,5)}

/-- The underlying undirected graph before subdivision. -/
def source : SimpleGraph (Fin 7) := SimpleGraph.fromEdgeSet sourceEdges

/-- The underlying undirected edges after subdividing the arc `0 → 1` by the vertex `6`; the arc
`1 → 0` remains. The edge `{0, 1}` becomes the triangle `0–6–1–0`. -/
def refinedEdges : Finset (Sym2 (Fin 7)) :=
  {s(0,6), s(6,1), s(1,0), s(0,2), s(0,3), s(1,4), s(1,5)}

/-- The underlying undirected graph after subdivision. -/
def refined : SimpleGraph (Fin 7) := SimpleGraph.fromEdgeSet refinedEdges

instance : DecidableRel source.Adj := by unfold source; infer_instance
instance : DecidableRel refined.Adj := by unfold refined; infer_instance

/-- `G` separates the quartet `23|45`: `2` is connected to `3`, `4` to `5`, and `2` not to `4`. -/
def separates (G : SimpleGraph (Fin 7)) : Prop :=
  G.Reachable 2 3 ∧ G.Reachable 4 5 ∧ ¬G.Reachable 2 4

instance (G : SimpleGraph (Fin 7)) [DecidableRel G.Adj] : Decidable (separates G) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- With antiparallel arcs, subdivision can destroy a cut. Deleting the edge `{0, 1}` from `source`
separates `23|45`, but deleting any single edge of `refined`, the graph after subdividing `0 → 1`,
does not. Acyclicity of `P` excludes this in `GraphSubdivision.displays_iff`. -/
theorem antiparallel_cut_counterexample :
    separates (source.deleteEdges {s(0,1)}) ∧
      ∀ e ∈ refinedEdges, ¬separates (refined.deleteEdges {e}) := by
  decide +kernel

end Camus.SubdivisionCounterexample
