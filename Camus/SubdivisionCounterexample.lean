module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

@[expose] public section

namespace Camus.SubdivisionCounterexample

/-- Underlying source graph for opposite directed arcs 0→1 and 1→0.
The four labelled leaves are 2,3,4,5. -/
def sourceEdges : Finset (Sym2 (Fin 7)) :=
  {s(0,1), s(0,2), s(0,3), s(1,4), s(1,5)}

def source : SimpleGraph (Fin 7) := SimpleGraph.fromEdgeSet sourceEdges

/-- Subdividing only 0→1 introduces vertex 6, while 1→0 remains.
The source bridge becomes the triangle 0–6–1–0. -/
def refinedEdges : Finset (Sym2 (Fin 7)) :=
  {s(0,6), s(6,1), s(1,0), s(0,2), s(0,3), s(1,4), s(1,5)}

def refined : SimpleGraph (Fin 7) := SimpleGraph.fromEdgeSet refinedEdges

instance : DecidableRel source.Adj := by unfold source; infer_instance
instance : DecidableRel refined.Adj := by unfold refined; infer_instance

def separates (G : SimpleGraph (Fin 7)) : Prop :=
  G.Reachable 2 3 ∧ G.Reachable 4 5 ∧ ¬G.Reachable 2 4

instance (G : SimpleGraph (Fin 7)) [DecidableRel G.Adj] : Decidable (separates G) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Kernel certificate for the false unrestricted subdivision helper:
opposite source arcs invalidate invariance of labelled quartet cuts.
A DAG hypothesis excludes precisely this obstruction. This certifies the
finite underlying cut example, independently of the main network library. -/
theorem antiparallel_cut_counterexample :
    separates (source.deleteEdges {s(0,1)}) ∧
      ∀ e ∈ refinedEdges, ¬separates (refined.deleteEdges {e}) := by
  decide +kernel

end Camus.SubdivisionCounterexample
