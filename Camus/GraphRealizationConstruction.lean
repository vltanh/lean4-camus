module

public import Camus.GraphRealizationCactus
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

@[expose] public section

namespace Camus

namespace Realization

/-- The canonical support switching is literally the subdivision specified by
the stored wires. These fields are proved, rather than supplied as assumptions. -/
noncomputable def support (t : PhyloTree) (ht : t.WellLabelled)
    (E : Finset Pair) (hE : EdgeAbove.CycleSeparated t E) :
    SupportSubdivision t (graph t E) (supportEdges t E) := by
  classical
  refine
    { original := Address.code
      wire := wire t E
      original_injective := Address.code_injective.injOn
      root_preserved := rfl
      taxa_preserved := rfl
      leaves_preserved := ?_
      wire_laws := ?_
      interiors_disjoint := ?_
      vertices_covered := vertices_covered t E hE.1
      edges_covered := rfl
      switching := support_switching t E hE.1 }
  · intro p hp a hleaf
    change Address.code p = Address.code (leafAddress t a)
    rw [leafAddress_eq ht hleaf]
  · intro p hp hp0
    exact ⟨wire_length t E p, wire_nodup t E hE.1 hp hp0,
      wire_head t E p, wire_last t E p, wireInterior_disjoint_original t E p⟩
  · intro p hp q hq hpq
    exact interiors_disjoint t E hE.1 hpq

theorem levelOne (t : PhyloTree) (ht : t.WellLabelled)
    (E : Finset Pair) (hE : EdgeAbove.CycleSeparated t E) :
    (graph t E).RootedBinaryLevelOne :=
  levelOne_of_cycle_disjoint t ht E hE (cycles_disjoint t E hE)

theorem extracted_eq (t : PhyloTree) (ht : t.WellLabelled)
    (E : Finset Pair) (hE : EdgeAbove.CycleSeparated t E) :
    (support t ht E hE).extracted = E := by
  classical
  have hpair : ∀ e ∈ E,
      (support t ht E hE).pairOf (donor t e, recipient t e) = e := by
    intro e he
    have ha := (Finset.mem_filter.mp (hE.1 he)).2
    have hd := (support t ht E hE).anchor_eq ha.1 ha.2.2.1
      ((donor_mem_wireInterior_iff hE.1 he).mpr rfl)
    have hr := (support t ht E hE).anchor_eq ha.2.1 ha.2.2.2.1
      ((recipient_mem_wireInterior_iff hE.1 he).mpr rfl)
    exact Prod.ext hd hr
  unfold SupportSubdivision.extracted
  rw [nonSupportEdges t E hE.1, Finset.image_image]
  calc
    _ = E.image id := Finset.image_congr hpair
    _ = E := Finset.image_id


end Realization

end Camus
