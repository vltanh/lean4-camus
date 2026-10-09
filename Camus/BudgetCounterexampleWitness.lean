module

public import Camus.BudgetCounterexamples
public import Camus.GraphRealizationRefinement
public import Camus.GraphSubdivisionInvariance
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace Camus.Counterexamples

open DynamicProgramming Realization

def budgetOuter : DynamicProgramming.Pair := ([false],[true])
def budgetInner : DynamicProgramming.Pair := ([true],[true,true,true])
def budgetPairs : Finset DynamicProgramming.Pair := {budgetOuter,budgetInner}
def alternateConstraint : PhyloTree :=
  .fork (.leaf 0) (.fork (.leaf 2) (.fork (.leaf 1) (.leaf 3)))

theorem budgetPairs_separated : EdgeAbove.CycleSeparated smallConstraint budgetPairs := by
  constructor
  · decide
  · intro e he f hf hef
    change e ∈ budgetPairs at he
    change f ∈ budgetPairs at hf
    simp only [budgetPairs,Finset.mem_insert,Finset.mem_singleton] at he hf
    rcases he with rfl | rfl <;> rcases hf with rfl | rfl
    · exact (hef rfl).elim
    · decide
    · decide
    · exact (hef rfl).elim

theorem outer_empty (p : Address)
    (h : ∀ e ∈ budgetPairs, ¬(e.1 = p ∧ EdgeAbove.target e ≠ p) ∧ e.2 ≠ p) :
    outerEndpoints smallConstraint budgetPairs p = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro v hv
  obtain ⟨e,he,hu | hr⟩ := mem_outerEndpoints.mp hv
  · exact (h e he).1 ⟨hu.1,hu.2.1⟩
  · exact (h e he).2 hr.1

theorem ghost_empty (p : Address)
    (h : ∀ e ∈ budgetPairs, ¬(e.1 = p ∧ EdgeAbove.target e = p)) :
    ghostEndpoints smallConstraint budgetPairs p = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro v hv
  obtain ⟨e,he,hu,ht,_⟩ := mem_ghostEndpoints.mp hv
  exact h e he ⟨hu,ht⟩

theorem wire_false : wire smallConstraint budgetPairs [false] =
    [1,donor smallConstraint budgetOuter,2] := by
  have ho := outerEndpoints_eq_singleton budgetPairs_separated
    (mem_outerEndpoints.mpr ⟨budgetOuter,by simp [budgetPairs],Or.inl ⟨rfl,by decide,rfl⟩⟩)
  have hg := ghost_empty [false] (by decide)
  simp only [budgetOuter] at ho hg
  simp [wire,ho,hg,parent,Address.code,budgetOuter]

theorem wire_true : wire smallConstraint budgetPairs [true] =
    [1,recipient smallConstraint budgetOuter,donor smallConstraint budgetInner,3] := by
  have ho := outerEndpoints_eq_singleton budgetPairs_separated
    (mem_outerEndpoints.mpr ⟨budgetOuter,by simp [budgetPairs],Or.inr ⟨rfl,rfl⟩⟩)
  have hg := ghostEndpoints_eq_singleton budgetPairs_separated
    (mem_ghostEndpoints.mpr ⟨budgetInner,by simp [budgetPairs],rfl,by decide,rfl⟩)
  simp only [budgetOuter,budgetInner] at ho hg
  simp [wire,ho,hg,parent,Address.code,budgetOuter,budgetInner]

theorem wire_recipient : wire smallConstraint budgetPairs [true,true,true] =
    [7,recipient smallConstraint budgetInner,15] := by
  have ho := outerEndpoints_eq_singleton budgetPairs_separated
    (mem_outerEndpoints.mpr ⟨budgetInner,by simp [budgetPairs],Or.inr ⟨rfl,rfl⟩⟩)
  have hg := ghost_empty [true,true,true] (by decide)
  simp only [budgetInner] at ho hg
  simp [wire,ho,hg,parent,Address.code,budgetInner]

theorem wire_other (p : Address)
    (hp : p ≠ [false] ∧ p ≠ [true] ∧ p ≠ [true,true,true]) :
    wire smallConstraint budgetPairs p = [Address.code (parent p),Address.code p] := by
  have ho := outer_empty p (by
    intro e he
    simp only [budgetPairs,Finset.mem_insert,Finset.mem_singleton] at he
    rcases he with rfl | rfl <;>
      simp [budgetOuter,budgetInner,Ne.symm hp.1,Ne.symm hp.2.1,Ne.symm hp.2.2])
  have hg := ghost_empty p (by
    intro e he
    simp only [budgetPairs,Finset.mem_insert,Finset.mem_singleton] at he
    rcases he with rfl | rfl <;> simp [budgetOuter,budgetInner,Ne.symm hp.1,Ne.symm hp.2.1])
  simp [wire,ho,hg]

noncomputable def budgetSwitch : Finset (ℕ×ℕ) :=
  insert (donor smallConstraint budgetInner,recipient smallConstraint budgetInner)
    ((supportEdges smallConstraint budgetPairs).erase (7,recipient smallConstraint budgetInner))

theorem support_expanded : supportEdges smallConstraint budgetPairs =
    {(1,donor smallConstraint budgetOuter),(donor smallConstraint budgetOuter,2),
      (1,recipient smallConstraint budgetOuter),(recipient smallConstraint budgetOuter,donor smallConstraint budgetInner),
      (donor smallConstraint budgetInner,3),(3,5),(3,7),(7,11),
      (7,recipient smallConstraint budgetInner),(recipient smallConstraint budgetInner,15)} := by
  unfold supportEdges
  have hn : smallConstraint.nodes.erase [] = {[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]} := by decide
  rw [hn]
  simp [wire_false,wire_true,wire_recipient,
    wire_other [true,false] (by decide),wire_other [true,true] (by decide),
    wire_other [true,true,false] (by decide),wireEdges,parent,Address.code,Finset.insert_comm]

theorem endpoint_facts :
    15 < donor smallConstraint budgetOuter ∧ 15 < recipient smallConstraint budgetOuter ∧
    15 < donor smallConstraint budgetInner ∧ 15 < recipient smallConstraint budgetInner ∧
    donor smallConstraint budgetOuter ≠ donor smallConstraint budgetInner ∧
    recipient smallConstraint budgetOuter ≠ recipient smallConstraint budgetInner ∧
    donor smallConstraint budgetOuter ≠ recipient smallConstraint budgetOuter ∧
    donor smallConstraint budgetOuter ≠ recipient smallConstraint budgetInner ∧
    donor smallConstraint budgetInner ≠ recipient smallConstraint budgetOuter ∧
    donor smallConstraint budgetInner ≠ recipient smallConstraint budgetInner := by
  have hb : 15 ≤ bound smallConstraint := by
    simpa [Address.code] using code_le_bound (show [true,true,true] ∈ smallConstraint.nodes by decide)
  have hdo := bound_lt_donor smallConstraint budgetOuter
  have hro := bound_lt_recipient smallConstraint budgetOuter
  have hdi := bound_lt_donor smallConstraint budgetInner
  have hri := bound_lt_recipient smallConstraint budgetInner
  have heo : budgetOuter ∈ EdgeAbove.candidates smallConstraint := by decide
  have hei : budgetInner ∈ EdgeAbove.candidates smallConstraint := by decide
  have hdd : donor smallConstraint budgetOuter ≠ donor smallConstraint budgetInner := by
    intro h
    have he := donor_injective smallConstraint heo hei h
    exact (by decide : budgetOuter ≠ budgetInner) he
  have hrr : recipient smallConstraint budgetOuter ≠ recipient smallConstraint budgetInner := by
    intro h
    have he := recipient_injective smallConstraint heo hei h
    exact (by decide : budgetOuter ≠ budgetInner) he
  exact ⟨by omega,by omega,by omega,by omega,hdd,hrr,
    donor_ne_recipient _ _ _,donor_ne_recipient _ _ _,donor_ne_recipient _ _ _,donor_ne_recipient _ _ _⟩

theorem switch_expanded : budgetSwitch =
    {(1,donor smallConstraint budgetOuter),(donor smallConstraint budgetOuter,2),
      (1,recipient smallConstraint budgetOuter),(recipient smallConstraint budgetOuter,donor smallConstraint budgetInner),
      (donor smallConstraint budgetInner,3),(3,5),(3,7),(7,11),
      (donor smallConstraint budgetInner,recipient smallConstraint budgetInner),
      (recipient smallConstraint budgetInner,15)} := by
  obtain ⟨hdo,hro,hdi,hri,hdd,hrr,hdo_ro,hdo_ri,hdi_ro,hdi_ri⟩ := endpoint_facts
  unfold budgetSwitch
  rw [support_expanded]
  ext f
  simp only [Finset.mem_insert,Finset.mem_singleton,Finset.mem_erase]
  constructor
  · intro h
    rcases h with h | ⟨_,h⟩ <;> tauto
  · intro h
    rcases h with h | h | h | h | h | h | h | h | h | h
    all_goals subst f
    all_goals simp [Prod.mk.injEq]
    all_goals omega

theorem baseline_alternate_vertices : (graph alternateConstraint ∅).vertices = {1,2,3,5,7,11,15} := by
  decide

theorem baseline_alternate_edges : (graph alternateConstraint ∅).edges =
    {(1,2),(1,3),(3,5),(3,7),(7,11),(7,15)} := by
  rw [baseline_edges]
  decide

noncomputable def alternateOriginal (n : ℕ) : ℕ :=
  if n = 3 then donor smallConstraint budgetInner else
  if n = 5 then 15 else if n = 7 then 3 else if n = 11 then 5 else if n = 15 then 11 else n

noncomputable def alternateWire (e : ℕ×ℕ) : List ℕ :=
  if e.2 = 2 then [1,donor smallConstraint budgetOuter,2] else
  if e.2 = 3 then [1,recipient smallConstraint budgetOuter,donor smallConstraint budgetInner] else
  if e.2 = 5 then [donor smallConstraint budgetInner,recipient smallConstraint budgetInner,15] else
  if e.2 = 7 then [donor smallConstraint budgetInner,3] else
  if e.2 = 11 then [3,5] else
  if e.2 = 15 then [3,7,11] else []

theorem full_vertices : (graph smallConstraint budgetPairs).vertices =
    {1,2,3,5,7,11,15,donor smallConstraint budgetOuter,recipient smallConstraint budgetOuter,
      donor smallConstraint budgetInner,recipient smallConstraint budgetInner} := by
  simp [graph,smallConstraint,PhyloTree.nodes,Address.code,budgetPairs,Finset.insert_comm]

theorem alternate_leaf_codes :
    (graph alternateConstraint ∅).leaf 0 = 2 ∧ (graph alternateConstraint ∅).leaf 1 = 11 ∧
    (graph alternateConstraint ∅).leaf 2 = 5 ∧ (graph alternateConstraint ∅).leaf 3 = 15 := by
  have ht : alternateConstraint.WellLabelled := by decide
  change (leafAddress alternateConstraint 0).code = 2 ∧ (leafAddress alternateConstraint 1).code = 11 ∧
    (leafAddress alternateConstraint 2).code = 5 ∧ (leafAddress alternateConstraint 3).code = 15
  rw [leafAddress_eq ht (show alternateConstraint.nodeAt [false] = some (.leaf 0) by decide),
    leafAddress_eq ht (show alternateConstraint.nodeAt [true,true,false] = some (.leaf 1) by decide),
    leafAddress_eq ht (show alternateConstraint.nodeAt [true,false] = some (.leaf 2) by decide),
    leafAddress_eq ht (show alternateConstraint.nodeAt [true,true,true] = some (.leaf 3) by decide)]
  decide

theorem original_leaf_codes :
    (graph smallConstraint budgetPairs).leaf 0 = 2 ∧ (graph smallConstraint budgetPairs).leaf 1 = 5 ∧
    (graph smallConstraint budgetPairs).leaf 2 = 15 ∧ (graph smallConstraint budgetPairs).leaf 3 = 11 := by
  have ht : smallConstraint.WellLabelled := by decide
  change (leafAddress smallConstraint 0).code = 2 ∧ (leafAddress smallConstraint 1).code = 5 ∧
    (leafAddress smallConstraint 2).code = 15 ∧ (leafAddress smallConstraint 3).code = 11
  rw [leafAddress_eq ht (show smallConstraint.nodeAt [false] = some (.leaf 0) by decide),
    leafAddress_eq ht (show smallConstraint.nodeAt [true,false] = some (.leaf 1) by decide),
    leafAddress_eq ht (show smallConstraint.nodeAt [true,true,true] = some (.leaf 2) by decide),
    leafAddress_eq ht (show smallConstraint.nodeAt [true,true,false] = some (.leaf 3) by decide)]
  decide

/-- The selected switch is a literal subdivision of the alternative quartet tree.
The root and taxon labels are preserved by the displayed explicit vertex map. -/
noncomputable def alternateSubdivision :
    GraphSubdivision (graph alternateConstraint ∅) {graph smallConstraint budgetPairs with edges := budgetSwitch} := by
  classical
  obtain ⟨hdo,hro,hdi,hri,hdd,hrr,hdo_ro,hdo_ri,hdi_ro,hdi_ri⟩ := endpoint_facts
  have hwP := baseline_alternate_vertices
  have heP := baseline_alternate_edges
  have hwN := full_vertices
  have heN := switch_expanded
  refine
    { original := alternateOriginal
      wire := alternateWire
      original_injective := ?_
      root_left := ?_
      root_preserved := ?_
      taxa_preserved := ?_
      leaves_left := ?_
      leaves_preserved := ?_
      edge_endpoints := ?_
      wire_laws := ?_
      interiors_disjoint := ?_
      vertices_covered := ?_
      edges_covered := ?_ }
  · intro u hu v hv heq
    change u ∈ (graph alternateConstraint ∅).vertices at hu
    change v ∈ (graph alternateConstraint ∅).vertices at hv
    rw [hwP] at hu hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try simp [alternateOriginal] at heq ⊢
    all_goals omega
  · rw [hwP]
    simp [graph,Address.code]
  · simp [graph,Address.code,alternateOriginal]
  · decide
  · intro a ha
    have hleaf := (supportGraphSubdivision alternateConstraint ∅ (Finset.empty_subset _)).leaves_left a ha
    exact hleaf
  · intro a ha
    have hat : a ∈ ({0,1,2,3} : Finset ℕ) := by simpa [graph,alternateConstraint,PhyloTree.taxa,PhyloTree.labels,Finset.insert_comm] using ha
    simp only [Finset.mem_insert,Finset.mem_singleton] at hat
    rcases hat with rfl | rfl | rfl | rfl
    · rw [alternate_leaf_codes.1,original_leaf_codes.1]
      simp [alternateOriginal]
    · rw [alternate_leaf_codes.2.1,original_leaf_codes.2.1]
      simp [alternateOriginal]
    · rw [alternate_leaf_codes.2.2.1,original_leaf_codes.2.2.1]
      simp [alternateOriginal]
    · rw [alternate_leaf_codes.2.2.2,original_leaf_codes.2.2.2]
      simp [alternateOriginal]
  · intro e he
    rw [heP] at he
    simp only [Finset.mem_insert,Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [hwP]
  · intro e he
    rw [heP] at he
    simp only [Finset.mem_insert,Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try simp [alternateWire,alternateOriginal,hwP,wireInterior]
    all_goals omega
  · intro e he f hf hef
    change e ∈ (graph alternateConstraint ∅).edges at he
    change f ∈ (graph alternateConstraint ∅).edges at hf
    rw [heP] at he hf
    simp only [Finset.mem_insert,Finset.mem_singleton] at he hf
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try simp [alternateWire,wireInterior] at hef ⊢
    all_goals omega
  · change (graph smallConstraint budgetPairs).vertices = _
    rw [hwN,hwP,heP]
    ext v
    simp [alternateOriginal,alternateWire,wireInterior]
    tauto
  · change budgetSwitch = _
    rw [heN,heP]
    ext f
    simp [alternateWire,wireEdges]
    tauto

theorem budgetSwitch_subset : budgetSwitch ⊆ (graph smallConstraint budgetPairs).edges := by
  intro f hf
  rcases Finset.mem_insert.mp hf with rfl | hf
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨budgetInner,by simp [budgetPairs],rfl⟩)
  · exact Finset.mem_union_left _ (Finset.mem_erase.mp hf).2

/-- Actual directed two-reticulation witness, including a root-preserving
subdivision proof of its selected alternative switching. No Observation 2 is
needed for the positive witness. -/
theorem graph_exact_two_score_one :
    (graph smallConstraint budgetPairs).AnchoredExtension smallConstraint ∧
    (graph smallConstraint budgetPairs).reticulationCount = 2 ∧
    score oneQuartet (DynamicProgramming.repertoire oneQuartet (graph smallConstraint budgetPairs)) = 1 := by
  have ht : smallConstraint.WellLabelled := by decide
  have hE := budgetPairs_separated
  have ht' : alternateConstraint.WellLabelled := by decide
  have hb : EdgeAbove.CycleSeparated alternateConstraint ∅ := by simp [EdgeAbove.CycleSeparated]
  have hbase : (graph alternateConstraint ∅).DisplaysQuartet (q0123 1) :=
    (baseline_displays_iff alternateConstraint ht' _).mpr (by decide)
  have hswitch := (alternateSubdivision.displays_iff (levelOne alternateConstraint ht' ∅ hb) _).mpr hbase
  have hdisplay := RootedNetwork.displays_of_edges_subset budgetSwitch_subset (q0123 1) hswitch
  refine ⟨⟨levelOne smallConstraint ht budgetPairs hE,
    ⟨supportEdges smallConstraint budgetPairs,⟨support smallConstraint ht budgetPairs hE⟩⟩⟩,?_,?_⟩
  · rw [reticulationCount_eq_card smallConstraint budgetPairs hE]
    decide
  · classical
    have hs : score oneQuartet (DynamicProgramming.repertoire oneQuartet (graph smallConstraint budgetPairs)) =
        oneQuartet.card := (score_eq_card_iff _ _).mpr (by
      intro q hq
      have heq : q = q0123 1 := by simpa [oneQuartet] using hq
      subst q
      exact Finset.mem_filter.mpr ⟨by simp [oneQuartet],hdisplay⟩)
    simpa [oneQuartet] using hs

def saturatedPairs : Finset DynamicProgramming.Pair :=
  {budgetOuter,([true,false],[true,true]),([true,true,false],[true,true,true])}

theorem saturatedPairs_separated : EdgeAbove.CycleSeparated smallConstraint saturatedPairs := by
  constructor
  · decide
  · intro e he f hf hef
    change e ∈ saturatedPairs at he
    change f ∈ saturatedPairs at hf
    simp only [saturatedPairs,Finset.mem_insert,Finset.mem_singleton] at he hf
    rcases he with rfl | rfl | rfl <;> rcases hf with rfl | rfl | rfl
    all_goals first | exact (hef rfl).elim | decide

/-- §2.4's printed exact-budget monotonicity claim fails in the full anchored
rooted directed graph class: the optimum is one at budget two and zero at budget
three. Both exact-budget feasible families are nonempty. The universal upper
bound at three has the explicitly authorized cited Observation 2 hypothesis. -/
theorem graph_exact_budget_nonmonotone
    (observation2 : External.WarnowTabatabaeeEvansObservation2) :
    (∃ N : RootedNetwork, N.AnchoredExtension smallConstraint ∧ N.reticulationCount = 2 ∧
      score oneQuartet (DynamicProgramming.repertoire oneQuartet N) = 1) ∧
    (∃ N : RootedNetwork, N.AnchoredExtension smallConstraint ∧ N.reticulationCount = 3) ∧
    (∀ N : RootedNetwork, N.AnchoredExtension smallConstraint → N.reticulationCount = 3 →
      score oneQuartet (DynamicProgramming.repertoire oneQuartet N) = 0) := by
  refine ⟨⟨graph smallConstraint budgetPairs,graph_exact_two_score_one⟩,?_,
    fun N hN hr => graph_exact_three_score_zero observation2 N hN hr⟩
  have ht : smallConstraint.WellLabelled := by decide
  have hE := saturatedPairs_separated
  refine ⟨graph smallConstraint saturatedPairs,
    ⟨levelOne smallConstraint ht saturatedPairs hE,
      ⟨supportEdges smallConstraint saturatedPairs,⟨support smallConstraint ht saturatedPairs hE⟩⟩⟩,?_⟩
  rw [reticulationCount_eq_card smallConstraint saturatedPairs hE]
  decide

end Camus.Counterexamples
