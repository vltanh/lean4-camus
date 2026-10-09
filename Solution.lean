module

public import Camus
public import Camus.MainTheorem

-- Preserve the Nat lattice instance chosen by the immutable Challenge imports.
-- Later proof imports also export Nat.instLattice; it is definitionally equal
-- but the Comparator requires identical elaborated statement dependencies.
attribute [local instance 2000] DistribLattice.toLattice
attribute [local instance 2000] Lattice.toSemilatticeSup

@[expose] public section

namespace CamusResults

theorem equation1 {α : Type*} [DecidableEq α] (Q : Multiset α) (D : Finset α) :
    (Q.filter (· ∈ D)).card =
      ∑ q ∈ Q.toFinset, if q ∈ D then Q.count q else 0 := by
  exact Camus.equation1 Q D

theorem atMostBudgetMonotone {α N : Type*} [DecidableEq α] [DecidableEq N]
    (C : Finset N) (displayed : N → Finset α) (reticulations : N → ℕ)
    (Q : Multiset α) {j k : ℕ} (hjk : j ≤ k) :
    (C.filter (fun n => reticulations n ≤ j)).sup
        (fun n => (Q.filter (· ∈ displayed n)).card) ≤
      (C.filter (fun n => reticulations n ≤ k)).sup
        (fun n => (Q.filter (· ∈ displayed n)).card) := by
  exact Camus.atMostScore_mono C displayed reticulations Q hjk

theorem correctedRecovery {α N : Type*} [DecidableEq α]
    (C : Finset N) (displayed : N → Finset α) (reticulations : N → ℕ)
    (equivalent : N → N → Prop) (truth selected : N)
    (truth_feasible : truth ∈ C) (Q : Multiset α)
    (exact_support : Q.toFinset = displayed truth)
    (identifiable : ∀ n ∈ C, displayed truth ⊆ displayed n →
      reticulations n ≤ reticulations truth → equivalent n truth)
    (optimal : selected ∈ C ∧ ∀ m ∈ C,
      (Q.filter (· ∈ displayed m)).card ≤ (Q.filter (· ∈ displayed selected)).card)
    (tie_break : ∀ m ∈ C,
      (m ∈ C ∧ ∀ n ∈ C,
        (Q.filter (· ∈ displayed n)).card ≤ (Q.filter (· ∈ displayed m)).card) →
      reticulations selected ≤ reticulations m) :
    equivalent selected truth := by
  exact Camus.correctedConsistency C displayed reticulations equivalent truth selected
    truth_feasible Q exact_support identifiable optimal tie_break


/-- Theorem 1: the full conditional optimality statement, with novel and total
support related explicitly. The root and all support-tree laws are retained. -/
theorem optimalNetwork
    (WarnowTabatabaeeEvansObservation2 :
      ∀ N : Camus.RootedNetwork, N.RootedBinaryLevelOne →
        ∀ q : Camus.Quartet, q.taxa ⊆ N.taxa →
          (N.DisplaysQuartet q ↔ N.CutEdgeSeparates q ∨ N.CycleSeparates q))
    (t : Camus.PhyloTree) (ht : t.WellLabelled) (Q : Multiset Camus.Quartet)
    (M : Camus.Address → ℕ)
    (hM : Camus.DynamicProgramming.Array t (Camus.DynamicProgramming.edgeWeight t Q) M)
    (E : Finset Camus.DynamicProgramming.Pair)
    (trace : Camus.DynamicProgramming.Trace t (Camus.DynamicProgramming.edgeWeight t Q) M [] E) :
    (Camus.Realization.graph t E).AnchoredExtension t ∧
      Camus.score Q (Camus.DynamicProgramming.novel t Q (Camus.Realization.graph t E)) = M [] ∧
      (∀ N : Camus.RootedNetwork, N.AnchoredExtension t →
        Camus.score Q (Camus.DynamicProgramming.novel t Q N) ≤
          Camus.score Q (Camus.DynamicProgramming.novel t Q (Camus.Realization.graph t E))) ∧
      (∀ N : Camus.RootedNetwork, N.AnchoredExtension t →
        Camus.score Q (Camus.DynamicProgramming.repertoire Q N) ≤
          Camus.score Q (Camus.DynamicProgramming.repertoire Q (Camus.Realization.graph t E))) := by
  exact Camus.theorem1 WarnowTabatabaeeEvansObservation2 t ht Q M hM E trace

end CamusResults
