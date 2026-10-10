module

public import Camus.Network.Realization.Construction
public import Camus.Network.Realization.Subdivision
public import Camus.DP.Frontier
public import Camus.Network.Completeness.Tree

@[expose] public section

namespace Camus.Realization

def baselineCut (p : Address) : Sym2 ℕ := s(Address.code (parent p), Address.code p)

noncomputable def baselineCutGraph (t : PhyloTree) (p : Address) : SimpleGraph ℕ :=
  (graph t ∅).underlying.deleteEdges {baselineCut p}

theorem baselineCut_injective : Function.Injective baselineCut := by
  intro p q h
  rcases Sym2.eq_iff.mp h with h | h
  · exact Address.code_injective h.2
  · have h₁ := Address.code_injective h.1
    have h₂ := Address.code_injective h.2
    have hpq := (parent_prefix p).length_le
    have hqp := (parent_prefix q).length_le
    have hlength : p.length = q.length := by rw [h₁] at hpq; rw [← h₂] at hqp; omega
    have hp : p = parent p := (parent_prefix p).eq_of_length_le (by rw [h₁, ← hlength]) |>.symm
    exact hp.trans h₁

theorem prefix_parent_iff {p q : Address} (hneq : p ≠ q) :
    p <+: parent q ↔ p <+: q :=
  ⟨fun h => h.trans (parent_prefix q), fun h => prefix_parent_of_ne h hneq⟩

theorem baselineCut_adj_prefix {t : PhyloTree} {p : Address} {u v : ℕ}
    (h : (baselineCutGraph t p).Adj u v) :
    p <+: addressOf u ↔ p <+: addressOf v := by
  obtain ⟨hbase, hcut⟩ := SimpleGraph.deleteEdges_adj.mp h
  have directed (u v : ℕ) (he : (u,v) ∈ (graph t ∅).edges)
      (hcut : s(u,v) ≠ baselineCut p) : p <+: addressOf u ↔ p <+: addressOf v := by
    rw [baseline_edges] at he
    obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp he
    obtain ⟨hu, hv⟩ := Prod.mk.inj heq
    subst u
    subst v
    simp only [addressOf_code]
    have hqp : q ≠ p := by
      intro h
      exact hcut (h ▸ rfl)
    exact prefix_parent_iff (Ne.symm hqp)
  rcases hbase.2 with he | he
  · exact directed u v he (by simpa only [Set.mem_singleton_iff] using hcut)
  · exact (directed v u he (by simpa only [Set.mem_singleton_iff, Sym2.eq_swap] using hcut)).symm

theorem baselineCut_reachable_prefix {t : PhyloTree} {p : Address} {u v : ℕ}
    (h : (baselineCutGraph t p).Reachable u v) :
    p <+: addressOf u ↔ p <+: addressOf v := by
  obtain ⟨walk⟩ := h
  induction walk with
  | nil => rfl
  | cons hadj walk ih => exact (baselineCut_adj_prefix hadj).trans ih

theorem baselineCut_step {t : PhyloTree} {p q : Address}
    (hq : q ∈ t.nodes) (hqnil : q ≠ []) (hqp : q ≠ p) :
    (baselineCutGraph t p).Reachable (Address.code q) (Address.code (parent q)) := by
  have he : (Address.code (parent q), Address.code q) ∈ (graph t ∅).edges := by
    rw [baseline_edges]
    exact Finset.mem_image.mpr ⟨q, Finset.mem_erase.mpr ⟨hqnil, hq⟩, rfl⟩
  have hne : Address.code q ≠ Address.code (parent q) := by
    intro h
    exact EdgeAbove.parent_ne_self hqnil (Address.code_injective h).symm
  apply SimpleGraph.Adj.reachable
  apply SimpleGraph.deleteEdges_adj.mpr
  refine ⟨⟨hne, Or.inr he⟩, ?_⟩
  simp only [Set.mem_singleton_iff]
  intro h
  apply hqp
  apply baselineCut_injective
  simpa only [baselineCut, Sym2.eq_swap] using h

theorem baselineCut_inside {t : PhyloTree} {p x : Address}
    (hx : x ∈ t.nodes) (hpx : p <+: x) :
    (baselineCutGraph t p).Reachable (Address.code x) (Address.code p) := by
  generalize hn : x.length = n
  induction n using Nat.strong_induction_on generalizing x with
  | h n ih =>
    by_cases heq : x = p
    · subst x
      exact .refl _
    · have hnil : x ≠ [] := by
        intro h
        subst x
        exact heq ((hpx.eq_of_length_le (by simp)).symm)
      have hparent := t.nodes_prefix_closed hx (parent_prefix x)
      have hp := prefix_parent_of_ne hpx (Ne.symm heq)
      have hlt : (parent x).length < n := by
        simp only [parent, List.length_take]
        have hpos := List.length_pos_iff.mpr hnil
        omega
      exact (baselineCut_step hx hnil heq).trans
        (ih (parent x).length hlt hparent hp rfl)

theorem baselineCut_outside {t : PhyloTree} {p x : Address}
    (hx : x ∈ t.nodes) (hpx : ¬p <+: x) :
    (baselineCutGraph t p).Reachable (Address.code x) (Address.code []) := by
  generalize hn : x.length = n
  induction n using Nat.strong_induction_on generalizing x with
  | h n ih =>
    by_cases hnil : x = []
    · subst x
      exact .refl _
    · have hneq : x ≠ p := by
        intro h
        exact hpx (h ▸ List.prefix_refl _)
      have hparent := t.nodes_prefix_closed hx (parent_prefix x)
      have hp : ¬p <+: parent x := fun h => hpx (h.trans (parent_prefix x))
      have hlt : (parent x).length < n := by
        simp only [parent, List.length_take]
        have hpos := List.length_pos_iff.mpr hnil
        omega
      exact (baselineCut_step hx hnil hneq).trans
        (ih (parent x).length hlt hparent hp rfl)

theorem baselineCut_reachable_iff {t : PhyloTree} {p x y : Address}
    (hx : x ∈ t.nodes) (hy : y ∈ t.nodes) :
    (baselineCutGraph t p).Reachable (Address.code x) (Address.code y) ↔
      (p <+: x ↔ p <+: y) := by
  constructor
  · intro h
    simpa only [addressOf_code] using baselineCut_reachable_prefix h
  · intro h
    by_cases hpx : p <+: x
    · exact (baselineCut_inside hx hpx).trans (baselineCut_inside hy (h.mp hpx)).symm
    · have hpy : ¬p <+: y := fun hy => hpx (h.mpr hy)
      exact (baselineCut_outside hx hpx).trans (baselineCut_outside hy hpy).symm

end Camus.Realization
