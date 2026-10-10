module

public import Camus.Galled.Basic

@[expose] public section

namespace Camus.PhyloTree

/-- Label-preserving rooted-tree isomorphism allows independent swaps of the two
children of each internal vertex. This connects plane-tree storage to the
unordered trees of the paper. -/
inductive RootedIso : PhyloTree → PhyloTree → Prop
  | leaf (a : ℕ) : RootedIso (.leaf a) (.leaf a)
  | fork {l₁ r₁ l₂ r₂ : PhyloTree} : RootedIso l₁ l₂ → RootedIso r₁ r₂ →
      RootedIso (.fork l₁ r₁) (.fork l₂ r₂)
  | swap {l₁ r₁ l₂ r₂ : PhyloTree} : RootedIso l₁ r₂ → RootedIso r₁ l₂ →
      RootedIso (.fork l₁ r₁) (.fork l₂ r₂)

theorem RootedIso.refl (t : PhyloTree) : RootedIso t t := by
  induction t with
  | leaf a => exact .leaf a
  | fork l r hl hr => exact .fork hl hr

theorem RootedIso.symm {t u : PhyloTree} (h : RootedIso t u) : RootedIso u t := by
  induction h with
  | leaf a => exact .leaf a
  | fork _ _ hl hr => exact .fork hl hr
  | swap _ _ hl hr => exact .swap hr hl

/-- Swaps preserve taxon sets. -/
theorem RootedIso.taxa_eq {t u : PhyloTree} (h : RootedIso t u) : t.taxa = u.taxa := by
  induction h with
  | leaf => rfl
  | fork _ _ hl hr =>
    simp only [taxa] at hl hr
    simp only [taxa, labels, List.toFinset_append]
    rw [hl, hr]
  | swap _ _ hl hr =>
    simp only [taxa] at hl hr
    simp only [taxa, labels, List.toFinset_append]
    rw [hl, hr, Finset.union_comm]

/-- Swaps preserve the rooted cluster hierarchy, hence every unrooted quartet
cut. No converse or general graph-isomorphism claim is assumed here. -/
theorem RootedIso.clades_eq {t u : PhyloTree} (h : RootedIso t u) :
    t.clades.toFinset = u.clades.toFinset := by
  induction h with
  | leaf => rfl
  | @fork l₁ r₁ l₂ r₂ h₁ h₂ hl hr =>
    simp only [clades, List.toFinset_cons, List.toFinset_append]
    rw [h₁.taxa_eq, h₂.taxa_eq, hl, hr]
  | @swap l₁ r₁ l₂ r₂ h₁ h₂ hl hr =>
    simp only [clades, List.toFinset_cons, List.toFinset_append]
    rw [h₁.taxa_eq, h₂.taxa_eq, hl, hr]
    simp only [Finset.union_comm]

/-- The quartet predicate is invariant under the storage choices allowed by
rooted-tree isomorphism. -/
theorem RootedIso.induced_eq {t u : PhyloTree} (h : RootedIso t u) (q : Quartet) :
    q.induced t = q.induced u := by
  have hc : t.clades.any q.cutBy = u.clades.any q.cutBy := by
    rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
    constructor
    · rintro ⟨s, hs, hcut⟩
      refine ⟨s, ?_, hcut⟩
      apply List.mem_toFinset.mp
      rw [← h.clades_eq]
      exact List.mem_toFinset.mpr hs
    · rintro ⟨s, hs, hcut⟩
      refine ⟨s, ?_, hcut⟩
      apply List.mem_toFinset.mp
      rw [h.clades_eq]
      exact List.mem_toFinset.mpr hs
  simp only [Quartet.induced, h.taxa_eq, hc]

/-- Equality of the labelled rooted cluster hierarchy. -/
def ClusterEq (t u : PhyloTree) : Prop :=
  t.taxa = u.taxa ∧ t.clades.toFinset = u.clades.toFinset

theorem ClusterEq.refl (t : PhyloTree) : ClusterEq t t := ⟨rfl, rfl⟩

theorem ClusterEq.symm {t u : PhyloTree} (h : ClusterEq t u) : ClusterEq u t :=
  ⟨h.1.symm, h.2.symm⟩

theorem ClusterEq.trans {t u v : PhyloTree} (h : ClusterEq t u) (h' : ClusterEq u v) :
    ClusterEq t v := ⟨h.1.trans h'.1, h.2.trans h'.2⟩

theorem ClusterEq.fork {a b c d : PhyloTree} (h : ClusterEq a c) (h' : ClusterEq b d) :
    ClusterEq (.fork a b) (.fork c d) := by
  constructor
  · change (a.labels ++ b.labels).toFinset = (c.labels ++ d.labels).toFinset
    simp only [List.toFinset_append]
    change a.taxa ∪ b.taxa = c.taxa ∪ d.taxa
    rw [h.1, h'.1]
  · simp only [clades, List.toFinset_cons, List.toFinset_append]
    rw [h.1, h'.1, h.2, h'.2]

theorem ClusterEq.fork_swap (a b : PhyloTree) : ClusterEq (.fork a b) (.fork b a) :=
  ⟨(RootedIso.swap (.refl a) (.refl b)).taxa_eq,
    (RootedIso.swap (.refl a) (.refl b)).clades_eq⟩

theorem ClusterEq.induced_eq {t u : PhyloTree} (h : ClusterEq t u) (q : Quartet) :
    q.induced t = q.induced u := by
  have hc : t.clades.any q.cutBy = u.clades.any q.cutBy := by
    rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
    constructor
    · rintro ⟨s, hs, hcut⟩
      refine ⟨s, ?_, hcut⟩
      apply List.mem_toFinset.mp
      rw [← h.2]
      exact List.mem_toFinset.mpr hs
    · rintro ⟨s, hs, hcut⟩
      refine ⟨s, ?_, hcut⟩
      apply List.mem_toFinset.mp
      rw [h.2]
      exact List.mem_toFinset.mpr hs
  simp only [Quartet.induced, h.1, hc]

end Camus.PhyloTree

namespace Camus.GalledNetwork

/-- A switching displays an unordered copy of the constraint tree. This is
separate from an anchored, root-preserving edge-addition witness, which is needed
for the full DP theorem. -/
def DisplaysTopology (n : GalledNetwork) (t : PhyloTree) : Prop :=
  ∃ u ∈ n.displayed, PhyloTree.RootedIso u t

/-- Literal plane-tree containment always provides the corresponding topology. -/
theorem extends_displaysTopology {n : GalledNetwork} {t : PhyloTree}
    (h : n.Extends t) : n.DisplaysTopology t :=
  ⟨t, h, PhyloTree.RootedIso.refl t⟩

end Camus.GalledNetwork
