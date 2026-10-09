module

public import Camus.Realization
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

@[expose] public section

namespace Camus

namespace Quartet

theorem sides_subset_taxa (q : Quartet) : q.sides.1 ⊆ q.taxa ∧ q.sides.2 ⊆ q.taxa := by
  simp only [sides]
  split_ifs <;> simp [taxa, Finset.subset_iff]

end Quartet

namespace RootedNetwork

/-- Reuse a switching when adding edges without changing vertices, root, or labels. -/
theorem displays_of_edges_subset {N : RootedNetwork} {S : Finset (ℕ × ℕ)}
    (h : S ⊆ N.edges) (q : Quartet) :
    ({N with edges := S}).DisplaysQuartet q → N.DisplaysQuartet q := by
  rintro ⟨hqt,R,hR,e,he,hsep⟩
  exact ⟨hqt,R,⟨hR.1.trans h,hR.2⟩,e,he,hsep⟩

noncomputable def renameEdges (f : ℕ ≃ ℕ) (S : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  S.image fun e => (f e.1, f e.2)

theorem renameEdges_mem (f : ℕ ≃ ℕ) (S : Finset (ℕ × ℕ)) (u v : ℕ) :
    (f u, f v) ∈ renameEdges f S ↔ (u,v) ∈ S := by
  classical
  simp [renameEdges, Prod.ext_iff]

theorem renameEdges_count (f : ℕ ≃ ℕ) (S : Finset (ℕ × ℕ)) (v : ℕ) :
    ((renameEdges f S).filter (fun e => e.2 = f v)).card =
      (S.filter (fun e => e.2 = v)).card := by
  classical
  rw [renameEdges, Finset.filter_image]
  simp only [f.injective.eq_iff]
  apply Finset.card_image_of_injective
  intro a b h
  apply Prod.ext
  · exact f.injective (congrArg Prod.fst h)
  · exact f.injective (congrArg Prod.snd h)

noncomputable def renamedUnderlyingIso (f : ℕ ≃ ℕ) (N P : RootedNetwork)
    (S : Finset (ℕ × ℕ)) :
    ({N with edges := S}).underlying ≃g
      ({P with edges := renameEdges f S}).underlying where
  toEquiv := f
  map_rel_iff' := by
    intro u v
    change (f u ≠ f v ∧ _) ↔ (u ≠ v ∧ _)
    simp only [f.injective.ne_iff, renameEdges_mem]

noncomputable def renamedCutIso (f : ℕ ≃ ℕ) (N P : RootedNetwork)
    (S : Finset (ℕ × ℕ)) (u v : ℕ) :
    (({N with edges := S}).underlying.deleteEdges {s(u,v)}) ≃g
      (({P with edges := renameEdges f S}).underlying.deleteEdges {s(f u,f v)}) where
  toEquiv := f
  map_rel_iff' := by
    intro a b
    simp only [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff, Sym2.eq_iff]
    have hadj : ({P with edges := renameEdges f S}).underlying.Adj (f a) (f b) ↔
        ({N with edges := S}).underlying.Adj a b :=
      (renamedUnderlyingIso f N P S).map_rel_iff
    rw [hadj]
    simp only [f.injective.eq_iff]

/-- A bijective renaming transports the chosen incoming edges and the quartet's
edge-separation witness. This lemma makes no optimization or attribution assumption. -/
theorem displays_of_rename {N P : RootedNetwork} (f : ℕ ≃ ℕ)
    (hvertices : ∀ v, v ∈ N.vertices ↔ f v ∈ P.vertices)
    (hedges : ∀ u v, (u,v) ∈ N.edges ↔ (f u,f v) ∈ P.edges)
    (hroot : f N.root = P.root) (htaxa : N.taxa = P.taxa)
    (hleaves : ∀ a ∈ N.taxa, f (N.leaf a) = P.leaf a)
    (q : Quartet) (hq : N.DisplaysQuartet q) : P.DisplaysQuartet q := by
  classical
  rcases hq with ⟨hqt,S,hS,e,he,hsep⟩
  have hqtP : q.taxa ⊆ P.taxa := htaxa ▸ hqt
  have hsP : P.Switching (renameEdges f S) := by
    constructor
    · intro a ha
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
      exact (hedges _ _).mp (hS.1 hb)
    · intro v hv hvr
      let u := f.symm v
      have huv : f u = v := f.apply_symm_apply v
      have hu : u ∈ N.vertices := (hvertices u).mpr (huv ▸ hv)
      have hur : u ≠ N.root := by
        intro h
        apply hvr
        rw [← huv, h, hroot]
      rw [← huv, renameEdges_count]
      exact hS.2 u hu hur
  refine ⟨hqtP,renameEdges f S,hsP,?_⟩
  induction e using Sym2.inductionOn with
  | _ u v =>
    refine ⟨s(f u,f v),?_,?_⟩
    · rw [SimpleGraph.mem_edgeSet] at he ⊢
      exact (renamedUnderlyingIso f N P S).map_rel_iff.mpr he
    · have hl (a : ℕ) (ha : a ∈ q.taxa) : f (N.leaf a) = P.leaf a :=
        hleaves a (hqt ha)
      have hr (a b : ℕ) (ha : a ∈ q.taxa) (hb : b ∈ q.taxa) :
          (({P with edges := renameEdges f S}).underlying.deleteEdges {s(f u,f v)}).Reachable
            (P.leaf a) (P.leaf b) ↔
          (({N with edges := S}).underlying.deleteEdges {s(u,v)}).Reachable
            (N.leaf a) (N.leaf b) := by
        rw [← hl a ha, ← hl b hb]
        exact (renamedCutIso f N P S u v).reachable_iff
      obtain ⟨h1,h2,h3⟩ := hsep
      refine ⟨?_,?_,?_⟩
      · intro a ha b hb
        exact (hr a b (q.sides_subset_taxa.1 ha) (q.sides_subset_taxa.1 hb)).mpr (h1 a ha b hb)
      · intro a ha b hb
        exact (hr a b (q.sides_subset_taxa.2 ha) (q.sides_subset_taxa.2 hb)).mpr (h2 a ha b hb)
      · intro a ha b hb h
        exact h3 a ha b hb ((hr a b (q.sides_subset_taxa.1 ha) (q.sides_subset_taxa.2 hb)).mp h)

end RootedNetwork
end Camus
