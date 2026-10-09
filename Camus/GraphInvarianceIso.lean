module

public import Camus.GraphInvarianceRename
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

@[expose] public section

namespace Camus

namespace RootedNetwork

theorem Iso.displays_iff {N P : RootedNetwork}
    (hN : N.RootedBinaryLevelOne) (hP : P.RootedBinaryLevelOne)
    (i : N.Iso P) (q : Quartet) : N.DisplaysQuartet q ↔ P.DisplaysQuartet q := by
  classical
  let f : ℕ ≃ ℕ := i.vertices.extendSubtype
  have hvertices (v : ℕ) : v ∈ N.vertices ↔ f v ∈ P.vertices := by
    by_cases hv : v ∈ N.vertices
    · exact ⟨fun _ => Equiv.extendSubtype_mem i.vertices v hv, fun _ => hv⟩
    · exact ⟨fun h => (hv h).elim, fun h =>
        (Equiv.extendSubtype_not_mem i.vertices v hv h).elim⟩
  have hedges (u v : ℕ) : (u,v) ∈ N.edges ↔ (f u,f v) ∈ P.edges := by
    by_cases hu : u ∈ N.vertices
    · by_cases hv : v ∈ N.vertices
      · simpa only [f, Equiv.extendSubtype_apply_of_mem _ u hu,
          Equiv.extendSubtype_apply_of_mem _ v hv] using i.edges ⟨u,hu⟩ ⟨v,hv⟩
      · have hn : (u,v) ∉ N.edges := fun h => hv (hN.2.1 _ h).2
        have hp : (f u,f v) ∉ P.edges := fun h =>
          hv ((hvertices v).mpr (hP.2.1 _ h).2)
        simp [hn,hp]
    · have hn : (u,v) ∉ N.edges := fun h => hu (hN.2.1 _ h).1
      have hp : (f u,f v) ∉ P.edges := fun h =>
        hu ((hvertices u).mpr (hP.2.1 _ h).1)
      simp [hn,hp]
  have hroot : f N.root = P.root := by
    simpa only [f, Equiv.extendSubtype_apply_of_mem _ N.root i.root_left] using
      congrArg Subtype.val i.root_preserved
  have hleaves (a : ℕ) (ha : a ∈ N.taxa) : f (N.leaf a) = P.leaf a := by
    simpa only [f, Equiv.extendSubtype_apply_of_mem _ (N.leaf a) (i.leaves_left a ha)] using
      congrArg Subtype.val (i.leaves_preserved a ha)
  constructor
  · exact displays_of_rename f hvertices hedges hroot i.taxa_preserved hleaves q
  · apply displays_of_rename f.symm
    · intro v
      simpa only [f.apply_symm_apply] using (hvertices (f.symm v)).symm
    · intro u v
      simpa only [f.apply_symm_apply] using (hedges (f.symm u) (f.symm v)).symm
    · rw [← hroot, f.symm_apply_apply]
    · exact i.taxa_preserved.symm
    · intro a ha
      have h := hleaves a (i.taxa_preserved.symm ▸ ha)
      rw [← h, f.symm_apply_apply]

end RootedNetwork

end Camus
