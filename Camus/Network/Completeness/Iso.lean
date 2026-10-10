module

public import Camus.Network.Completeness.CanonicalWires

@[expose] public section

namespace Camus

theorem wireEdges_map (l : List ℕ) (f : ℕ → ℕ) :
    wireEdges (l.map f) = (wireEdges l).image (Prod.map f f) := by
  classical
  ext e
  simp only [wireEdges,← List.map_tail,List.zip_map,Finset.mem_image,List.mem_toFinset,List.mem_map]

namespace SupportSubdivision

variable {t : PhyloTree} {N : RootedNetwork} {S : Finset (ℕ × ℕ)}

theorem encode_edges_image (H : SupportSubdivision t N S)
    (hN : N.RootedBinaryLevelOne)
    (hpairs : Set.InjOn H.pairOf (N.edges \ S : Finset (ℕ × ℕ)))
    (hsep : EdgeAbove.CycleSeparated t H.extracted) :
    N.edges.image (Prod.map H.encode H.encode) = (Realization.graph t H.extracted).edges := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he
    by_cases hfS : f ∈ S
    · rw [H.edges_covered] at hfS
      obtain ⟨p,hp,hfp⟩ := Finset.mem_biUnion.mp hfS
      obtain ⟨hp0,hp⟩ := Finset.mem_erase.mp hp
      apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      refine ⟨p,Finset.mem_erase.mpr ⟨hp0,hp⟩,?_⟩
      rw [← H.map_wire_eq hN hpairs hsep hp hp0,wireEdges_map]
      exact Finset.mem_image.mpr ⟨f,hfp,rfl⟩
    · have hfD : f ∈ N.edges \ S := Finset.mem_sdiff.mpr ⟨hf,hfS⟩
      apply Finset.mem_union_right
      refine Finset.mem_image.mpr ⟨H.pairOf f,Finset.mem_image.mpr ⟨f,hfD,rfl⟩,?_⟩
      simp only [Prod.map,H.encode_donor hN hfD,H.encode_recipient hN hfD]
  · intro he
    rcases Finset.mem_union.mp he with hs | hr
    · obtain ⟨p,hp,hep⟩ := Finset.mem_biUnion.mp hs
      obtain ⟨hp0,hp⟩ := Finset.mem_erase.mp hp
      rw [← H.map_wire_eq hN hpairs hsep hp hp0,wireEdges_map] at hep
      obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hep
      exact Finset.mem_image.mpr ⟨f,H.switching.1 (H.wire_edge_mem_support hp hp0 hf),rfl⟩
    · obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hr
      obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hq
      refine Finset.mem_image.mpr ⟨f,(Finset.mem_sdiff.mp hf).1,?_⟩
      simp only [Prod.map,H.encode_donor hN hf,H.encode_recipient hN hf]

/-- The graph isomorphism is constructed from the canonical vertex encoding
and the proved equality of every directed wire. -/
noncomputable def canonicalIso (H : SupportSubdivision t N S)
    (hN : N.RootedBinaryLevelOne)
    (hpairs : Set.InjOn H.pairOf (N.edges \ S : Finset (ℕ × ℕ)))
    (hsep : EdgeAbove.CycleSeparated t H.extracted) :
    N.Iso (Realization.graph t H.extracted) := by
  classical
  have hroot : (Realization.graph t H.extracted).root ∈
      (Realization.graph t H.extracted).vertices :=
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨[],t.root_mem_nodes,rfl⟩)
  have hleaves : ∀ a ∈ N.taxa, (Realization.graph t H.extracted).leaf a ∈
      (Realization.graph t H.extracted).vertices := by
    intro a ha
    have hat : a ∈ t.taxa := H.taxa_preserved ▸ ha
    exact Finset.mem_union_left _ (Finset.mem_image.mpr
      ⟨Realization.leafAddress t a,Realization.leafAddress_mem_nodes hat,rfl⟩)
  refine
    { vertices := H.vertexEquiv hN hpairs
      edges := ?_
      root_left := hN.1
      root_right := hroot
      root_preserved := ?_
      taxa_preserved := H.taxa_preserved
      leaves_left := fun a ha => (hN.2.2.2.2.2.2.2.1 a ha).1
      leaves_right := hleaves
      leaves_preserved := ?_ }
  · intro u v
    change ((u.val,v.val) ∈ N.edges ↔ (H.encode u.val,H.encode v.val) ∈ _)
    rw [← H.encode_edges_image hN hpairs hsep]
    constructor
    · intro he
      exact Finset.mem_image.mpr ⟨(u.val,v.val),he,rfl⟩
    · intro he
      obtain ⟨f,hf,heq⟩ := Finset.mem_image.mp he
      have hfN := hN.2.1 f hf
      have heq₁ : H.encode f.1 = H.encode u.val := congrArg Prod.fst heq
      have heq₂ : H.encode f.2 = H.encode v.val := congrArg Prod.snd heq
      have hu := H.encode_injective_vertices hN hpairs hfN.1 u.property heq₁
      have hv := H.encode_injective_vertices hN hpairs hfN.2 v.property heq₂
      have hfe : f = (u.val,v.val) := Prod.ext hu hv
      exact hfe ▸ hf
  · apply Subtype.ext
    change H.encode N.root = Address.code []
    rw [← H.root_preserved,H.encode_original t.root_mem_nodes]
  · intro a ha
    apply Subtype.ext
    change H.encode (N.leaf a) = Address.code (Realization.leafAddress t a)
    have hat : a ∈ t.taxa := H.taxa_preserved ▸ ha
    have hp := Realization.leafAddress_mem_nodes hat
    have hleaf := H.leaves_preserved _ hp a (Realization.leafAddress_nodeAt hat)
    rw [← hleaf,H.encode_original hp]

end SupportSubdivision
end Camus
