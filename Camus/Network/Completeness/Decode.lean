module

public import Camus.Network.Completeness.Transport

@[expose] public section

namespace Camus.SupportSubdivision

variable {t : PhyloTree} {N : RootedNetwork} {S : Finset (ℕ × ℕ)}

noncomputable def decode (H : SupportSubdivision t N S)
    (hN : N.RootedBinaryLevelOne)
    (hpairs : Set.InjOn H.pairOf (N.edges \ S : Finset (ℕ × ℕ))) (v : ℕ) : ℕ :=
  if h : v ∈ (Realization.graph t H.extracted).vertices then
    ((H.vertexEquiv hN hpairs).symm ⟨v,h⟩).val else N.root

theorem decode_encode (H : SupportSubdivision t N S)
    (hN : N.RootedBinaryLevelOne)
    (hpairs : Set.InjOn H.pairOf (N.edges \ S : Finset (ℕ × ℕ)))
    {v : ℕ} (hv : v ∈ N.vertices) : H.decode hN hpairs (H.encode v) = v := by
  classical
  unfold decode
  rw [dite_eq_left (H.encode_mem_vertices hN hv)]
  exact congrArg Subtype.val ((H.vertexEquiv hN hpairs).symm_apply_apply ⟨v,hv⟩)

theorem encode_decode (H : SupportSubdivision t N S)
    (hN : N.RootedBinaryLevelOne)
    (hpairs : Set.InjOn H.pairOf (N.edges \ S : Finset (ℕ × ℕ)))
    {v : ℕ} (hv : v ∈ (Realization.graph t H.extracted).vertices) :
    H.encode (H.decode hN hpairs v) = v := by
  classical
  unfold decode
  rw [dite_eq_left hv]
  exact congrArg Subtype.val ((H.vertexEquiv hN hpairs).apply_symm_apply ⟨v,hv⟩)

theorem decode_injective (H : SupportSubdivision t N S)
    (hN : N.RootedBinaryLevelOne)
    (hpairs : Set.InjOn H.pairOf (N.edges \ S : Finset (ℕ × ℕ))) :
    Set.InjOn (H.decode hN hpairs) (Realization.graph t H.extracted).vertices := by
  intro u hu v hv huv
  have heq := congrArg H.encode huv
  rw [H.encode_decode hN hpairs hu,H.encode_decode hN hpairs hv] at heq
  exact heq

theorem decode_mem_vertices (H : SupportSubdivision t N S)
    (hN : N.RootedBinaryLevelOne)
    (hpairs : Set.InjOn H.pairOf (N.edges \ S : Finset (ℕ × ℕ)))
    {v : ℕ} (hv : v ∈ (Realization.graph t H.extracted).vertices) :
    H.decode hN hpairs v ∈ N.vertices := by
  classical
  unfold decode
  rw [dite_eq_left hv]
  exact ((H.vertexEquiv hN hpairs).symm ⟨v,hv⟩).property

theorem decode_vertices_image (H : SupportSubdivision t N S)
    (hN : N.RootedBinaryLevelOne)
    (hpairs : Set.InjOn H.pairOf (N.edges \ S : Finset (ℕ × ℕ))) :
    (Realization.graph t H.extracted).vertices.image (H.decode hN hpairs) = N.vertices := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hv
    exact H.decode_mem_vertices hN hpairs hu
  · intro hv
    exact Finset.mem_image.mpr ⟨H.encode v,H.encode_mem_vertices hN hv,H.decode_encode hN hpairs hv⟩

theorem encode_support_edges_image (H : SupportSubdivision t N S)
    (hN : N.RootedBinaryLevelOne)
    (hpairs : Set.InjOn H.pairOf (N.edges \ S : Finset (ℕ × ℕ)))
    (hsep : EdgeAbove.CycleSeparated t H.extracted) :
    S.image (Prod.map H.encode H.encode) = Realization.supportEdges t H.extracted := by
  classical
  calc
    S.image (Prod.map H.encode H.encode) =
      ((t.nodes.erase []).biUnion (fun p => wireEdges (H.wire p))).image
        (Prod.map H.encode H.encode) := congrArg
          (fun A : Finset (ℕ × ℕ) => A.image (Prod.map H.encode H.encode)) H.edges_covered
    _ = Realization.supportEdges t H.extracted := by
      rw [Finset.biUnion_image]
      apply Finset.biUnion_congr rfl
      intro p hp
      obtain ⟨hp0,hp⟩ := Finset.mem_erase.mp hp
      rw [← wireEdges_map,H.map_wire_eq hN hpairs hsep hp hp0]

theorem decode_support_edges_image (H : SupportSubdivision t N S)
    (hN : N.RootedBinaryLevelOne)
    (hpairs : Set.InjOn H.pairOf (N.edges \ S : Finset (ℕ × ℕ)))
    (hsep : EdgeAbove.CycleSeparated t H.extracted) :
    (Realization.supportEdges t H.extracted).image
      (Prod.map (H.decode hN hpairs) (H.decode hN hpairs)) = S := by
  classical
  rw [← H.encode_support_edges_image hN hpairs hsep,Finset.image_image]
  calc
    S.image ((Prod.map (H.decode hN hpairs) (H.decode hN hpairs)) ∘ (Prod.map H.encode H.encode)) =
      S.image id := by
        apply Finset.image_congr
        intro e he
        have hends := hN.2.1 e (H.switching.1 he)
        simp only [Function.comp_def,Prod.map,H.decode_encode hN hpairs hends.1,
          H.decode_encode hN hpairs hends.2,id_eq,Prod.mk.eta]
    _ = S := Finset.image_id

theorem decode_original (H : SupportSubdivision t N S)
    (hN : N.RootedBinaryLevelOne)
    (hpairs : Set.InjOn H.pairOf (N.edges \ S : Finset (ℕ × ℕ)))
    {p : Address} (hp : p ∈ t.nodes) :
    H.decode hN hpairs (Address.code p) = H.original p := by
  rw [← H.encode_original hp]
  exact H.decode_encode hN hpairs (H.original_mem_vertices hp)

theorem decode_donor (H : SupportSubdivision t N S)
    (hN : N.RootedBinaryLevelOne)
    (hpairs : Set.InjOn H.pairOf (N.edges \ S : Finset (ℕ × ℕ)))
    {e : ℕ × ℕ} (he : e ∈ N.edges \ S) :
    H.decode hN hpairs (Realization.donor t (H.pairOf e)) = e.1 := by
  rw [← H.encode_donor hN he]
  exact H.decode_encode hN hpairs (hN.2.1 e (Finset.mem_sdiff.mp he).1).1

theorem decode_recipient (H : SupportSubdivision t N S)
    (hN : N.RootedBinaryLevelOne)
    (hpairs : Set.InjOn H.pairOf (N.edges \ S : Finset (ℕ × ℕ)))
    {e : ℕ × ℕ} (he : e ∈ N.edges \ S) :
    H.decode hN hpairs (Realization.recipient t (H.pairOf e)) = e.2 := by
  rw [← H.encode_recipient hN he]
  exact H.decode_encode hN hpairs (hN.2.1 e (Finset.mem_sdiff.mp he).1).2

theorem decode_root (H : SupportSubdivision t N S)
    (hN : N.RootedBinaryLevelOne)
    (hpairs : Set.InjOn H.pairOf (N.edges \ S : Finset (ℕ × ℕ))) :
    H.decode hN hpairs (Realization.graph t H.extracted).root = N.root := by
  exact (H.decode_original hN hpairs t.root_mem_nodes).trans H.root_preserved

theorem decode_leaf (H : SupportSubdivision t N S)
    (hN : N.RootedBinaryLevelOne)
    (hpairs : Set.InjOn H.pairOf (N.edges \ S : Finset (ℕ × ℕ)))
    {a : ℕ} (ha : a ∈ (Realization.graph t H.extracted).taxa) :
    H.decode hN hpairs ((Realization.graph t H.extracted).leaf a) = N.leaf a := by
  have hp := Realization.leafAddress_mem_nodes ha
  exact (H.decode_original hN hpairs hp).trans
    (H.leaves_preserved _ hp a (Realization.leafAddress_nodeAt ha))

theorem decode_single_edges_image (H : SupportSubdivision t N S)
    (hN : N.RootedBinaryLevelOne)
    (hpairs : Set.InjOn H.pairOf (N.edges \ S : Finset (ℕ × ℕ)))
    (hsep : EdgeAbove.CycleSeparated t H.extracted)
    {e : ℕ × ℕ} (he : e ∈ N.edges \ S) :
    (insert (Realization.donor t (H.pairOf e),Realization.recipient t (H.pairOf e))
      (Realization.supportEdges t H.extracted)).image
        (Prod.map (H.decode hN hpairs) (H.decode hN hpairs)) = insert e S := by
  classical
  rw [Finset.image_insert,H.decode_support_edges_image hN hpairs hsep]
  simp only [Prod.map,H.decode_donor hN hpairs he,H.decode_recipient hN hpairs he,
    Prod.mk.eta]

end Camus.SupportSubdivision
