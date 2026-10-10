module

public import Camus.Network.Completeness.Admissible
public import Camus.Network.Realization.Basic

@[expose] public section

namespace Camus.SupportSubdivision

variable {t : PhyloTree} {N : RootedNetwork} {S : Finset (ℕ × ℕ)}

noncomputable def originalAddress (H : SupportSubdivision t N S) (v : ℕ) : Address :=
  if h : ∃ p ∈ t.nodes, H.original p = v then h.choose else []

theorem originalAddress_original (H : SupportSubdivision t N S) {p : Address}
    (hp : p ∈ t.nodes) : H.originalAddress (H.original p) = p := by
  classical
  have hex : ∃ q ∈ t.nodes, H.original q = H.original p := ⟨p,hp,rfl⟩
  unfold originalAddress
  rw [dite_eq_left hex]
  exact H.original_injective hex.choose_spec.1 hp hex.choose_spec.2

noncomputable def encode (H : SupportSubdivision t N S) (v : ℕ) : ℕ :=
  if h : ∃ p ∈ t.nodes, H.original p = v then Address.code h.choose else
  if h : ∃ e ∈ N.edges \ S, e.1 = v then Realization.donor t (H.pairOf h.choose) else
  if h : ∃ e ∈ N.edges \ S, e.2 = v then Realization.recipient t (H.pairOf h.choose) else
  Address.code []

theorem encode_original (H : SupportSubdivision t N S) {p : Address}
    (hp : p ∈ t.nodes) : H.encode (H.original p) = Address.code p := by
  classical
  have hex : ∃ q ∈ t.nodes, H.original q = H.original p := ⟨p,hp,rfl⟩
  unfold encode
  rw [dite_eq_left hex]
  congr 1
  exact H.original_injective hex.choose_spec.1 hp hex.choose_spec.2

theorem deleted_source_ne_target (H : SupportSubdivision t N S)
    (hN : N.RootedBinaryLevelOne) {e f : ℕ × ℕ}
    (he : e ∈ N.edges \ S) (hf : f ∈ N.edges \ S) : e.1 ≠ f.2 := by
  have hs := H.deleted_source_tree_vertex hN he
  have ht := RootedNetwork.deleted_edge_target_reticulation hN H.switching hf
  intro heq
  rw [heq] at hs
  omega

theorem encode_donor (H : SupportSubdivision t N S) (hN : N.RootedBinaryLevelOne)
    {e : ℕ × ℕ} (he : e ∈ N.edges \ S) :
    H.encode e.1 = Realization.donor t (H.pairOf e) := by
  classical
  have hno : ¬∃ p ∈ t.nodes, H.original p = e.1 := by
    intro ho
    exact H.deleted_source_not_original hN he (Finset.mem_image.mpr ho)
  have hex : ∃ f ∈ N.edges \ S, f.1 = e.1 := ⟨e,he,rfl⟩
  unfold encode
  rw [dite_eq_right hno, dite_eq_left hex]
  have hchosen : hex.choose = e := RootedNetwork.deleted_sources_injective
    hN H.switching hex.choose_spec.1 he hex.choose_spec.2
  rw [hchosen]

theorem encode_recipient (H : SupportSubdivision t N S) (hN : N.RootedBinaryLevelOne)
    {e : ℕ × ℕ} (he : e ∈ N.edges \ S) :
    H.encode e.2 = Realization.recipient t (H.pairOf e) := by
  classical
  have hno : ¬∃ p ∈ t.nodes, H.original p = e.2 := by
    intro ho
    exact H.deleted_target_not_original hN he (Finset.mem_image.mpr ho)
  have hnodonor : ¬∃ f ∈ N.edges \ S, f.1 = e.2 := by
    rintro ⟨f,hf,hfe⟩
    exact H.deleted_source_ne_target hN hf he hfe
  have hex : ∃ f ∈ N.edges \ S, f.2 = e.2 := ⟨e,he,rfl⟩
  unfold encode
  rw [dite_eq_right hno, dite_eq_right hnodonor, dite_eq_left hex]
  have hchosen : hex.choose = e := RootedNetwork.deleted_targets_injective
    hN H.switching hex.choose_spec.1 he hex.choose_spec.2
  rw [hchosen]

theorem vertex_endpoint_cases (H : SupportSubdivision t N S)
    (hN : N.RootedBinaryLevelOne) {v : ℕ} (hv : v ∈ N.vertices) :
    (∃ p ∈ t.nodes, v = H.original p) ∨
      (∃ e ∈ N.edges \ S, v = e.1) ∨ (∃ e ∈ N.edges \ S, v = e.2) := by
  rcases H.vertex_cases hv with ho | hi
  · obtain ⟨p,hp,hpv⟩ := ho
    exact Or.inl ⟨p,hp,hpv.symm⟩
  · obtain ⟨e,he,hev⟩ := H.interior_is_deleted_endpoint hN hi.1 hi.2.1 hi.2.2
    rcases hev with hs | ht
    · exact Or.inr (Or.inl ⟨e,he,hs.symm⟩)
    · exact Or.inr (Or.inr ⟨e,he,ht.symm⟩)

theorem extracted_subset_candidates (H : SupportSubdivision t N S)
    (hN : N.RootedBinaryLevelOne) : H.extracted ⊆ EdgeAbove.candidates t := by
  classical
  intro e he
  obtain ⟨f,hfdel,rfl⟩ := Finset.mem_image.mp he
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨(H.deleted_source_anchor_spec hN hfdel).1,
      (H.deleted_target_anchor_spec hN hfdel).1⟩, H.deleted_pair_admissible hN hfdel⟩

theorem encode_mem_vertices (H : SupportSubdivision t N S)
    (hN : N.RootedBinaryLevelOne) {v : ℕ} (hv : v ∈ N.vertices) :
    H.encode v ∈ (Realization.graph t H.extracted).vertices := by
  classical
  rcases H.vertex_endpoint_cases hN hv with ho | hd | hr
  · obtain ⟨p,hp,rfl⟩ := ho
    rw [H.encode_original hp]
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p,hp,rfl⟩)
  · obtain ⟨e,he,rfl⟩ := hd
    rw [H.encode_donor hN he]
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨H.pairOf e,Finset.mem_image.mpr ⟨e,he,rfl⟩,Finset.mem_insert_self _ _⟩)
  · obtain ⟨e,he,rfl⟩ := hr
    rw [H.encode_recipient hN he]
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨H.pairOf e,Finset.mem_image.mpr ⟨e,he,rfl⟩,
        Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))⟩)

theorem encode_surjective_vertices (H : SupportSubdivision t N S)
    (hN : N.RootedBinaryLevelOne) {v : ℕ}
    (hv : v ∈ (Realization.graph t H.extracted).vertices) :
    ∃ u ∈ N.vertices, H.encode u = v := by
  classical
  rcases Finset.mem_union.mp hv with ho | hf
  · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ho
    exact ⟨H.original p,H.original_mem_vertices hp,H.encode_original hp⟩
  · obtain ⟨e,he,hve⟩ := Finset.mem_biUnion.mp hf
    obtain ⟨f,hfdel,rfl⟩ := Finset.mem_image.mp he
    rcases Finset.mem_insert.mp hve with hd | hr
    · subst v
      exact ⟨f.1,(hN.2.1 f (Finset.mem_sdiff.mp hfdel).1).1,H.encode_donor hN hfdel⟩
    · have heq := Finset.mem_singleton.mp hr
      subst v
      exact ⟨f.2,(hN.2.1 f (Finset.mem_sdiff.mp hfdel).1).2,H.encode_recipient hN hfdel⟩

theorem encode_injective_vertices (H : SupportSubdivision t N S)
    (hN : N.RootedBinaryLevelOne)
    (hpairs : Set.InjOn H.pairOf (N.edges \ S : Finset (ℕ × ℕ))) :
    Set.InjOn H.encode N.vertices := by
  intro u hu v hv huv
  rcases H.vertex_endpoint_cases hN hu with ho | hd | hr <;>
    rcases H.vertex_endpoint_cases hN hv with ho' | hd' | hr'
  · obtain ⟨p,hp,rfl⟩ := ho
    obtain ⟨q,hq,rfl⟩ := ho'
    rw [H.encode_original hp,H.encode_original hq] at huv
    exact congrArg H.original (Address.code_injective huv)
  · obtain ⟨p,hp,rfl⟩ := ho
    obtain ⟨e,he,rfl⟩ := hd'
    rw [H.encode_original hp,H.encode_donor hN he] at huv
    exact False.elim (Realization.donor_ne_code (H.pairOf e) hp huv.symm)
  · obtain ⟨p,hp,rfl⟩ := ho
    obtain ⟨e,he,rfl⟩ := hr'
    rw [H.encode_original hp,H.encode_recipient hN he] at huv
    exact False.elim (Realization.recipient_ne_code (H.pairOf e) hp huv.symm)
  · obtain ⟨e,he,rfl⟩ := hd
    obtain ⟨p,hp,rfl⟩ := ho'
    rw [H.encode_donor hN he,H.encode_original hp] at huv
    exact False.elim (Realization.donor_ne_code (H.pairOf e) hp huv)
  · obtain ⟨e,he,rfl⟩ := hd
    obtain ⟨f,hf,rfl⟩ := hd'
    rw [H.encode_donor hN he,H.encode_donor hN hf] at huv
    have hec := H.extracted_subset_candidates hN (Finset.mem_image.mpr ⟨e,he,rfl⟩)
    have hfc := H.extracted_subset_candidates hN (Finset.mem_image.mpr ⟨f,hf,rfl⟩)
    have hef := hpairs he hf (Realization.donor_injective t hec hfc huv)
    exact congrArg Prod.fst hef
  · obtain ⟨e,he,rfl⟩ := hd
    obtain ⟨f,hf,rfl⟩ := hr'
    rw [H.encode_donor hN he,H.encode_recipient hN hf] at huv
    exact False.elim (Realization.donor_ne_recipient t (H.pairOf e) (H.pairOf f) huv)
  · obtain ⟨e,he,rfl⟩ := hr
    obtain ⟨p,hp,rfl⟩ := ho'
    rw [H.encode_recipient hN he,H.encode_original hp] at huv
    exact False.elim (Realization.recipient_ne_code (H.pairOf e) hp huv)
  · obtain ⟨e,he,rfl⟩ := hr
    obtain ⟨f,hf,rfl⟩ := hd'
    rw [H.encode_recipient hN he,H.encode_donor hN hf] at huv
    exact False.elim (Realization.donor_ne_recipient t (H.pairOf f) (H.pairOf e) huv.symm)
  · obtain ⟨e,he,rfl⟩ := hr
    obtain ⟨f,hf,rfl⟩ := hr'
    rw [H.encode_recipient hN he,H.encode_recipient hN hf] at huv
    have hec := H.extracted_subset_candidates hN (Finset.mem_image.mpr ⟨e,he,rfl⟩)
    have hfc := H.extracted_subset_candidates hN (Finset.mem_image.mpr ⟨f,hf,rfl⟩)
    have hef := hpairs he hf (Realization.recipient_injective t hec hfc huv)
    exact congrArg Prod.snd hef

noncomputable def vertexEquiv (H : SupportSubdivision t N S)
    (hN : N.RootedBinaryLevelOne)
    (hpairs : Set.InjOn H.pairOf (N.edges \ S : Finset (ℕ × ℕ))) :
    N.vertices ≃ (Realization.graph t H.extracted).vertices := by
  let f : N.vertices → (Realization.graph t H.extracted).vertices :=
    fun v => ⟨H.encode v.val,H.encode_mem_vertices hN v.property⟩
  apply Equiv.ofBijective f
  constructor
  · intro u v huv
    exact Subtype.ext (H.encode_injective_vertices hN hpairs u.property v.property
      (congrArg Subtype.val huv))
  · intro v
    obtain ⟨u,hu,heq⟩ := H.encode_surjective_vertices hN v.property
    exact ⟨⟨u,hu⟩,Subtype.ext heq⟩

end Camus.SupportSubdivision
