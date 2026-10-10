module

public import Camus.Network.Completeness.Order
public import Camus.Network.Realization.CycleWires
public import Mathlib.Data.List.Permutation

/-!
# The wires of N are the canonical wires

For each non-root vertex `p` of `T`, the encoding maps the wire of `p` in `N`, vertex by vertex
and in order, to the wire of `p` in the canonical network `Realization.graph t H.extracted`. The
interiors agree as sets: both consist of the names of the endpoints of non-tree edges with
anchor `p`. As the extracted family is cycle-separated, the canonical interior is at most one
outer endpoint followed by at most one ghost donor, and the reverse order cannot occur in `N`
(`SupportSubdivision.no_ghost_before_endpoint`).

## Main results

* `SupportSubdivision.map_wire_eq`: `(H.wire p).map H.encode = Realization.wire t H.extracted p`.
-/

@[expose] public section

namespace Camus

/-- A list of length at least two with first element `a` and last element `b` is
`a :: (l.tail.dropLast ++ [b])`. -/
theorem wire_decompose {l : List ℕ} (hlen : 2 ≤ l.length) {a b : ℕ}
    (hhead : l.head? = some a) (hlast : l.getLast? = some b) :
    l = a :: (l.tail.dropLast ++ [b]) := by
  cases l with
  | nil => simp at hlen
  | cons x l =>
    cases l with
    | nil => simp at hlen
    | cons y l =>
      simp only [List.head?_cons,Option.some.injEq] at hhead
      subst x
      have htail : (y :: l).getLast? = some b := by simpa using hlast
      exact congrArg (List.cons a) (List.dropLast_append_getLast? b (htail ▸ Option.mem_some_self
          b)).symm

namespace SupportSubdivision

variable {t : PhyloTree} {N : RootedNetwork} {S : Finset (ℕ × ℕ)}

/-- The encoding maps the interior of the wire of `p` onto the interior of the canonical wire
`Realization.wire t H.extracted p`. -/
theorem encoded_interior_eq (H : SupportSubdivision t N S)
    (hN : N.RootedBinaryLevelOne) {p : Address} (hp : p ∈ t.nodes) (hp0 : p ≠ []) :
    (wireInterior (H.wire p)).image H.encode =
      wireInterior (Realization.wire t H.extracted p) := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨e,he,hew⟩ := H.interior_is_deleted_endpoint hN hp hp0 hu
    have heE : H.pairOf e ∈ H.extracted := Finset.mem_image.mpr ⟨e,he,rfl⟩
    apply Realization.mem_wireInterior.mpr
    refine ⟨H.pairOf e,heE,?_⟩
    rcases hew with hsource | htarget
    · have hanchor : H.anchor e.1 = p := H.anchor_eq hp hp0 (hsource ▸ hu)
      exact Or.inl ⟨hanchor,(hsource ▸ H.encode_donor hN he)⟩
    · have hanchor : H.anchor e.2 = p := H.anchor_eq hp hp0 (htarget ▸ hu)
      exact Or.inr ⟨hanchor,(htarget ▸ H.encode_recipient hN he)⟩
  · intro hv
    obtain ⟨q,hq,hend⟩ := Realization.mem_wireInterior.mp hv
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hq
    rcases hend with ⟨hsource,hcode⟩ | ⟨htarget,hcode⟩
    · have hspec := H.deleted_source_anchor_spec hN he
      have hinner : e.1 ∈ wireInterior (H.wire p) := by
        simpa only [pairOf] using (hsource ▸ hspec.2.2)
      exact Finset.mem_image.mpr ⟨e.1,hinner,(H.encode_donor hN he).trans hcode.symm⟩
    · have hspec := H.deleted_target_anchor_spec hN he
      have hinner : e.2 ∈ wireInterior (H.wire p) := by
        simpa only [pairOf] using (htarget ▸ hspec.2.2)
      exact Finset.mem_image.mpr ⟨e.2,hinner,(H.encode_recipient hN he).trans hcode.symm⟩

/-- The encoded interior of the wire of `p` is not `[g, o]` with `g` a ghost donor and `o` an
outer endpoint of the canonical wire (`SupportSubdivision.no_ghost_before_endpoint`). -/
theorem encoded_ghost_before_outer_impossible (H : SupportSubdivision t N S)
    (hN : N.RootedBinaryLevelOne)
    (hpairs : Set.InjOn H.pairOf (N.edges \ S : Finset (ℕ × ℕ)))
    {p : Address} (hp : p ∈ t.nodes) (hp0 : p ≠ []) {g o : ℕ}
    (hg : g ∈ Realization.ghostEndpoints t H.extracted p)
    (ho : o ∈ Realization.outerEndpoints t H.extracted p)
    (hbad : ((H.wire p).tail.dropLast.map H.encode) = [g,o]) : False := by
  classical
  have hlen : (H.wire p).tail.dropLast.length = 2 := by
    have := congrArg List.length hbad
    simpa using this
  obtain ⟨u,v,hmid⟩ := List.length_eq_two.mp hlen
  have hu : u ∈ wireInterior (H.wire p) := List.mem_toFinset.mpr (by rw [hmid]; simp)
  have hv : v ∈ wireInterior (H.wire p) := List.mem_toFinset.mpr (by rw [hmid]; simp)
  have huN := H.interior_mem_vertices hp hp0 hu
  have hvN := H.interior_mem_vertices hp hp0 hv
  simp only [hmid,List.map_cons,List.map_nil,List.cons.injEq] at hbad
  obtain ⟨eg,heg,hgu,hgt,hgcode⟩ := Realization.mem_ghostEndpoints.mp hg
  obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp heg
  have huEq : u = e.1 := H.encode_injective_vertices hN hpairs huN
    (hN.2.1 _ (Finset.mem_sdiff.mp he).1).1
    ((hbad.1.trans hgcode).trans (H.encode_donor hN he).symm)
  obtain ⟨of,hof,hout⟩ := Realization.mem_outerEndpoints.mp ho
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hof
  have hchosen : ∃ w, w ∈ N.vertices ∧ (w = f.1 ∨ w = f.2) ∧ H.encode w = o := by
    rcases hout with ⟨hfu,hft,hoc⟩ | ⟨hfw,hoc⟩
    · exact ⟨f.1,(hN.2.1 _ (Finset.mem_sdiff.mp hf).1).1,Or.inl rfl,
        (H.encode_donor hN hf).trans hoc.symm⟩
    · exact ⟨f.2,(hN.2.1 _ (Finset.mem_sdiff.mp hf).1).2,Or.inr rfl,
        (H.encode_recipient hN hf).trans hoc.symm⟩
  obtain ⟨w,hwN,hw,hwencode⟩ := hchosen
  have hvEq : v = w := H.encode_injective_vertices hN hpairs hvN hwN
    (hbad.2.1.trans hwencode.symm)
  have hef : e ≠ f := by
    intro hef
    subst f
    rcases hout with ⟨hfu,hft,hoc⟩ | ⟨hfw,hoc⟩
    · exact hft hgt
    · exact H.deleted_anchors_ne hN he (hgu.trans hfw.symm)
  have hwire := wire_decompose (H.wire_laws p hp hp0).1
    (H.wire_laws p hp hp0).2.2.1 (H.wire_laws p hp hp0).2.2.2.1
  rw [hmid,huEq,hvEq] at hwire
  exact H.no_ghost_before_endpoint hN he hf hef hp hp0 hgt hw hwire

/-- Assume that distinct non-tree edges have distinct pairs and that the extracted family is
cycle-separated. For a non-root vertex `p` of `T`, the encoding maps the wire of `p` in `N`, as a
list, to the wire of `p` in `Realization.graph t H.extracted`. The interiors agree as sets; the
canonical interior is at most one outer endpoint followed by at most one ghost donor, and the
other order cannot occur in `N`. -/
theorem map_wire_eq (H : SupportSubdivision t N S)
    (hN : N.RootedBinaryLevelOne)
    (hpairs : Set.InjOn H.pairOf (N.edges \ S : Finset (ℕ × ℕ)))
    (hsep : EdgeAbove.CycleSeparated t H.extracted)
    {p : Address} (hp : p ∈ t.nodes) (hp0 : p ≠ []) :
    (H.wire p).map H.encode = Realization.wire t H.extracted p := by
  classical
  let m := (H.wire p).tail.dropLast
  let M := m.map H.encode
  let O := Realization.outerEndpoints t H.extracted p
  let G := Realization.ghostEndpoints t H.extracted p
  have hmN : m.Nodup := (H.wire_laws p hp hp0).2.1.tail.sublist (List.dropLast_sublist _)
  have hMN : M.Nodup := hmN.map_on (fun u hu v hv huv =>
    H.encode_injective_vertices hN hpairs
      (H.interior_mem_vertices hp hp0 (List.mem_toFinset.mpr hu))
      (H.interior_mem_vertices hp hp0 (List.mem_toFinset.mpr hv)) huv)
  have hOGN : (O ++ G).Nodup :=
    (Realization.outerEndpoints_nodup t H.extracted hsep.1 p).append
      (Realization.ghostEndpoints_nodup t H.extracted hsep.1 p)
      (Realization.outer_ghost_disjoint t H.extracted hsep.1 p)
  have hsets : M.toFinset = (O ++ G).toFinset := by
    change (m.map H.encode).toFinset = _
    have hbridge : (m.map H.encode).toFinset = (wireInterior (H.wire p)).image H.encode := by
      ext v
      simp only [m,wireInterior,List.mem_toFinset,List.mem_map,Finset.mem_image]
    exact hbridge.trans ((H.encoded_interior_eq hN hp hp0).trans (Realization.wireInterior_eq t
        H.extracted p))
  have hperm : M.Perm (O ++ G) := List.perm_of_nodup_nodup_toFinset_eq hMN hOGN hsets
  have hOC : O = [] ∨ ∃ o, O = [o] := by
    cases ho : O with
    | nil => exact Or.inl rfl
    | cons o os =>
      apply Or.inr
      refine ⟨o,?_⟩
      have heq := Realization.outerEndpoints_eq_singleton hsep (p := p)
        (v := o) (by change o ∈ O; rw [ho]; simp)
      change O = [o] at heq
      simpa only [ho] using heq
  have hGC : G = [] ∨ ∃ g, G = [g] := by
    cases hg : G with
    | nil => exact Or.inl rfl
    | cons g gs =>
      apply Or.inr
      refine ⟨g,?_⟩
      have heq := Realization.ghostEndpoints_eq_singleton hsep (p := p)
        (v := g) (by change g ∈ G; rw [hg]; simp)
      change G = [g] at heq
      simpa only [hg] using heq
  have hmid : M = O ++ G := by
    rcases hOC with ho | ⟨o,ho⟩ <;> rcases hGC with hg | ⟨g,hg⟩
    · simpa only [ho,hg,List.nil_append,List.perm_nil] using hperm
    · simpa only [ho,hg,List.nil_append,List.perm_singleton] using hperm
    · simpa only [ho,hg,List.append_nil,List.perm_singleton] using hperm
    · have hpairsM : M = [o,g] ∨ M = [g,o] := List.perm_pair.mp
        (by simpa only [ho,hg,List.singleton_append] using hperm)
      rcases hpairsM with hgood | hbad
      · simpa only [ho,hg,List.singleton_append] using hgood
      · exact False.elim (H.encoded_ghost_before_outer_impossible hN hpairs hp hp0
          (by change g ∈ G; rw [hg]; simp) (by change o ∈ O; rw [ho]; simp) hbad)
  have hdecomp := wire_decompose (H.wire_laws p hp hp0).1
    (H.wire_laws p hp hp0).2.2.1 (H.wire_laws p hp hp0).2.2.2.1
  have hmap := congrArg (List.map H.encode) hdecomp
  have hpParent := t.nodes_prefix_closed hp (parent_prefix p)
  simp only [List.map_cons,List.map_append,
    H.encode_original hp,H.encode_original hpParent] at hmap
  calc
    (H.wire p).map H.encode = Address.code (parent p) :: (M ++ [Address.code p]) := hmap
    _ = Realization.wire t H.extracted p := by rw [hmid]; rfl

end SupportSubdivision
end Camus
