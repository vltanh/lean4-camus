module

public import Camus.Network.Realization.Basic

/-!
# The canonical network of an edge family: wires

We identify a vertex `p` of `T` with its code `Address.code p`. In `Realization.graph t E` the
edge of `T` from `parent(p)` to a non-root vertex `p` is replaced by a directed path, the wire
`Realization.wire t E p` above `p`. It runs from `parent(p)` through the fresh vertices placed on
this edge to `p`. These are, in order, the outer endpoints (`Realization.outerEndpoints`): the
donor `u′` of each pair `(u, w) ∈ E` with `u = p ≠ lca(u, w)` and the recipient `w′` of each
pair with `w = p`; then the ghost donors (`Realization.ghostEndpoints`): the donor `u′` of each
pair with `u = p = lca(u, w)`, whose recipient end `w` lies below `u`. For a family of admissible
pairs, this file proves that the vertices inside the wire above `p` are the donors of the pairs
with donor end `p` and the recipients of the pairs with recipient end `p`, that the wire
interiors are pairwise disjoint and contain no vertex of `T`, and that each wire is a path from
`parent(p)` to `p`.

## Main results

* `Realization.mem_wireInterior`: the vertices inside the wire above `p` are the donors `u′` of
  the pairs `(u, w) ∈ E` with `u = p` and the recipients `w′` of the pairs with `w = p`.
* `Realization.donor_mem_wireInterior_iff`, `Realization.recipient_mem_wireInterior_iff`: `u′`
  is inside the wire above `p` iff `u = p`, and `w′` iff `w = p`.
* `Realization.wireInterior_disjoint_original`, `Realization.interiors_disjoint`: the wire
  interiors contain no vertex of `T` and are pairwise disjoint.
* `Realization.wire_nodup`, `Realization.wire_head`, `Realization.wire_last`: the wire above `p`
  is a path from `parent(p)` to `p`.
* `Realization.vertices_covered`: the vertices of the network are the vertices of `T` and the
  vertices inside the wires.

## The order on a shared wire

A wire can carry an endpoint of one cycle and the ghost donor of another. Suppose the pair `e`
has an outer endpoint `x` on the wire above `p` and the pair `f` has its ghost donor `g` there.
The cycle of `e` contains `parent(p)` and the part of the wire from `parent(p)` to `x`; the
cycle of `f` contains the part of the wire from `g` to `p`. These cycles are disjoint only if `x`
comes before `g`, the order used by `Realization.wire`. For a cycle-separated family each wire
carries at most one vertex of each kind (`Realization.outerEndpoints_eq_singleton`,
`Realization.ghostEndpoints_eq_singleton`).
-/

@[expose] public section

namespace Camus.Realization

/-- A fresh vertex determines its pair: if `v` is the donor or the recipient of the admissible
pair `e`, and also of the admissible pair `f`, then `e = f`. -/
theorem endpoint_owner_unique {t : PhyloTree} {e f : Pair}
    (he : e ∈ EdgeAbove.candidates t) (hf : f ∈ EdgeAbove.candidates t)
    {v : ℕ} (hv : v = donor t e ∨ v = recipient t e)
    (hw : v = donor t f ∨ v = recipient t f) : e = f := by
  rcases hv with hd | hr <;> rcases hw with hd' | hr'
  · exact donor_injective t he hf (hd.symm.trans hd')
  · exact False.elim (donor_ne_recipient t e f (hd.symm.trans hr'))
  · exact False.elim (donor_ne_recipient t f e (hd'.symm.trans hr))
  · exact recipient_injective t he hf (hr.symm.trans hr')

/-- The outer endpoints on the wire above `p` are the donors `u′` of the pairs `(u, w) ∈ E`
with `u = p ≠ lca(u, w)` and the recipients `w′` of the pairs with `w = p`. -/
theorem mem_outerEndpoints {t : PhyloTree} {E : Finset Pair} {p : Address} {v : ℕ} :
    v ∈ outerEndpoints t E p ↔
      ∃ e ∈ E, (e.1 = p ∧ EdgeAbove.target e ≠ p ∧ v = donor t e) ∨
        (e.2 = p ∧ v = recipient t e) := by
  classical
  simp only [outerEndpoints, List.mem_flatMap, Finset.mem_toList, List.mem_append]
  constructor
  · rintro ⟨e, he, h | h⟩
    · split_ifs at h with hh
      · exact ⟨e, he, Or.inl ⟨hh.1, hh.2, List.mem_singleton.mp h⟩⟩
      · simp at h
    · split_ifs at h with hh
      · exact ⟨e, he, Or.inr ⟨hh, List.mem_singleton.mp h⟩⟩
      · simp at h
  · rintro ⟨e, he, (⟨hu, ht, rfl⟩ | ⟨hw, rfl⟩)⟩
    · exact ⟨e, he, Or.inl (by simp [hu, ht])⟩
    · exact ⟨e, he, Or.inr (by simp [hw])⟩

/-- The ghost donors on the wire above `p` are the donors `u′` of the pairs `(u, w) ∈ E` with
`u = p = lca(u, w)`. -/
theorem mem_ghostEndpoints {t : PhyloTree} {E : Finset Pair} {p : Address} {v : ℕ} :
    v ∈ ghostEndpoints t E p ↔
      ∃ e ∈ E, e.1 = p ∧ EdgeAbove.target e = p ∧ v = donor t e := by
  classical
  simp only [ghostEndpoints, List.mem_flatMap, Finset.mem_toList]
  constructor
  · rintro ⟨e, he, h⟩
    split_ifs at h with hh
    · exact ⟨e, he, hh.1, hh.2, List.mem_singleton.mp h⟩
    · simp at h
  · rintro ⟨e, he, hu, ht, rfl⟩
    exact ⟨e, he, by simp [hu, ht]⟩

/-- The interior of the wire above `p` consists of its outer endpoints and ghost donors. -/
theorem wireInterior_eq (t : PhyloTree) (E : Finset Pair) (p : Address) :
    wireInterior (wire t E p) = (outerEndpoints t E p ++ ghostEndpoints t E p).toFinset := by
  simp [wireInterior, wire, List.append_assoc]

/-- The vertices inside the wire above `p` are the donors `u′` of the pairs `(u, w) ∈ E` with
`u = p` and the recipients `w′` of the pairs with `w = p`. -/
theorem mem_wireInterior {t : PhyloTree} {E : Finset Pair} {p : Address} {v : ℕ} :
    v ∈ wireInterior (wire t E p) ↔
      ∃ e ∈ E, (e.1 = p ∧ v = donor t e) ∨ (e.2 = p ∧ v = recipient t e) := by
  classical
  rw [wireInterior_eq]
  simp only [List.mem_toFinset, List.mem_append, mem_outerEndpoints, mem_ghostEndpoints]
  constructor
  · rintro (⟨e, he, (⟨hu, _, hv⟩ | ⟨hw, hv⟩)⟩ | ⟨e, he, hu, _, hv⟩)
    · exact ⟨e, he, Or.inl ⟨hu, hv⟩⟩
    · exact ⟨e, he, Or.inr ⟨hw, hv⟩⟩
    · exact ⟨e, he, Or.inl ⟨hu, hv⟩⟩
  · rintro ⟨e, he, (⟨hu, hv⟩ | ⟨hw, hv⟩)⟩
    · by_cases ht : EdgeAbove.target e = p
      · exact Or.inr ⟨e, he, hu, ht, hv⟩
      · exact Or.inl ⟨e, he, Or.inl ⟨hu, ht, hv⟩⟩
    · exact Or.inl ⟨e, he, Or.inr ⟨hw, hv⟩⟩

/-- No vertex inside a wire is a vertex of `T`. -/
theorem wireInterior_disjoint_original (t : PhyloTree) (E : Finset Pair) (p : Address) :
    Disjoint (wireInterior (wire t E p)) (t.nodes.image Address.code) := by
  classical
  rw [Finset.disjoint_left]
  intro v hv hc
  obtain ⟨e, _, he⟩ := mem_wireInterior.mp hv
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hc
  rcases he with ⟨_, hd⟩ | ⟨_, hr⟩
  · exact donor_ne_code e hq hd.symm
  · exact recipient_ne_code e hq hr.symm

/-- For a family of admissible pairs, the wires above distinct vertices have disjoint
interiors. -/
theorem interiors_disjoint (t : PhyloTree) (E : Finset Pair)
    (hE : E ⊆ EdgeAbove.candidates t) {p q : Address} (hpq : p ≠ q) :
    Disjoint (wireInterior (wire t E p)) (wireInterior (wire t E q)) := by
  classical
  rw [Finset.disjoint_left]
  intro v hv hw
  obtain ⟨e, he, hpe⟩ := mem_wireInterior.mp hv
  obtain ⟨f, hf, hqf⟩ := mem_wireInterior.mp hw
  have howner := endpoint_owner_unique (hE he) (hE hf)
    (hpe.elim (fun h => Or.inl h.2) (fun h => Or.inr h.2))
    (hqf.elim (fun h => Or.inl h.2) (fun h => Or.inr h.2))
  subst f
  rcases hpe with ⟨hpu, hd⟩ | ⟨hpw, hr⟩ <;>
    rcases hqf with ⟨hqu, hd'⟩ | ⟨hqw, hr'⟩
  · exact hpq (hpu.symm.trans hqu)
  · exact donor_ne_recipient t e e (hd.symm.trans hr')
  · exact donor_ne_recipient t e e (hd'.symm.trans hr)
  · exact hpq (hpw.symm.trans hqw)

/-- The vertices of the wire above `p` are `parent(p)`, the vertices inside it, and `p`. -/
theorem mem_wire {t : PhyloTree} {E : Finset Pair} {p : Address} {v : ℕ} :
    v ∈ wire t E p ↔ v = Address.code (parent p) ∨
      v ∈ wireInterior (wire t E p) ∨ v = Address.code p := by
  rw [wireInterior_eq]
  simp [wire, List.append_assoc, or_assoc]

/-- For `(u, w)` in a family `E` of admissible pairs, the donor `u′` is inside the wire above
`p` iff `u = p`. -/
theorem donor_mem_wireInterior_iff {t : PhyloTree} {E : Finset Pair}
    (hE : E ⊆ EdgeAbove.candidates t) {e : Pair} (he : e ∈ E) {p : Address} :
    donor t e ∈ wireInterior (wire t E p) ↔ e.1 = p := by
  classical
  constructor
  · intro hv
    obtain ⟨f, hf, hfmem⟩ := mem_wireInterior.mp hv
    rcases hfmem with ⟨hfu, hd⟩ | ⟨hfw, hr⟩
    · exact donor_injective t (hE he) (hE hf) hd ▸ hfu
    · exact False.elim (donor_ne_recipient t e f hr)
  · intro h
    exact mem_wireInterior.mpr ⟨e, he, Or.inl ⟨h, rfl⟩⟩

/-- For `(u, w)` in a family `E` of admissible pairs, the recipient `w′` is inside the wire
above `p` iff `w = p`. -/
theorem recipient_mem_wireInterior_iff {t : PhyloTree} {E : Finset Pair}
    (hE : E ⊆ EdgeAbove.candidates t) {e : Pair} (he : e ∈ E) {p : Address} :
    recipient t e ∈ wireInterior (wire t E p) ↔ e.2 = p := by
  classical
  constructor
  · intro hv
    obtain ⟨f, hf, hfmem⟩ := mem_wireInterior.mp hv
    rcases hfmem with ⟨hfu, hd⟩ | ⟨hfw, hr⟩
    · exact False.elim (donor_ne_recipient t f e hd.symm)
    · exact recipient_injective t (hE he) (hE hf) hr ▸ hfw
  · intro h
    exact mem_wireInterior.mpr ⟨e, he, Or.inr ⟨h, rfl⟩⟩

private theorem outer_atom_mem_owner (t : PhyloTree) (e : Pair) (p : Address) {v : ℕ}
    (hv : v ∈ (if e.1 = p ∧ EdgeAbove.target e ≠ p then [donor t e] else []) ++
      (if e.2 = p then [recipient t e] else [])) :
    v = donor t e ∨ v = recipient t e := by
  rcases List.mem_append.mp hv with hd | hr
  · split_ifs at hd with h
    · exact Or.inl (List.mem_singleton.mp hd)
    · simp at hd
  · split_ifs at hr with h
    · exact Or.inr (List.mem_singleton.mp hr)
    · simp at hr

/-- For a family of admissible pairs, the outer endpoints on a wire are listed without
repetition. -/
theorem outerEndpoints_nodup (t : PhyloTree) (E : Finset Pair)
    (hE : E ⊆ EdgeAbove.candidates t) (p : Address) :
    (outerEndpoints t E p).Nodup := by
  classical
  apply List.nodup_flatMap.mpr
  constructor
  · intro e he
    split_ifs <;> simp [donor_ne_recipient]
  · apply (Finset.nodup_toList E).imp_of_mem
    intro e f he hf hne
    change List.Disjoint _ _
    rw [List.disjoint_left]
    intro v hv hw
    exact hne (endpoint_owner_unique (hE (Finset.mem_toList.mp he))
      (hE (Finset.mem_toList.mp hf))
      (outer_atom_mem_owner t e p hv) (outer_atom_mem_owner t f p hw))

/-- For a family of admissible pairs, the ghost donors on a wire are listed without
repetition. -/
theorem ghostEndpoints_nodup (t : PhyloTree) (E : Finset Pair)
    (hE : E ⊆ EdgeAbove.candidates t) (p : Address) :
    (ghostEndpoints t E p).Nodup := by
  classical
  apply List.nodup_flatMap.mpr
  constructor
  · intro e he
    split_ifs <;> simp
  · apply (Finset.nodup_toList E).imp_of_mem
    intro e f he hf hne
    change List.Disjoint _ _
    rw [List.disjoint_left]
    intro v hv hw
    dsimp at hv hw
    split_ifs at hv hw <;> simp_all only [List.not_mem_nil, List.mem_singleton]
    exact hne (donor_injective t (hE (Finset.mem_toList.mp he))
      (hE (Finset.mem_toList.mp hf)) hw)

/-- For a family of admissible pairs, no vertex is both an outer endpoint and a ghost donor
on the same wire. -/
theorem outer_ghost_disjoint (t : PhyloTree) (E : Finset Pair)
    (hE : E ⊆ EdgeAbove.candidates t) (p : Address) :
    List.Disjoint (outerEndpoints t E p) (ghostEndpoints t E p) := by
  classical
  rw [List.disjoint_left]
  intro v hv hw
  obtain ⟨e, he, hout⟩ := mem_outerEndpoints.mp hv
  obtain ⟨f, hf, hfu, hft, hd⟩ := mem_ghostEndpoints.mp hw
  rcases hout with ⟨heu, het, hd'⟩ | ⟨hew, hr⟩
  · have hef := donor_injective t (hE he) (hE hf) (hd'.symm.trans hd)
    subst f
    exact het hft
  · exact donor_ne_recipient t f e (hd.symm.trans hr)

/-- A wire has at least two vertices. -/
theorem wire_length (t : PhyloTree) (E : Finset Pair) (p : Address) :
    2 ≤ (wire t E p).length := by
  simp only [wire, List.length_append, List.length_singleton]
  omega

/-- The wire above `p` starts at `parent(p)`. -/
theorem wire_head (t : PhyloTree) (E : Finset Pair) (p : Address) :
    (wire t E p).head? = some (Address.code (parent p)) := by
  simp [wire, List.append_assoc]

/-- The wire above `p` ends at `p`. -/
theorem wire_last (t : PhyloTree) (E : Finset Pair) (p : Address) :
    (wire t E p).getLast? = some (Address.code p) := by
  simp only [wire, List.getLast?_append]
  rfl

private theorem endpoints_ne_code (t : PhyloTree) (E : Finset Pair) (p : Address)
    {q : Address} (hq : q ∈ t.nodes) {v : ℕ}
    (hv : v ∈ outerEndpoints t E p ++ ghostEndpoints t E p) : v ≠ Address.code q := by
  have h : v ∈ wireInterior (wire t E p) := by simpa [wireInterior_eq] using hv
  exact fun hc => Finset.disjoint_left.mp (wireInterior_disjoint_original t E p) h
    (Finset.mem_image.mpr ⟨q, hq, hc.symm⟩)

/-- For a family of admissible pairs and a non-root vertex `p` of `T`, the wire above `p` has
no repeated vertex. -/
theorem wire_nodup (t : PhyloTree) (E : Finset Pair)
    (hE : E ⊆ EdgeAbove.candidates t) {p : Address} (hp : p ∈ t.nodes) (hne : p ≠ []) :
    (wire t E p).Nodup := by
  classical
  have hparent : parent p ∈ t.nodes := t.nodes_prefix_closed hp (parent_prefix p)
  have hlen : (parent p).length < p.length := by
    have hpos : 0 < p.length := List.length_pos_iff.mpr hne
    simp only [parent, List.length_take]
    omega
  have hdiff : Address.code (parent p) ≠ Address.code p := by
    intro h
    have := congrArg List.length (Address.code_injective h)
    omega
  have hinner : (outerEndpoints t E p ++ ghostEndpoints t E p).Nodup :=
    (outerEndpoints_nodup t E hE p).append (ghostEndpoints_nodup t E hE p)
      (outer_ghost_disjoint t E hE p)
  have hlast : (outerEndpoints t E p ++ ghostEndpoints t E p ++ [Address.code p]).Nodup :=
    hinner.append (by simp) (by
      rw [List.disjoint_left]
      intro v hv hvlast
      exact endpoints_ne_code t E p hp hv (List.mem_singleton.mp hvlast))
  change (Address.code (parent p) ::
    (outerEndpoints t E p ++ ghostEndpoints t E p ++ [Address.code p])).Nodup
  refine List.nodup_cons.mpr ⟨?_, hlast⟩
  intro hmem
  rcases List.mem_append.mp hmem with hinner | hlast
  · exact endpoints_ne_code t E p hparent hinner rfl
  · exact hdiff (List.mem_singleton.mp hlast)

/-- For a family of admissible pairs, the vertices of `Realization.graph t E` are the vertices
of `T` and the vertices inside the wires above the non-root vertices of `T`. -/
theorem vertices_covered (t : PhyloTree) (E : Finset Pair)
    (hE : E ⊆ EdgeAbove.candidates t) :
    (graph t E).vertices = t.nodes.image Address.code ∪
      (t.nodes.erase []).biUnion (fun p => wireInterior (wire t E p)) := by
  classical
  change t.nodes.image Address.code ∪ E.biUnion (fun e => {donor t e, recipient t e}) = _
  apply congrArg (fun F => t.nodes.image Address.code ∪ F)
  ext v
  simp only [Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton,
    Finset.mem_erase, mem_wireInterior]
  constructor
  · rintro ⟨e, he, hd | hr⟩
    · have ha := (Finset.mem_filter.mp (hE he)).2
      exact ⟨e.1, ⟨ha.2.2.1, ha.1⟩, e, he, Or.inl ⟨rfl, hd⟩⟩
    · have ha := (Finset.mem_filter.mp (hE he)).2
      exact ⟨e.2, ⟨ha.2.2.2.1, ha.2.1⟩, e, he, Or.inr ⟨rfl, hr⟩⟩
  · rintro ⟨p, _, e, he, hdonor | hrecipient⟩
    · exact ⟨e, he, Or.inl hdonor.2⟩
    · exact ⟨e, he, Or.inr hrecipient.2⟩

end Camus.Realization
