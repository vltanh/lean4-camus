module

public import Camus.Network.Completeness.Wires

/-!
# Colouring a wire

Auxiliary to `GraphSubdivision.displays_iff` (subdividing edges does not change the displayed
quartets). A wire is the directed path that replaces an edge of `P` in a subdivision `N`: a
duplicate-free list `L` of vertices, whose arcs `wireEdges L` are its consecutive pairs. Given a set
`B` of arcs, this file colours the vertices of one wire, with prescribed colours at its two ends, so
that every arc of the wire in `B` joins two vertices of the same colour. The end colours may differ
only if some arc of the wire is missing from `B`. `GraphSubdivision.exists_subdivision_coloring`
glues these colourings over all wires.

## Main results

* `wire_edge_idxOf`: each arc of a wire goes one step forward along the list.
* `exists_wire_coloring`: the colouring of one wire.
-/

@[expose] public section

namespace Camus

/-- Each arc `(x, y)` of a duplicate-free wire `L` goes one step forward: the position of `y` in `L`
is the position of `x` plus one. -/
theorem wire_edge_idxOf {L : List ℕ} (hL : L.Nodup) {e : ℕ × ℕ}
    (he : e ∈ wireEdges L) : L.idxOf e.2 = L.idxOf e.1 + 1 := by
  induction L with
  | nil => simp [wireEdges] at he
  | cons a L ih =>
    cases L with
    | nil => simp [wireEdges] at he
    | cons b L =>
      have hcons : wireEdges (a :: b :: L) = insert (a,b) (wireEdges (b :: L)) := by simp [wireEdges]
      rw [hcons] at he
      rcases Finset.mem_insert.mp he with rfl | he
      · have hab : b ≠ a := by
          intro h
          exact (List.nodup_cons.mp hL).1 (by simp [h])
        simp [List.idxOf_cons_ne, Ne.symm hab]
      · have htail := (List.nodup_cons.mp hL).2
        have ha := (List.nodup_cons.mp hL).1
        have hfirst : e.1 ≠ a := by
          intro h
          exact ha (h ▸ List.mem_of_mem_dropLast (wire_edge_source_mem he))
        have hsecond : e.2 ≠ a := by
          intro h
          exact ha (h ▸ List.mem_of_mem_tail (wire_edge_target_mem he))
        simp only [List.idxOf_cons_ne _ (Ne.symm hfirst), List.idxOf_cons_ne _ (Ne.symm hsecond)]
        rw [ih htail he]

/-- No arc of the wire in `B` crosses an arc `gap` of the wire missing from `B`: both ends of the
arc lie at or before the source of `gap`, or both lie after it. -/
theorem wire_gap_color {L : List ℕ} (hL : L.Nodup) {B : Finset (ℕ × ℕ)}
    {gap : ℕ × ℕ} (hgap : gap ∈ wireEdges L) (hmissing : gap ∉ B)
    {e : ℕ × ℕ} (he : e ∈ wireEdges L) (heB : e ∈ B) :
    (L.idxOf e.1 ≤ L.idxOf gap.1 ↔ L.idxOf e.2 ≤ L.idxOf gap.1) := by
  have heidx := wire_edge_idxOf hL he
  have hgapidx := wire_edge_idxOf hL hgap
  constructor
  · intro h
    by_contra hn
    have hi : L.idxOf e.1 = L.idxOf gap.1 := by omega
    have hj : L.idxOf e.2 = L.idxOf gap.2 := by omega
    have hf := (List.idxOf_inj (List.mem_of_mem_dropLast (wire_edge_source_mem he))).mp hi
    have hs := (List.idxOf_inj (List.mem_of_mem_tail (wire_edge_target_mem he))).mp hj
    have heq : e = gap := Prod.ext hf hs
    exact hmissing (heq ▸ heB)
  · intro h
    omega

/-- Colouring one wire. Let `L` be a duplicate-free wire from `a` to `b`, `B` a set of arcs, and
`ca`, `cb` two colours with `ca = cb` whenever the whole wire lies in `B`. Then some colouring gives
`a` the colour `ca`, `b` the colour `cb`, and both ends of every arc of the wire in `B` the same
colour. If `ca ≠ cb`, some arc of the wire is missing from `B`; colour the vertices up to its source
with `ca` and the others with `cb`. -/
theorem exists_wire_coloring {β : Type*} (L : List ℕ) (hL : L.Nodup)
    {a b : ℕ} (hhead : L.head? = some a) (hlast : L.getLast? = some b)
    (B : Finset (ℕ × ℕ)) (ca cb : β) (hfull : wireEdges L ⊆ B → ca = cb) :
    ∃ color : ℕ → β, color a = ca ∧ color b = cb ∧
      ∀ e ∈ wireEdges L, e ∈ B → color e.1 = color e.2 := by
  classical
  by_cases hsame : ca = cb
  · exact ⟨fun _ => ca, rfl, hsame, fun _ _ _ => rfl⟩
  · have hnot : ¬wireEdges L ⊆ B := fun h => hsame (hfull h)
    obtain ⟨gap, hgap, hmissing⟩ := Finset.not_subset.mp hnot
    let color := fun v => if L.idxOf v ≤ L.idxOf gap.1 then ca else cb
    have hne : L ≠ [] := by intro h; simp [h] at hhead
    have ha : L.idxOf a = 0 := by
      rw [List.idxOf_eq_zero_iff_head_eq hne]
      exact Option.some.inj ((List.head?_eq_some_head hne).symm.trans hhead)
    have hb : L.idxOf b = L.length - 1 := by
      have hlast' : L.getLast hne = b :=
        Option.some.inj ((List.getLast?_eq_some_getLast hne).symm.trans hlast)
      rw [← hlast']
      apply List.idxOf_getLast hne
      have hn : (L.dropLast ++ [L.getLast hne]).Nodup := by
        rw [List.dropLast_append_getLast hne]
        exact hL
      intro hmem
      exact (List.nodup_append.mp hn).2.2 _ hmem _ (by simp) rfl
    have hidx := wire_edge_idxOf hL hgap
    have hbound := List.idxOf_lt_length_of_mem (List.mem_of_mem_tail (wire_edge_target_mem hgap))
    refine ⟨color, ?_, ?_, ?_⟩
    · simp [color, ha]
    · simp only [color, hb]
      rw [ite_eq_right (by omega)]
    · intro e he heB
      simp only [color]
      have hiff := wire_gap_color hL hgap hmissing he heB
      by_cases h : L.idxOf e.1 ≤ L.idxOf gap.1
      · simp only [ite_eq_left h, ite_eq_left (hiff.mp h)]
      · simp only [ite_eq_right h, ite_eq_right (fun h' => h (hiff.mpr h'))]

end Camus
