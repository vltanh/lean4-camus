module

public import Camus.GraphCompletenessBaseline
public import Camus.GraphCompletenessFootprints

@[expose] public section

namespace Camus

/-- Data for marking a proper interior vertex of a directed wire. The two
nonempty sides retain the original endpoints. -/
structure WireSplit (l : List ℕ) (v : ℕ) where
  before : List ℕ
  after : List ℕ
  decomposition : l = before ++ v :: after
  before_nonempty : before ≠ []
  after_nonempty : after ≠ []

theorem exists_wireSplit {l : List ℕ} (hl : l.Nodup) {v : ℕ}
    (hv : v ∈ wireInterior l) : Nonempty (WireSplit l v) := by
  have hvl : v ∈ l := List.mem_of_mem_tail (List.mem_of_mem_dropLast (List.mem_toFinset.mp hv))
  obtain ⟨a,b,heq⟩ := List.mem_iff_append.mp hvl
  have ha : a ≠ [] := by
    intro ha
    subst a
    rw [List.nil_append] at heq
    rw [heq] at hl hv
    have hnot := (List.nodup_cons.mp hl).1
    exact hnot (List.mem_of_mem_dropLast (List.mem_toFinset.mp hv))
  have hb : b ≠ [] := by
    intro hb
    subst b
    have hvs : v ∈ l.dropLast := wire_interior_mem_dropLast hv
    rw [heq, List.dropLast_concat] at hvs
    have hnot : v ∉ a := by
      have hn := List.nodup_append.mp (heq ▸ hl)
      exact fun hv => hn.2.2 v hv v (by simp) rfl
    exact hnot hvs
  exact ⟨⟨a,b,heq,ha,hb⟩⟩

namespace WireSplit

def lower {l : List ℕ} {v : ℕ} (W : WireSplit l v) : List ℕ := v :: W.after
def upper {l : List ℕ} {v : ℕ} (W : WireSplit l v) : List ℕ := W.before ++ [v]

theorem edges_union (a b : List ℕ) (v : ℕ) :
    wireEdges (a ++ v :: b) = wireEdges (a ++ [v]) ∪ wireEdges (v :: b) := by
  induction a with
  | nil => simp [wireEdges]
  | cons x a ih =>
    cases a with
    | nil => simp [wireEdges]
    | cons y a =>
      simp only [List.cons_append, wireEdges, List.tail_cons, List.zip_cons_cons,
        List.toFinset_cons] at ih ⊢
      rw [ih, Finset.insert_union]

theorem edges_covered {l : List ℕ} {v : ℕ} (W : WireSplit l v) :
    wireEdges l = wireEdges W.upper ∪ wireEdges W.lower := by
  change wireEdges l = wireEdges (W.before ++ [v]) ∪ wireEdges (v :: W.after)
  exact (congrArg wireEdges W.decomposition).trans (edges_union W.before W.after v)

theorem upper_length {l : List ℕ} {v : ℕ} (W : WireSplit l v) : 2 ≤ W.upper.length := by
  have := List.length_pos_iff.mpr W.before_nonempty
  simp only [upper,List.length_append,List.length_singleton]
  omega

theorem lower_length {l : List ℕ} {v : ℕ} (W : WireSplit l v) : 2 ≤ W.lower.length := by
  have := List.length_pos_iff.mpr W.after_nonempty
  simp only [lower,List.length_cons]
  omega

theorem upper_nodup {l : List ℕ} {v : ℕ} (W : WireSplit l v) (hl : l.Nodup) : W.upper.Nodup := by
  have hnl : (W.before ++ [v] ++ W.after).Nodup := by
    simpa only [List.append_assoc,List.singleton_append] using W.decomposition ▸ hl
  exact hnl.of_append_left

theorem lower_nodup {l : List ℕ} {v : ℕ} (W : WireSplit l v) (hl : l.Nodup) : W.lower.Nodup := by
  have hnl : (W.before ++ v :: W.after).Nodup := W.decomposition ▸ hl
  exact hnl.of_append_right

theorem upper_head {l : List ℕ} {v : ℕ} (W : WireSplit l v) : W.upper.head? = l.head? := by
  obtain ⟨a,b,heq,ha,hb⟩ := W
  subst l
  cases a with
  | nil => exact False.elim (ha rfl)
  | cons x a => rfl

theorem upper_last {l : List ℕ} {v : ℕ} (W : WireSplit l v) : W.upper.getLast? = some v := by
  simp [upper]

theorem lower_head {l : List ℕ} {v : ℕ} (W : WireSplit l v) : W.lower.head? = some v := rfl

theorem lower_last {l : List ℕ} {v : ℕ} (W : WireSplit l v) : W.lower.getLast? = l.getLast? := by
  obtain ⟨a,b,heq,ha,hb⟩ := W
  subst l
  cases b with
  | nil => exact False.elim (hb rfl)
  | cons x b =>
    have hn : (x :: b).getLast? ≠ none := by simp
    cases hlast : (x :: b).getLast? with
    | none => exact False.elim (hn hlast)
    | some z => simp [lower,hlast]

theorem interior_covered {l : List ℕ} {v : ℕ} (W : WireSplit l v) :
    wireInterior l = {v} ∪ wireInterior W.upper ∪ wireInterior W.lower := by
  obtain ⟨a,b,heq,ha,hb⟩ := W
  subst l
  cases a with
  | nil => exact False.elim (ha rfl)
  | cons x a =>
    cases b with
    | nil => exact False.elim (hb rfl)
    | cons y b =>
      ext z
      simp [wireInterior,upper,lower]

end WireSplit
end Camus
