module

public import Camus.Network.RootAbove.Defs
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-!
# Adding an outgroup

Let `N` be a rooted binary level-1 network. Adding an outgroup gives the network `N⁺`
(`RootedNetwork.withOutgroup`): a new root `ρ` whose two children are the root of `N` and a new
leaf `ℓ`, labelled by a new taxon `z`. The new vertices lie on no cycle, so `N⁺` is again a rooted
binary level-1 network (`RootedNetwork.withOutgroup_levelOne`), with the reticulations of `N`.

## Main results

* `RootedNetwork.withOutgroup_levelOne`: `N⁺` is a rooted binary level-1 network.
* `RootedNetwork.withOutgroup_reticulationCount`: `N⁺` has as many reticulations as `N`.
* `RootedNetwork.withOutgroup_indegree`, `RootedNetwork.withOutgroup_outdegree`: the degrees of
  `N⁺`.
-/

@[expose] public section

namespace Camus

namespace RootedNetwork

/-- The network `N` with an outgroup: a new root `ρ` whose children are the root of `N` and a new
leaf `ℓ` labelled by the new taxon `z`. -/
def withOutgroup (N : RootedNetwork) (z ρ ℓ : ℕ) : RootedNetwork where
  vertices := insert ρ (insert ℓ N.vertices)
  edges := insert (ρ, N.root) (insert (ρ, ℓ) N.edges)
  root := ρ
  taxa := insert z N.taxa
  leaf := fun a => if a = z then ℓ else N.leaf a

variable {N : RootedNetwork} {z ρ ℓ : ℕ}

/-- Counting the elements of `insert a s` with a property. -/
theorem card_filter_insert_of_notMem {α : Type*} [DecidableEq α] {s : Finset α} {a : α}
    (ha : a ∉ s) (p : α → Prop) [DecidablePred p] :
    ((insert a s).filter p).card = (s.filter p).card + if p a then 1 else 0 := by
  rw [Finset.filter_insert]
  split_ifs with h
  · exact Finset.card_insert_of_notMem (fun hm => ha (Finset.mem_filter.mp hm).1)
  · simp

/-- The edges of `N⁺`: the two edges out of the new root, and the edges of `N`. -/
theorem withOutgroup_mem_edges {x y : ℕ} :
    (x, y) ∈ (N.withOutgroup z ρ ℓ).edges ↔
      (x = ρ ∧ y = N.root) ∨ (x = ρ ∧ y = ℓ) ∨ (x, y) ∈ N.edges := by
  simp [withOutgroup]

/-- The vertices of `N⁺`: the new root, the new leaf, and the vertices of `N`. -/
theorem withOutgroup_mem_vertices {v : ℕ} :
    v ∈ (N.withOutgroup z ρ ℓ).vertices ↔ v = ρ ∨ v = ℓ ∨ v ∈ N.vertices := by
  simp [withOutgroup]

/-- The two new edges are not edges of `N`. -/
theorem withOutgroup_new_notMem (hN : N.RootedBinaryLevelOne) (hρ : ρ ∉ N.vertices)
    (hℓ : ℓ ∉ N.vertices) {X : Finset (ℕ × ℕ)} (hX : X ⊆ N.edges) :
    (ρ, N.root) ∉ insert (ρ, ℓ) X ∧ (ρ, ℓ) ∉ X := by
  have hρE : ∀ y, (ρ, y) ∉ N.edges := fun y h => hρ (hN.2.1 _ h).1
  refine ⟨?_, fun h => hρE ℓ (hX h)⟩
  intro h
  rcases Finset.mem_insert.mp h with h | h
  · simp only [Prod.mk.injEq] at h
    exact hℓ (h.2 ▸ hN.1)
  · exact hρE _ (hX h)

/-- The edges into `v` of a subset `X` of the edges of `N`, with the two new edges added. -/
theorem withOutgroup_filter_in (hN : N.RootedBinaryLevelOne) (hρ : ρ ∉ N.vertices)
    (hℓ : ℓ ∉ N.vertices) {X : Finset (ℕ × ℕ)} (hX : X ⊆ N.edges) (v : ℕ) :
    ((insert (ρ, N.root) (insert (ρ, ℓ) X)).filter (fun e => e.2 = v)).card =
      (X.filter (fun e => e.2 = v)).card + (if ℓ = v then 1 else 0) +
        (if N.root = v then 1 else 0) := by
  obtain ⟨h1, h2⟩ := withOutgroup_new_notMem hN hρ hℓ hX
  rw [card_filter_insert_of_notMem h1, card_filter_insert_of_notMem h2]

/-- The edges out of `v` of a subset `X` of the edges of `N`, with the two new edges added. -/
theorem withOutgroup_filter_out (hN : N.RootedBinaryLevelOne) (hρ : ρ ∉ N.vertices)
    (hℓ : ℓ ∉ N.vertices) {X : Finset (ℕ × ℕ)} (hX : X ⊆ N.edges) (v : ℕ) :
    ((insert (ρ, N.root) (insert (ρ, ℓ) X)).filter (fun e => e.1 = v)).card =
      (X.filter (fun e => e.1 = v)).card + (if ρ = v then 1 else 0) +
        (if ρ = v then 1 else 0) := by
  obtain ⟨h1, h2⟩ := withOutgroup_new_notMem hN hρ hℓ hX
  rw [card_filter_insert_of_notMem h1, card_filter_insert_of_notMem h2]

/-- The indegrees of `N⁺`: those of `N`, plus one at the root of `N` and at the new leaf. -/
theorem withOutgroup_indegree (hN : N.RootedBinaryLevelOne) (hρ : ρ ∉ N.vertices)
    (hℓ : ℓ ∉ N.vertices) (v : ℕ) :
    (N.withOutgroup z ρ ℓ).indegree v =
      N.indegree v + (if ℓ = v then 1 else 0) + (if N.root = v then 1 else 0) :=
  withOutgroup_filter_in hN hρ hℓ (Finset.Subset.refl _) v

/-- The outdegrees of `N⁺`: those of `N`, plus two at the new root. -/
theorem withOutgroup_outdegree (hN : N.RootedBinaryLevelOne) (hρ : ρ ∉ N.vertices)
    (hℓ : ℓ ∉ N.vertices) (v : ℕ) :
    (N.withOutgroup z ρ ℓ).outdegree v =
      N.outdegree v + (if ρ = v then 1 else 0) + (if ρ = v then 1 else 0) :=
  withOutgroup_filter_out hN hρ hℓ (Finset.Subset.refl _) v

/-- A vertex outside `N` has no edge of `N` into it. -/
theorem indegree_eq_zero_of_notMem (hN : N.RootedBinaryLevelOne) {v : ℕ}
    (hv : v ∉ N.vertices) : N.indegree v = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨heN, hev⟩ := Finset.mem_filter.mp he
  exact hv (hev ▸ (hN.2.1 e heN).2)

/-- A vertex outside `N` has no edge of `N` out of it. -/
theorem outdegree_eq_zero_of_notMem (hN : N.RootedBinaryLevelOne) {v : ℕ}
    (hv : v ∉ N.vertices) : N.outdegree v = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨heN, hev⟩ := Finset.mem_filter.mp he
  exact hv (hev ▸ (hN.2.1 e heN).1)

/-- In `N⁺`, the new leaf is adjacent only to the new root. -/
theorem withOutgroup_adj_leaf (hN : N.RootedBinaryLevelOne) (hρ : ρ ∉ N.vertices)
    (hℓ : ℓ ∉ N.vertices) (hρℓ : ρ ≠ ℓ) (x : ℕ) :
    (N.withOutgroup z ρ ℓ).underlying.Adj ℓ x ↔ x = ρ := by
  have hrootℓ : N.root ≠ ℓ := fun h => hℓ (h ▸ hN.1)
  constructor
  · rintro ⟨_, h | h⟩
    · rcases withOutgroup_mem_edges.mp h with h | h | h
      · exact absurd h.1 hρℓ.symm
      · exact absurd h.1 hρℓ.symm
      · exact absurd (hN.2.1 _ h).1 hℓ
    · rcases withOutgroup_mem_edges.mp h with h | h | h
      · exact absurd h.2.symm hrootℓ
      · exact h.1
      · exact absurd (hN.2.1 _ h).2 hℓ
  · rintro rfl
    exact ⟨hρℓ.symm, Or.inr (withOutgroup_mem_edges.mpr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩

/-- In `N⁺`, the new root is adjacent only to the root of `N` and the new leaf. -/
theorem withOutgroup_adj_root (hN : N.RootedBinaryLevelOne) (hρ : ρ ∉ N.vertices) (x : ℕ) :
    (N.withOutgroup z ρ ℓ).underlying.Adj ρ x → x = N.root ∨ x = ℓ := by
  rintro ⟨_, h | h⟩
  · rcases withOutgroup_mem_edges.mp h with h | h | h
    · exact Or.inl h.2
    · exact Or.inr h.2
    · exact absurd (hN.2.1 _ h).1 hρ
  · rcases withOutgroup_mem_edges.mp h with h | h | h
    · exact absurd (h.2 ▸ hN.1) hρ
    · exact absurd h.2 (fun h' => hρ (by simp_all))
    · exact absurd (hN.2.1 _ h).2 hρ

/-- A cycle of `N⁺` avoids the new root and the new leaf: in a cycle every vertex has two
neighbours on the cycle, the new leaf has one neighbour, and the new root has the new leaf as one
of its two neighbours. -/
theorem withOutgroup_cycle_avoids (hN : N.RootedBinaryLevelOne) (hρ : ρ ∉ N.vertices)
    (hℓ : ℓ ∉ N.vertices) (hρℓ : ρ ≠ ℓ) {u : ℕ}
    (c : (N.withOutgroup z ρ ℓ).underlying.Walk u u) (hc : c.IsCycle) :
    ρ ∉ c.support ∧ ℓ ∉ c.support := by
  have hleaf : ℓ ∉ c.support := by
    intro hm
    have h2 := hc.ncard_neighborSet_toSubgraph_eq_two hm
    have hsub : c.toSubgraph.neighborSet ℓ ⊆ {ρ} := by
      intro x hx
      have hadj := c.toSubgraph.neighborSet_subset ℓ hx
      rw [SimpleGraph.mem_neighborSet] at hadj
      exact (withOutgroup_adj_leaf hN hρ hℓ hρℓ x).mp hadj
    have hle := Set.ncard_le_ncard hsub (Set.finite_singleton ρ)
    rw [Set.ncard_singleton] at hle
    omega
  refine ⟨?_, hleaf⟩
  intro hm
  have h2 := hc.ncard_neighborSet_toSubgraph_eq_two hm
  by_cases hnb : ℓ ∈ c.toSubgraph.neighborSet ρ
  · exact hleaf ((c.mem_verts_toSubgraph).mp (SimpleGraph.Subgraph.Adj.snd_mem hnb))
  · have hsub : c.toSubgraph.neighborSet ρ ⊆ {N.root} := by
      intro x hx
      have hadj := c.toSubgraph.neighborSet_subset ρ hx
      rw [SimpleGraph.mem_neighborSet] at hadj
      rcases withOutgroup_adj_root hN hρ x hadj with h | h
      · exact h
      · exact absurd (h ▸ hx) hnb
    have hle := Set.ncard_le_ncard hsub (Set.finite_singleton N.root)
    rw [Set.ncard_singleton] at hle
    omega

/-- The edges of a cycle of `N⁺` are edges of the undirected graph of `N`. -/
theorem withOutgroup_cycle_edges (hN : N.RootedBinaryLevelOne) (hρ : ρ ∉ N.vertices)
    (hℓ : ℓ ∉ N.vertices) (hρℓ : ρ ≠ ℓ) {u : ℕ}
    (c : (N.withOutgroup z ρ ℓ).underlying.Walk u u) (hc : c.IsCycle) :
    ∀ e ∈ c.edges, e ∈ N.underlying.edgeSet := by
  obtain ⟨hρc, hℓc⟩ := withOutgroup_cycle_avoids hN hρ hℓ hρℓ c hc
  intro e he
  induction e using Sym2.ind with
  | _ x y =>
    have hx := c.fst_mem_support_of_mem_edges he
    have hy := c.snd_mem_support_of_mem_edges he
    have hxρ : x ≠ ρ := fun h => hρc (h ▸ hx)
    have hyρ : y ≠ ρ := fun h => hρc (h ▸ hy)
    obtain ⟨hxy, h⟩ := c.adj_of_mem_edges he
    refine ⟨hxy, h.imp (fun h => ?_) (fun h => ?_)⟩
    · rcases withOutgroup_mem_edges.mp h with h | h | h
      · exact absurd h.1 hxρ
      · exact absurd h.1 hxρ
      · exact h
    · rcases withOutgroup_mem_edges.mp h with h | h | h
      · exact absurd h.1 hyρ
      · exact absurd h.1 hyρ
      · exact h

/-- Adding an outgroup to a rooted binary level-1 network `N` gives a rooted binary level-1
network `N⁺`, when the new root `ρ` and the new leaf `ℓ` are distinct vertices outside `N` and the
new taxon `z` is not a taxon of `N`. The cycles of `N⁺` are those of `N`. -/
theorem withOutgroup_levelOne (hN : N.RootedBinaryLevelOne) (hρ : ρ ∉ N.vertices)
    (hℓ : ℓ ∉ N.vertices) (hρℓ : ρ ≠ ℓ) (hz : z ∉ N.taxa) :
    (N.withOutgroup z ρ ℓ).RootedBinaryLevelOne := by
  classical
  have hroot : N.root ∈ N.vertices := hN.1
  have hrootρ : N.root ≠ ρ := fun h => hρ (h ▸ hroot)
  have hrootℓ : N.root ≠ ℓ := fun h => hℓ (h ▸ hroot)
  have hin := withOutgroup_indegree (z := z) hN hρ hℓ
  have hout := withOutgroup_outdegree (z := z) hN hρ hℓ
  have hleafN : ∀ a ∈ N.taxa, N.leaf a ∈ N.vertices := fun a ha =>
    (hN.2.2.2.2.2.2.2.1 a ha).1
  have hvert : ∀ v, v ∈ (N.withOutgroup z ρ ℓ).vertices ↔
      v = ρ ∨ v = ℓ ∨ v ∈ N.vertices := fun v => withOutgroup_mem_vertices
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- the root is a vertex
  · exact (hvert ρ).mpr (Or.inl rfl)
  -- the edges join vertices
  · rintro ⟨x, y⟩ he
    rcases withOutgroup_mem_edges.mp he with h | h | h
    · exact ⟨(hvert x).mpr (Or.inl h.1), (hvert y).mpr (Or.inr (Or.inr (h.2 ▸ hroot)))⟩
    · exact ⟨(hvert x).mpr (Or.inl h.1), (hvert y).mpr (Or.inr (Or.inl h.2))⟩
    · exact ⟨(hvert x).mpr (Or.inr (Or.inr (hN.2.1 _ h).1)),
        (hvert y).mpr (Or.inr (Or.inr (hN.2.1 _ h).2))⟩
  -- no directed cycle: a rank that grows along the edges
  · let r : ℕ → ℕ := fun v => if v = ρ then 0 else N.dagRank v + 1
    have hrank : ∀ x y, (x, y) ∈ (N.withOutgroup z ρ ℓ).edges → r x < r y := by
      intro x y he
      rcases withOutgroup_mem_edges.mp he with h | h | h
      · simp only [r, h.1, h.2, ite_eq_left, ite_eq_right hrootρ]
        omega
      · simp only [r, h.1, h.2, ite_eq_left, ite_eq_right hρℓ.symm]
        omega
      · have hx : x ≠ ρ := fun hx => hρ (hx ▸ (hN.2.1 _ h).1)
        have hy : y ≠ ρ := fun hy => hρ (hy ▸ (hN.2.1 _ h).2)
        simp only [r, ite_eq_right hx, ite_eq_right hy]
        exact Nat.succ_lt_succ (dagRank_lt hN h)
    intro v hv
    have hlt : ∀ a b, Relation.TransGen (fun u w => (u, w) ∈ (N.withOutgroup z ρ ℓ).edges) a b →
        r a < r b := by
      intro a b h
      induction h with
      | single h => exact hrank _ _ h
      | tail _ h ih => exact ih.trans (hrank _ _ h)
    exact lt_irrefl _ (hlt v v hv)
  -- the new root has indegree 0
  · change (N.withOutgroup z ρ ℓ).indegree ρ = 0
    rw [hin, indegree_eq_zero_of_notMem hN hρ, ite_eq_right hρℓ.symm, ite_eq_right hrootρ]
  -- the new root has outdegree 2
  · right
    change (N.withOutgroup z ρ ℓ).outdegree ρ = 2
    rw [hout, outdegree_eq_zero_of_notMem hN hρ, ite_eq_left rfl]
  -- every vertex is reachable from the new root
  · intro v hv
    rcases (hvert v).mp hv with h | h | h
    · subst h
      exact Relation.ReflTransGen.refl
    · subst h
      exact Relation.ReflTransGen.single
        (withOutgroup_mem_edges.mpr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
    · have hN' := Relation.ReflTransGen.mono (fun a b hab =>
        (withOutgroup_mem_edges (z := z) (ρ := ρ) (ℓ := ℓ)).mpr (Or.inr (Or.inr hab)))
        N.root v (hN.2.2.2.2.2.1 v h)
      exact Relation.ReflTransGen.head
        (withOutgroup_mem_edges.mpr (Or.inl ⟨rfl, rfl⟩)) hN'
  -- distinct taxa label distinct leaves
  · intro a ha b hb hab
    have ha' : a = z ∨ a ∈ N.taxa := by simpa [withOutgroup] using ha
    have hb' : b = z ∨ b ∈ N.taxa := by simpa [withOutgroup] using hb
    change (if a = z then ℓ else N.leaf a) = (if b = z then ℓ else N.leaf b) at hab
    by_cases haz : a = z <;> by_cases hbz : b = z
    · rw [haz, hbz]
    · rw [ite_eq_left haz, ite_eq_right hbz] at hab
      exact absurd (hab ▸ hleafN b (hb'.resolve_left hbz)) hℓ
    · rw [ite_eq_right haz, ite_eq_left hbz] at hab
      exact absurd (hab ▸ hleafN a (ha'.resolve_left haz)) hℓ
    · rw [ite_eq_right haz, ite_eq_right hbz] at hab
      exact hN.2.2.2.2.2.2.1 (ha'.resolve_left haz) (hb'.resolve_left hbz) hab
  -- the leaves have indegree 1 and outdegree 0
  · intro a ha
    have ha' : a = z ∨ a ∈ N.taxa := by simpa [withOutgroup] using ha
    change (if a = z then ℓ else N.leaf a) ∈ _ ∧
      (N.withOutgroup z ρ ℓ).indegree (if a = z then ℓ else N.leaf a) =
        (if (if a = z then ℓ else N.leaf a) = ρ then 0 else 1) ∧
      (N.withOutgroup z ρ ℓ).outdegree (if a = z then ℓ else N.leaf a) = 0
    by_cases haz : a = z
    · simp only [ite_eq_left haz]
      refine ⟨(hvert ℓ).mpr (Or.inr (Or.inl rfl)), ?_, ?_⟩
      · rw [hin, indegree_eq_zero_of_notMem hN hℓ, ite_eq_left rfl, ite_eq_right hrootℓ,
          ite_eq_right hρℓ.symm]
      · rw [hout, outdegree_eq_zero_of_notMem hN hℓ, ite_eq_right hρℓ]
    · have haN := ha'.resolve_left haz
      have hlv := hleafN a haN
      have hlρ : N.leaf a ≠ ρ := fun h => hρ (h ▸ hlv)
      have hlℓ : ℓ ≠ N.leaf a := fun h => hℓ (h ▸ hlv)
      obtain ⟨_, hinN, houtN⟩ := hN.2.2.2.2.2.2.2.1 a haN
      simp only [ite_eq_right haz, ite_eq_right hlρ]
      refine ⟨(hvert _).mpr (Or.inr (Or.inr hlv)), ?_, ?_⟩
      · rw [hin, hinN, ite_eq_right hlℓ]
        by_cases hr : N.leaf a = N.root
        · rw [ite_eq_left hr, ite_eq_left hr.symm]
        · rw [ite_eq_right hr, ite_eq_right (Ne.symm hr)]
      · rw [hout, houtN, ite_eq_right (Ne.symm hlρ)]
  -- the vertices of outdegree 0 are the leaves
  · intro v hv
    change (N.withOutgroup z ρ ℓ).outdegree v = 0 ↔
      ∃ a ∈ insert z N.taxa, (if a = z then ℓ else N.leaf a) = v
    rcases (hvert v).mp hv with h | h | h
    · subst v
      rw [hout, outdegree_eq_zero_of_notMem hN hρ, ite_eq_left rfl]
      constructor
      · omega
      · rintro ⟨a, ha, hav⟩
        by_cases haz : a = z
        · rw [ite_eq_left haz] at hav
          exact absurd hav.symm hρℓ
        · rw [ite_eq_right haz] at hav
          have haN : a ∈ N.taxa := by simpa [haz] using ha
          exact absurd (hav ▸ hleafN a haN) hρ
    · subst v
      rw [hout, outdegree_eq_zero_of_notMem hN hℓ, ite_eq_right hρℓ]
      exact ⟨fun _ => ⟨z, Finset.mem_insert_self _ _, ite_eq_left rfl⟩, fun _ => rfl⟩
    · have hvρ : ρ ≠ v := fun h' => hρ (h' ▸ h)
      have hvℓ : v ≠ ℓ := fun h' => hℓ (h' ▸ h)
      rw [hout, ite_eq_right hvρ]
      simp only [Nat.add_zero]
      rw [hN.2.2.2.2.2.2.2.2.1 v h]
      constructor
      · rintro ⟨a, ha, hav⟩
        refine ⟨a, Finset.mem_insert_of_mem ha, ?_⟩
        have haz : a ≠ z := fun h' => hz (h' ▸ ha)
        rw [ite_eq_right haz]
        exact hav
      · rintro ⟨a, ha, hav⟩
        by_cases haz : a = z
        · rw [ite_eq_left haz] at hav
          exact absurd hav.symm hvℓ
        · rw [ite_eq_right haz] at hav
          exact ⟨a, by simpa [haz] using ha, hav⟩
  -- the other vertices are leaves, tree vertices or reticulations
  · intro v hv hvρ
    rcases (hvert v).mp hv with h | h | h
    · exact absurd h hvρ
    · subst v
      left
      rw [hin, hout, indegree_eq_zero_of_notMem hN hℓ, outdegree_eq_zero_of_notMem hN hℓ,
        ite_eq_left rfl, ite_eq_right hrootℓ, ite_eq_right hρℓ]
      exact ⟨rfl, rfl⟩
    · have hvℓ : ℓ ≠ v := fun h' => hℓ (h' ▸ h)
      have hρv : ρ ≠ v := Ne.symm hvρ
      rw [hin, hout, ite_eq_right hvℓ, ite_eq_right hρv]
      simp only [Nat.add_zero]
      by_cases hr : v = N.root
      · subst v
        rw [ite_eq_left rfl, hN.2.2.2.1]
        rcases hN.2.2.2.2.1 with h0 | h2
        · exact Or.inl ⟨rfl, h0⟩
        · exact Or.inr (Or.inl ⟨rfl, h2⟩)
      · rw [ite_eq_right (Ne.symm hr)]
        simpa using hN.2.2.2.2.2.2.2.2.2.1 v h hr
  -- level-1: the cycles of `N⁺` are cycles of `N`
  · intro v w c d hc hd hcd
    have hce := withOutgroup_cycle_edges hN hρ hℓ hρℓ c hc
    have hde := withOutgroup_cycle_edges hN hρ hℓ hρℓ d hd
    have h := hN.2.2.2.2.2.2.2.2.2.2 v w (c.transfer N.underlying hce)
      (d.transfer N.underlying hde) ((SimpleGraph.Walk.isCycle_transfer hce).mpr hc)
      ((SimpleGraph.Walk.isCycle_transfer hde).mpr hd)
      (by rwa [SimpleGraph.Walk.edges_transfer, SimpleGraph.Walk.edges_transfer])
    rwa [SimpleGraph.Walk.support_transfer, SimpleGraph.Walk.support_transfer] at h

/-- `N⁺` has as many reticulations as `N`: the new root has indegree 0, the new leaf and the root
of `N` have indegree 1, and the other indegrees are those of `N`. -/
theorem withOutgroup_reticulationCount (hN : N.RootedBinaryLevelOne) (hρ : ρ ∉ N.vertices)
    (hℓ : ℓ ∉ N.vertices) (hρℓ : ρ ≠ ℓ) :
    (N.withOutgroup z ρ ℓ).reticulationCount = N.reticulationCount := by
  classical
  have hrootℓ : N.root ≠ ℓ := fun h => hℓ (h ▸ hN.1)
  have hrootρ : N.root ≠ ρ := fun h => hρ (h ▸ hN.1)
  unfold reticulationCount
  have hin := withOutgroup_indegree (z := z) hN hρ hℓ
  have hfilter : (N.withOutgroup z ρ ℓ).vertices.filter
      (fun v => (N.withOutgroup z ρ ℓ).indegree v = 2) =
      N.vertices.filter (fun v => N.indegree v = 2) := by
    ext v
    rw [Finset.mem_filter, Finset.mem_filter, withOutgroup_mem_vertices, hin]
    constructor
    · rintro ⟨h | h | h, hd⟩
      · subst v
        rw [indegree_eq_zero_of_notMem hN hρ, ite_eq_right hρℓ.symm, ite_eq_right hrootρ] at hd
        omega
      · subst v
        rw [indegree_eq_zero_of_notMem hN hℓ, ite_eq_left rfl, ite_eq_right hrootℓ] at hd
        omega
      · have hvℓ : ℓ ≠ v := fun h' => hℓ (h' ▸ h)
        rw [ite_eq_right hvℓ] at hd
        by_cases hr : N.root = v
        · subst v
          rw [ite_eq_left rfl, hN.2.2.2.1] at hd
          omega
        · rw [ite_eq_right hr] at hd
          exact ⟨h, by omega⟩
    · rintro ⟨h, hd⟩
      have hvℓ : ℓ ≠ v := fun h' => hℓ (h' ▸ h)
      have hr : N.root ≠ v := by
        intro h'
        subst v
        rw [hN.2.2.2.1] at hd
        omega
      exact ⟨Or.inr (Or.inr h), by rw [ite_eq_right hvℓ, ite_eq_right hr]; omega⟩
  rw [hfilter]

end RootedNetwork

end Camus
