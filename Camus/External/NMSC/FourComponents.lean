module

public import Camus.External.NMSC.Splits

/-!
# Four taxa in four components of a cycle

Section 3.3 of CAMUS designs Quartet Filtering (Algorithm 1) for a CF pattern on each set of four
taxa (`Brooqs.RegularPattern`, `Brooqs.Net.RegularOn`): if the network displays one of the three
quartets on them, it is strictly the most probable and the two others are equally probable; if it
displays two, the third is strictly the least probable. This file proves the pattern for four taxa
in four distinct components of a cycle `Ω`, the case of `Brooqs.nmsc_quartetCF`
(`Brooqs.Net.Cycle.regularOn_of_components`).

The displayed quartets are read from the positions of the components on the path of a displayed
tree (`Brooqs.Net.Cycle.displays_iff`): with the hybrid component below the side `side₁` (at
position `0`) or below the side `side₂` (at position `d`), the clusters along the sides contain the
taxa of the components at the positions up to some `k`, or from some `m` on; so the network displays
`ab|ce` iff one of the two paths separates the positions of `a, b` from those of `c, e`
(`Brooqs.pathSep`). The CFs are the `γ`-mixtures of `Brooqs.quartetCF_eq_of_components`, and the
pattern follows (`Brooqs.regularPattern_of_mixture`).

## Main results

* `Brooqs.RegularPattern`, `Brooqs.Net.cf3`, `Brooqs.Net.disp3`, `Brooqs.Net.RegularOn`: the CF
  pattern.
* `Brooqs.Net.Cycle.mem_tail₁_iff`, `Brooqs.Net.Cycle.mem_tail₂_iff`,
  `Brooqs.Net.Cycle.mem_top_iff`: the taxa below the parts of the sides, by positions.
* `Brooqs.Net.Cycle.displays_iff`: the displayed quartets of four components.
* `Brooqs.regularPattern_of_mixture`: the pattern of a `γ`-mixture of two quartet trees.
* `Brooqs.Net.Cycle.regularOn_of_components`: the pattern for four components of a cycle.
-/

@[expose] public noncomputable section

namespace Brooqs

open Finset

universe u

variable {X : Type u} [DecidableEq X] {N : Net X}

/-! ### Taxa and positions -/

namespace Net.Cycle

variable (Ω : N.Cycle)

/-- A taxon lies in at most one component. -/
theorem eq_of_mem_component (hN : N.leaves.Nodup) {t : X} {i j : ℕ} (hi : t ∈ Ω.component i)
    (hj : t ∈ Ω.component j) : i = j := by
  by_contra h
  exact disjoint_left.1 (Ω.component_disjoint hN h) hi hj

/-- A taxon lies below the hybrid node iff it lies in the component at position `0`. -/
theorem mem_below_iff (hN : N.leaves.Nodup) {t : X} {i : ℕ} (ht : t ∈ Ω.component i) :
    t ∈ Ω.below.taxa ↔ i = 0 := by
  rw [← Ω.component_zero]
  exact ⟨fun h => Ω.eq_of_mem_component hN ht h, fun h => h ▸ ht⟩

/-- A taxon lies below a lower part `U` of the side `side₁` with `k` nodes iff its component is at
a position `1, …, k`. -/
theorem mem_tail₁_iff (hN : N.leaves.Nodup) {U : Side X} (hU : U ∈ Ω.side₁.tails) {t : X}
    {i : ℕ} (ht : t ∈ Ω.component i) : t ∈ U.taxa ↔ 1 ≤ i ∧ i ≤ U.nodes.length := by
  have hUn := Side.nodes_of_mem_tails hU
  have hkp : U.nodes.length ≤ Ω.side₁.nodes.length := by
    have := congrArg List.length hUn
    simp only [List.length_drop] at this
    omega
  rw [Side.mem_taxa_iff]
  constructor
  · rintro ⟨n, hn, htn⟩
    rw [hUn] at hn
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hn
    simp only [List.length_drop] at hj
    have hcomp := Ω.component_side₁ (i := U.nodes.length - 1 - j) (by omega)
    rw [List.getElem_reverse] at hcomp
    have hidx : Ω.side₁.nodes.length - 1 - (U.nodes.length - 1 - j) =
        Ω.side₁.nodes.length - U.nodes.length + j := by omega
    rw [List.getElem_drop] at htn
    have htc : t ∈ Ω.component (U.nodes.length - 1 - j + 1) := by
      rw [hcomp]
      simp only [hidx]
      exact htn
    have := Ω.eq_of_mem_component hN ht htc
    omega
  · rintro ⟨h1, h2⟩
    obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    have hcomp := Ω.component_side₁ (i := i') (by omega)
    rw [hcomp] at ht
    refine ⟨_, ?_, ht⟩
    rw [hUn, List.getElem_reverse]
    exact List.mem_drop_iff_getElem.2 ⟨Ω.side₁.nodes.length - 1 - i' -
      (Ω.side₁.nodes.length - U.nodes.length), by omega, by
        congr 1
        omega⟩

/-- The size of a cycle exceeds the number of nodes of its sides. -/
theorem size_ge : Ω.side₁.nodes.length + Ω.side₂.nodes.length + 1 ≤ Ω.size := by
  by_cases h : Ω.top = N
  · rw [Ω.size_of_top_eq h]
  · rw [Ω.size_of_top_ne h]
    omega

/-- A taxon lies below a lower part `U` of the side `side₂` with `k` nodes iff its component is at
a position `d - k, …, d - 1`. -/
theorem mem_tail₂_iff (hN : N.leaves.Nodup) {U : Side X} (hU : U ∈ Ω.side₂.tails) {t : X}
    {i : ℕ} (hi : i < Ω.size) (ht : t ∈ Ω.component i) :
    t ∈ U.taxa ↔ Ω.size - U.nodes.length ≤ i := by
  have hUn := Side.nodes_of_mem_tails hU
  have hkq : U.nodes.length ≤ Ω.side₂.nodes.length := by
    have := congrArg List.length hUn
    simp only [List.length_drop] at this
    omega
  have hsz := Ω.size_ge
  rw [Side.mem_taxa_iff]
  constructor
  · rintro ⟨n, hn, htn⟩
    rw [hUn] at hn
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hn
    simp only [List.length_drop] at hj
    have hcomp := Ω.component_side₂ (i := U.nodes.length - 1 - j) (by omega)
    rw [List.getElem_reverse] at hcomp
    have hidx : Ω.side₂.nodes.length - 1 - (U.nodes.length - 1 - j) =
        Ω.side₂.nodes.length - U.nodes.length + j := by omega
    rw [List.getElem_drop] at htn
    have htc : t ∈ Ω.component (Ω.size - (U.nodes.length - 1 - j + 1)) := by
      rw [hcomp]
      simp only [hidx]
      exact htn
    have := Ω.eq_of_mem_component hN ht htc
    omega
  · intro h
    have hcomp := Ω.component_side₂ (i := Ω.size - 1 - i) (by omega)
    rw [show Ω.size - (Ω.size - 1 - i + 1) = i by omega] at hcomp
    rw [hcomp] at ht
    refine ⟨_, ?_, ht⟩
    rw [hUn, List.getElem_reverse]
    exact List.mem_drop_iff_getElem.2 ⟨Ω.side₂.nodes.length - 1 - (Ω.size - 1 - i) -
      (Ω.side₂.nodes.length - U.nodes.length), by omega, by
        congr 1
        omega⟩

/-- The network hanging from a node of a side is a component of the cycle. -/
theorem exists_component_of_mem_nodes {n : ℝ × ℝ × Net X}
    (hn : n ∈ Ω.side₁.nodes ∨ n ∈ Ω.side₂.nodes) :
    ∃ j < Ω.size, n.2.2.taxa = Ω.component j := by
  have hsz := Ω.size_ge
  rcases hn with hn | hn
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (List.mem_reverse.2 hn)
    simp only [List.length_reverse] at hi
    exact ⟨i + 1, by omega, (Ω.component_side₁ hi).symm⟩
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (List.mem_reverse.2 hn)
    simp only [List.length_reverse] at hi
    exact ⟨Ω.size - (i + 1), by omega, (Ω.component_side₂ hi).symm⟩

omit [DecidableEq X] in
theorem _root_.Brooqs.Side.self_mem_tails (S : Side X) : S ∈ S.tails := by
  cases S <;> simp [Side.tails]

/-- A taxon in the component at position `i` lies below the top node of the cycle iff the
component is not the component of the root, at position `p + 1`. -/
theorem mem_top_iff (hN : N.leaves.Nodup) {t : X} {i : ℕ} (hi : i < Ω.size)
    (ht : t ∈ Ω.component i) :
    t ∈ Ω.top.taxa ↔ Ω.top = N ∨ i ≠ Ω.side₁.nodes.length + 1 := by
  have h1 := Ω.mem_tail₁_iff hN (Side.self_mem_tails _) ht
  have h2 := Ω.mem_tail₂_iff hN (Side.self_mem_tails _) hi ht
  have h0 := Ω.mem_below_iff hN ht
  have htop : Ω.top.taxa = Ω.side₁.taxa ∪ Ω.side₂.taxa ∪ Ω.below.taxa := Net.taxa_cycle _ _ _ _ _
  rw [htop, mem_union, mem_union, h1, h2, h0]
  by_cases h : Ω.top = N
  · have := Ω.size_of_top_eq h
    simp only [h, true_or, iff_true]
    omega
  · have := Ω.size_of_top_ne h
    simp only [h, false_or]
    omega

end Net.Cycle

/-! ### The displayed quartets of four components -/

/-- The quartet tree on the path `0 — 1 — ⋯ — d` with the four taxa at the positions `a, b, c, e`
has the split `ab|ce`: the condition of `Brooqs.pathCF`. -/
def pathSep (a b c e : ℕ) : Prop := max a b < min c e ∨ max c e < min a b

instance (a b c e : ℕ) : Decidable (pathSep a b c e) := by
  unfold pathSep
  infer_instance

/-- The cluster `A` cuts the quartet `s a, s b | s c, s e`. -/
private def fc_cuts (A : Finset X) (s : Fin 4 → X) (a b c e : Fin 4) : Prop :=
  (s a ∈ A ∧ s b ∈ A ∧ s c ∉ A ∧ s e ∉ A) ∨ (s c ∈ A ∧ s e ∈ A ∧ s a ∉ A ∧ s b ∉ A)

omit [DecidableEq X] in
private theorem fc_cuts_le {A : Finset X} {s : Fin 4 → X} {P : Fin 4 → ℕ} {k : ℕ}
    (hA : ∀ l, s l ∈ A ↔ P l ≤ k) {a b c e : Fin 4} (h : fc_cuts A s a b c e) :
    pathSep (P a) (P b) (P c) (P e) := by
  unfold fc_cuts at h
  simp only [hA] at h
  unfold pathSep
  omega

omit [DecidableEq X] in
private theorem fc_cuts_ge {A : Finset X} {s : Fin 4 → X} {P : Fin 4 → ℕ} {m : ℕ}
    (hA : ∀ l, s l ∈ A ↔ m ≤ P l) {a b c e : Fin 4} (h : fc_cuts A s a b c e) :
    pathSep (P a) (P b) (P c) (P e) := by
  unfold fc_cuts at h
  simp only [hA] at h
  unfold pathSep
  omega

section Components

variable (Ω : N.Cycle) {s : Fin 4 → X} {pos : Fin 4 → ℕ}

/-- The clusters of a displayed tree of the top of the cycle `Ω`, seen from four taxa in distinct
components: the cluster of all the taxa of the cycle; a cluster inside one component; or, along
a side, the taxa at the positions up to `k` or from `m` on, for the hybrid component at position
`0` (`pos`) or at position `d` (`toRightEnd`). -/
private theorem fc_cluster_cases (hN : N.leaves.Nodup) (hlt : ∀ l, pos l < Ω.size)
    (hs : ∀ l, s l ∈ Ω.component (pos l)) {K : Finset (Finset X)} (hK : K ∈ Ω.top.displayed)
    {A : Finset X} (hA : A ∈ K) :
    A = Ω.top.taxa ∨ (∃ j, A ⊆ Ω.component j) ∨ (∃ k, ∀ l, s l ∈ A ↔ pos l ≤ k) ∨
      (∃ m, ∀ l, s l ∈ A ↔ m ≤ pos l) ∨
      (∃ k, ∀ l, s l ∈ A ↔ toRightEnd Ω.size (pos l) ≤ k) ∨
      (∃ m, ∀ l, s l ∈ A ↔ m ≤ toRightEnd Ω.size (pos l)) := by
  have hsz := Ω.size_ge
  have htop : Ω.top = .cycle Ω.γ Ω.side₁ Ω.side₂ Ω.ℓ Ω.below := rfl
  have htaxa : Ω.top.taxa = Ω.side₁.taxa ∪ Ω.side₂.taxa ∪ Ω.below.taxa := Net.taxa_cycle _ _ _ _ _
  have h0 := fun l => Ω.mem_below_iff hN (hs l)
  have hpend : ∀ {S : Side X} {T : Finset X} {K₁ : Finset (Finset X)}, K₁ ∈ S.displayed T →
      (∀ n ∈ S.nodes, n ∈ Ω.side₁.nodes ∨ n ∈ Ω.side₂.nodes) → A ∈ K₁ →
      (∃ j, A ⊆ Ω.component j) ∨ ∃ U ∈ S.tails, A = T ∪ U.taxa := by
    intro S T K₁ hK₁ hS hA₁
    rcases Side.cluster_of_mem_displayed hK₁ A hA₁ with ⟨n, hn, K', hK', hAK'⟩ | h
    · obtain ⟨j, -, hj⟩ := Ω.exists_component_of_mem_nodes (hS n hn)
      exact Or.inl ⟨j, hj ▸ Net.subset_taxa_of_mem_displayed hK' A hAK'⟩
    · exact Or.inr h
  rw [htop] at hK
  simp only [Net.displayed, List.mem_flatMap, List.mem_append, List.mem_map] at hK
  obtain ⟨K₀, hK₀, ⟨K₁, hK₁, K₂, hK₂, rfl⟩ | ⟨K₁, hK₁, K₂, hK₂, rfl⟩⟩ := hK
  all_goals
    rcases mem_insert.1 hA with rfl | hA
    · exact Or.inl htaxa.symm
    rcases mem_union.1 hA with hA | hA
    · rcases mem_union.1 hA with hA | hA
      · exact Or.inr (Or.inl ⟨0, Ω.component_zero ▸ Net.subset_taxa_of_mem_displayed hK₀ A hA⟩)
      · rcases hpend hK₁ (fun n hn => Or.inl hn) hA with h | ⟨U, hU, rfl⟩
        · exact Or.inr (Or.inl h)
        · have h1 := fun l => Ω.mem_tail₁_iff hN hU (hs l)
          have hkp : U.nodes.length ≤ Ω.side₁.nodes.length := by
            have := congrArg List.length (Side.nodes_of_mem_tails hU)
            simp only [List.length_drop] at this
            omega
          first
            | refine Or.inr (Or.inr (Or.inl ⟨U.nodes.length, fun l => ?_⟩))
              rw [mem_union, h0 l, h1 l]
              omega
            | refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨U.nodes.length, fun l => ?_⟩))))
              rw [empty_union, h1 l]
              have := hlt l
              unfold toRightEnd
              split_ifs <;> omega
    · rcases hpend hK₂ (fun n hn => Or.inr hn) hA with h | ⟨U, hU, rfl⟩
      · exact Or.inr (Or.inl h)
      · have h2 := fun l => Ω.mem_tail₂_iff hN hU (hlt l) (hs l)
        first
          | refine Or.inr (Or.inr (Or.inr (Or.inl ⟨Ω.size - U.nodes.length, fun l => ?_⟩)))
            rw [empty_union, h2 l]
          | refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              ⟨Ω.size - U.nodes.length, fun l => ?_⟩))))
            rw [mem_union, h0 l, h2 l]
            have := hlt l
            unfold toRightEnd
            split_ifs <;> omega

/-- A displayed tree of the top of `Ω` with a cluster cutting the quartet gives a displayed tree of
`N` that displays it. -/
private theorem fc_displays_of_top {a b c e : Fin 4} {K : Finset (Finset X)}
    (hK : K ∈ Ω.top.displayed) {A : Finset X} (hA : A ∈ K) (h : fc_cuts A s a b c e) :
    N.Displays (s a) (s b) (s c) (s e) := by
  obtain ⟨K', hK', hsub⟩ := Net.extend_displayed Ω.mem K hK
  exact ⟨K', hK', decide_eq_true ⟨A, hsub hA, h⟩⟩

/-- Two lineages below two others on the path with the hybrid component at position `0`: a
displayed tree of the top of `Ω`, with the hybrid component below the side `side₁`, separates
them. -/
private theorem fc_cut₁ (hN : N.leaves.Nodup) (hlt : ∀ l, pos l < Ω.size)
    (hs : ∀ l, s l ∈ Ω.component (pos l)) {x y z w : Fin 4} (hxy : pos x ≠ pos y)
    (hlow : max (pos x) (pos y) < min (pos z) (pos w)) :
    ∃ K ∈ Ω.top.displayed, ∃ A ∈ K,
      (s x ∈ A ∧ s y ∈ A ∧ s z ∉ A ∧ s w ∉ A) ∨ (s z ∈ A ∧ s w ∈ A ∧ s x ∉ A ∧ s y ∉ A) := by
  have hsz := Ω.size_ge
  have hsz' : Ω.size ≤ Ω.side₁.nodes.length + Ω.side₂.nodes.length + 2 := by
    by_cases h : Ω.top = N
    · rw [Ω.size_of_top_eq h]
      omega
    · rw [Ω.size_of_top_ne h]
  have h0 := fun l => Ω.mem_below_iff hN (hs l)
  obtain ⟨K₀, hK₀⟩ := List.exists_mem_of_ne_nil _ (Net.displayed_ne_nil Ω.below)
  obtain ⟨K₁, hK₁⟩ := List.exists_mem_of_ne_nil _ (Side.displayed_ne_nil Ω.side₁ Ω.below.taxa)
  obtain ⟨K₂, hK₂⟩ := List.exists_mem_of_ne_nil _ (Side.displayed_ne_nil Ω.side₂ ∅)
  have hK : insert (Ω.side₁.taxa ∪ Ω.side₂.taxa ∪ Ω.below.taxa) (K₀ ∪ K₁ ∪ K₂) ∈
      Ω.top.displayed := by
    show _ ∈ (Net.cycle Ω.γ Ω.side₁ Ω.side₂ Ω.ℓ Ω.below).displayed
    simp only [Net.displayed, List.mem_flatMap, List.mem_append, List.mem_map]
    exact ⟨K₀, hK₀, Or.inl ⟨K₁, hK₁, K₂, hK₂, rfl⟩⟩
  refine ⟨_, hK, ?_⟩
  by_cases hm : max (pos x) (pos y) ≤ Ω.side₁.nodes.length
  · -- the cluster of the node of `side₁` at the height of the upper of `x, y`
    obtain ⟨U, hU, hUk⟩ := Side.exists_tail Ω.side₁ _ hm
    have hne : U.nodes ≠ [] := by
      intro h
      rw [h] at hUk
      simp at hUk
      omega
    refine ⟨Ω.below.taxa ∪ U.taxa, mem_insert_of_mem (mem_union_left _ (mem_union_right _
      (Side.tail_mem_displayed hK₁ U hU hne))), Or.inl ?_⟩
    have hmem : ∀ l, s l ∈ Ω.below.taxa ∪ U.taxa ↔ pos l ≤ max (pos x) (pos y) := by
      intro l
      rw [mem_union, h0 l, Ω.mem_tail₁_iff hN hU (hs l), hUk]
      omega
    simp only [hmem]
    exact ⟨le_max_left _ _, le_max_right _ _, not_le.2 (hlow.trans_le (min_le_left _ _)),
      not_le.2 (hlow.trans_le (min_le_right _ _))⟩
  · -- the cluster of the node of `side₂` at the height of the lower of `z, w`
    obtain ⟨U, hU, hUk⟩ := Side.exists_tail Ω.side₂ (Ω.size - min (pos z) (pos w)) (by
      have := hlt z
      have := hlt w
      omega)
    have hne : U.nodes ≠ [] := by
      intro h
      rw [h] at hUk
      simp at hUk
      have := hlt z
      have := hlt w
      omega
    refine ⟨∅ ∪ U.taxa, mem_insert_of_mem (mem_union_right _
      (Side.tail_mem_displayed hK₂ U hU hne)), Or.inr ?_⟩
    have hmem : ∀ l, s l ∈ ∅ ∪ U.taxa ↔ min (pos z) (pos w) ≤ pos l := by
      intro l
      rw [empty_union, Ω.mem_tail₂_iff hN hU (hlt l) (hs l), hUk]
      have := hlt z
      have := hlt w
      omega
    simp only [hmem]
    exact ⟨min_le_left _ _, min_le_right _ _, not_le.2 ((le_max_left _ _).trans_lt hlow),
      not_le.2 ((le_max_right _ _).trans_lt hlow)⟩

/-- The same on the path with the hybrid component at position `d`, with the hybrid component
below the side `side₂`. -/
private theorem fc_cut₂ (hN : N.leaves.Nodup) (hlt : ∀ l, pos l < Ω.size)
    (hs : ∀ l, s l ∈ Ω.component (pos l)) {x y z w : Fin 4}
    (hzw : toRightEnd Ω.size (pos z) ≠ toRightEnd Ω.size (pos w))
    (hlow : max (toRightEnd Ω.size (pos x)) (toRightEnd Ω.size (pos y)) <
      min (toRightEnd Ω.size (pos z)) (toRightEnd Ω.size (pos w))) :
    ∃ K ∈ Ω.top.displayed, ∃ A ∈ K,
      (s x ∈ A ∧ s y ∈ A ∧ s z ∉ A ∧ s w ∉ A) ∨ (s z ∈ A ∧ s w ∈ A ∧ s x ∉ A ∧ s y ∉ A) := by
  have hsz := Ω.size_ge
  have hsz' : Ω.size ≤ Ω.side₁.nodes.length + Ω.side₂.nodes.length + 2 := by
    by_cases h : Ω.top = N
    · rw [Ω.size_of_top_eq h]
      omega
    · rw [Ω.size_of_top_ne h]
  have h0 := fun l => Ω.mem_below_iff hN (hs l)
  have hP : ∀ l, 1 ≤ toRightEnd Ω.size (pos l) ∧ toRightEnd Ω.size (pos l) ≤ Ω.size ∧
      (pos l = 0 → toRightEnd Ω.size (pos l) = Ω.size) ∧
      (pos l ≠ 0 → toRightEnd Ω.size (pos l) = pos l) := by
    intro l
    have := hlt l
    unfold toRightEnd
    split_ifs <;> omega
  obtain ⟨K₀, hK₀⟩ := List.exists_mem_of_ne_nil _ (Net.displayed_ne_nil Ω.below)
  obtain ⟨K₁, hK₁⟩ := List.exists_mem_of_ne_nil _ (Side.displayed_ne_nil Ω.side₁ ∅)
  obtain ⟨K₂, hK₂⟩ := List.exists_mem_of_ne_nil _ (Side.displayed_ne_nil Ω.side₂ Ω.below.taxa)
  have hK : insert (Ω.side₁.taxa ∪ Ω.side₂.taxa ∪ Ω.below.taxa) (K₀ ∪ K₁ ∪ K₂) ∈
      Ω.top.displayed := by
    show _ ∈ (Net.cycle Ω.γ Ω.side₁ Ω.side₂ Ω.ℓ Ω.below).displayed
    simp only [Net.displayed, List.mem_flatMap, List.mem_append, List.mem_map]
    exact ⟨K₀, hK₀, Or.inr ⟨K₁, hK₁, K₂, hK₂, rfl⟩⟩
  refine ⟨_, hK, ?_⟩
  have hx := hP x
  have hy := hP y
  have hz := hP z
  have hw := hP w
  by_cases hm : max (toRightEnd Ω.size (pos x)) (toRightEnd Ω.size (pos y)) ≤
      Ω.side₁.nodes.length
  · obtain ⟨U, hU, hUk⟩ := Side.exists_tail Ω.side₁ _ hm
    have hne : U.nodes ≠ [] := by
      intro h
      rw [h] at hUk
      simp at hUk
      omega
    refine ⟨∅ ∪ U.taxa, mem_insert_of_mem (mem_union_left _ (mem_union_right _
      (Side.tail_mem_displayed hK₁ U hU hne))), Or.inl ?_⟩
    have hmem : ∀ l, s l ∈ ∅ ∪ U.taxa ↔
        toRightEnd Ω.size (pos l) ≤ max (toRightEnd Ω.size (pos x))
          (toRightEnd Ω.size (pos y)) := by
      intro l
      rw [empty_union, Ω.mem_tail₁_iff hN hU (hs l), hUk]
      have := hP l
      by_cases h : pos l = 0
      · rw [this.2.2.1 h]
        omega
      · rw [this.2.2.2 h]
        omega
    simp only [hmem]
    exact ⟨le_max_left _ _, le_max_right _ _, not_le.2 (hlow.trans_le (min_le_left _ _)),
      not_le.2 (hlow.trans_le (min_le_right _ _))⟩
  · obtain ⟨U, hU, hUk⟩ := Side.exists_tail Ω.side₂
      (Ω.size - min (toRightEnd Ω.size (pos z)) (toRightEnd Ω.size (pos w))) (by omega)
    have hne : U.nodes ≠ [] := by
      intro h
      rw [h] at hUk
      simp at hUk
      omega
    refine ⟨Ω.below.taxa ∪ U.taxa, mem_insert_of_mem (mem_union_right _
      (Side.tail_mem_displayed hK₂ U hU hne)), Or.inr ?_⟩
    have hmem : ∀ l, s l ∈ Ω.below.taxa ∪ U.taxa ↔
        min (toRightEnd Ω.size (pos z)) (toRightEnd Ω.size (pos w)) ≤
          toRightEnd Ω.size (pos l) := by
      intro l
      rw [mem_union, h0 l, Ω.mem_tail₂_iff hN hU (hlt l) (hs l), hUk]
      have := hP l
      by_cases h : pos l = 0
      · rw [this.2.2.1 h]
        omega
      · rw [this.2.2.2 h]
        omega
    simp only [hmem]
    exact ⟨min_le_left _ _, min_le_right _ _, not_le.2 ((le_max_left _ _).trans_lt hlow),
      not_le.2 ((le_max_right _ _).trans_lt hlow)⟩

/-- **The quartets of four components.** Four taxa `s 0, …, s 3` in four distinct components of a
cycle `Ω`, at the positions `pos l`: `N` displays `s a s b | s c s e` iff the path
`0 — 1 — ⋯ — d` with the four taxa at their positions (the displayed tree with the hybrid component
below the side `side₁`, at position `0`) or with the hybrid component moved to position `d` (below
the side `side₂`) has the split `ab|ce`. -/
theorem displays_iff (hN : N.leaves.Nodup) (hinj : Function.Injective pos)
    (hlt : ∀ l, pos l < Ω.size) (hs : ∀ l, s l ∈ Ω.component (pos l)) {a b c e : Fin 4}
    (hab : a ≠ b) (hce : c ≠ e) :
    N.Displays (s a) (s b) (s c) (s e) ↔
      pathSep (pos a) (pos b) (pos c) (pos e) ∨
        pathSep (toRightEnd Ω.size (pos a)) (toRightEnd Ω.size (pos b))
          (toRightEnd Ω.size (pos c)) (toRightEnd Ω.size (pos e)) := by
  have hne : ∀ {i j : Fin 4}, i ≠ j → pos i ≠ pos j := fun h h' => h (hinj h')
  have hne' : ∀ {i j : Fin 4}, i ≠ j → toRightEnd Ω.size (pos i) ≠ toRightEnd Ω.size (pos j) := by
    intro i j h h'
    have := hne h
    have := hlt i
    have := hlt j
    unfold toRightEnd at h'
    split_ifs at h' <;> omega
  constructor
  · rintro ⟨K, hK, h⟩
    obtain ⟨A, hA, hcut⟩ := of_decide_eq_true h
    have hcut' : fc_cuts A s a b c e := hcut
    -- two taxa of the four lie in the cluster, the two others do not
    have hin : ∃ x y z w : Fin 4, x ≠ y ∧ z ≠ w ∧ s x ∈ A ∧ s y ∈ A ∧ s z ∉ A ∧ s w ∉ A := by
      rcases hcut with h | h
      · exact ⟨a, b, c, e, hab, hce, h⟩
      · exact ⟨c, e, a, b, hce, hab, h⟩
    obtain ⟨x, y, z, w, hxy, hzw, hx, hy, hz, hw⟩ := hin
    have hcontra : ¬ Ω.top.taxa ⊆ A := by
      intro hsub
      rcases (Ω.mem_top_iff hN (hlt z) (hs z)).2 |>.mt (fun h => hz (hsub h)) |> not_or.1 with
        ⟨h1, h2⟩
      have := (Ω.mem_top_iff hN (hlt w) (hs w)).2 (Or.inr (fun h3 => hne hzw (by
        push Not at h2
        rw [h2, h3])))
      exact hw (hsub this)
    obtain ⟨K', hK', hAK'⟩ := Net.restrict_displayed hN Ω.mem K hK
    rcases hAK' A hA with hA' | hsup | hdis
    · rcases fc_cluster_cases Ω hN hlt hs hK' hA' with
          h | ⟨j, hj⟩ | ⟨k, hk⟩ | ⟨m, hm⟩ | ⟨k, hk⟩ | ⟨m, hm⟩
      · exact absurd (h ▸ subset_rfl) hcontra
      · exact absurd ((Ω.eq_of_mem_component hN (hs x) (hj hx)).trans
          (Ω.eq_of_mem_component hN (hs y) (hj hy)).symm) (hne hxy)
      · exact Or.inl (fc_cuts_le hk hcut')
      · exact Or.inl (fc_cuts_ge hm hcut')
      · exact Or.inr (fc_cuts_le hk hcut')
      · exact Or.inr (fc_cuts_ge hm hcut')
    · exact absurd hsup hcontra
    · have hxo := (Ω.mem_top_iff hN (hlt x) (hs x)).not.1
        (fun h => disjoint_left.1 hdis hx h)
      have hyo := (Ω.mem_top_iff hN (hlt y) (hs y)).not.1
        (fun h => disjoint_left.1 hdis hy h)
      push Not at hxo hyo
      exact absurd (hxo.2.trans hyo.2.symm) (hne hxy)
  · rintro (h | h)
    · rcases h with h | h
      · obtain ⟨K, hK, A, hA, hcut⟩ := fc_cut₁ Ω hN hlt hs (hne hab) h
        exact fc_displays_of_top Ω hK hA hcut
      · obtain ⟨K, hK, A, hA, hcut⟩ := fc_cut₁ Ω hN hlt hs (hne hce) h
        exact fc_displays_of_top Ω hK hA (Or.comm.1 hcut)
    · rcases h with h | h
      · obtain ⟨K, hK, A, hA, hcut⟩ := fc_cut₂ Ω hN hlt hs (hne' hce) h
        exact fc_displays_of_top Ω hK hA hcut
      · obtain ⟨K, hK, A, hA, hcut⟩ := fc_cut₂ Ω hN hlt hs (hne' hab) h
        exact fc_displays_of_top Ω hK hA (Or.comm.1 hcut)

end Components

/-! ### The CF pattern -/

/-- The CF pattern that the design of Quartet Filtering presumes on four taxa (Section 3.3 of
CAMUS), for the three quartets on them, numbered `0, 1, 2`, displayed or not (`disp`), with CFs
`cf`: the network displays exactly one of them, which is strictly the most probable, the two
others being equally probable, with positive probability; or it displays exactly two of them, and
the third is strictly the least probable. -/
def RegularPattern (disp : Fin 3 → Prop) (cf : Fin 3 → ℝ) : Prop :=
  (∃ s₁, disp s₁ ∧ (∀ s, s ≠ s₁ → ¬ disp s) ∧ (∀ s, s ≠ s₁ → cf s < cf s₁) ∧
      (∀ s s', s ≠ s₁ → s' ≠ s₁ → cf s = cf s') ∧ ∀ s, 0 < cf s) ∨
  (∃ s₃, ¬ disp s₃ ∧ (∀ s, s ≠ s₃ → disp s) ∧ ∀ s, s ≠ s₃ → cf s₃ < cf s)

/-- The quartet CFs of the three quartets `ab|ce`, `ac|be`, `ae|bc` on four taxa. -/
def Net.cf3 (N : Net X) (a b c e : X) : Fin 3 → ℝ :=
  ![N.quartetCF a b c e, N.quartetCF a c b e, N.quartetCF a e b c]

/-- Whether `N` displays the three quartets `ab|ce`, `ac|be`, `ae|bc`. -/
def Net.disp3 (N : Net X) (a b c e : X) : Fin 3 → Prop :=
  ![N.Displays a b c e, N.Displays a c b e, N.Displays a e b c]

/-- The four taxa `a, b, c, e` have the CF pattern that Quartet Filtering presumes. -/
def Net.RegularOn (N : Net X) (a b c e : X) : Prop :=
  RegularPattern (N.disp3 a b c e) (N.cf3 a b c e)

private theorem fc_other : ∀ a b : Fin 3, ∃ u : Fin 3, u ≠ a ∧ u ≠ b := by
  decide

private theorem fc_cover : ∀ a b c s : Fin 3, a ≠ b → c ≠ a → c ≠ b → s ≠ c → s = a ∨ s = b := by
  decide

/-- **A mixture of two quartet trees.** If each quartet's CF is the `γ`-mixture of its CFs `g₁`
and `g₂` on two quartet trees, `1 - (2/3) u` for the split of the tree and `u/3` for the others
(`0 < u < 1`), and the network displays exactly the splits of the two trees, the CFs have the
pattern `RegularPattern`. -/
theorem regularPattern_of_mixture {disp : Fin 3 → Prop} {cf g₁ g₂ : Fin 3 → ℝ}
    {S₁ S₂ : Fin 3 → Prop} {γ u₁ u₂ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hu₁0 : 0 < u₁)
    (hu₁1 : u₁ < 1) (hu₂0 : 0 < u₂) (hu₂1 : u₂ < 1) (h₁ : ∃! i, S₁ i) (h₂ : ∃! i, S₂ i)
    (hdisp : ∀ i, disp i ↔ S₁ i ∨ S₂ i) (hcf : ∀ i, cf i = γ * g₁ i + (1 - γ) * g₂ i)
    (hg₁ : ∀ i, (S₁ i → g₁ i = 1 - 2 / 3 * u₁) ∧ (¬ S₁ i → g₁ i = 1 / 3 * u₁))
    (hg₂ : ∀ i, (S₂ i → g₂ i = 1 - 2 / 3 * u₂) ∧ (¬ S₂ i → g₂ i = 1 / 3 * u₂)) :
    RegularPattern disp cf := by
  obtain ⟨i₁, hi₁, hu₁⟩ := h₁
  obtain ⟨i₂, hi₂, hu₂⟩ := h₂
  have hn₁ : ∀ s, s ≠ i₁ → ¬ S₁ s := fun s hs h => hs (hu₁ s h)
  have hn₂ : ∀ s, s ≠ i₂ → ¬ S₂ s := fun s hs h => hs (hu₂ s h)
  have hpos : ∀ s, 0 < cf s := fun s => by
    rw [hcf]
    have : 0 < g₁ s := by
      by_cases h : S₁ s
      · rw [(hg₁ s).1 h]
        linarith
      · rw [(hg₁ s).2 h]
        linarith
    have : 0 < g₂ s := by
      by_cases h : S₂ s
      · rw [(hg₂ s).1 h]
        linarith
      · rw [(hg₂ s).2 h]
        linarith
    have : 0 < 1 - γ := by linarith
    positivity
  by_cases h : i₁ = i₂
  · -- one displayed tree
    subst h
    left
    refine ⟨i₁, (hdisp _).2 (Or.inl hi₁), fun s hs hd => ?_, fun s hs => ?_,
      fun s s' hs hs' => ?_, hpos⟩
    · rcases (hdisp s).1 hd with h | h
      · exact hn₁ s hs h
      · exact hn₂ s hs h
    · rw [hcf, hcf, (hg₁ _).1 hi₁, (hg₂ _).1 hi₂, (hg₁ _).2 (hn₁ s hs), (hg₂ _).2 (hn₂ s hs)]
      nlinarith
    · rw [hcf, hcf, (hg₁ _).2 (hn₁ s hs), (hg₂ _).2 (hn₂ s hs), (hg₁ _).2 (hn₁ s' hs'),
        (hg₂ _).2 (hn₂ s' hs')]
  · -- two displayed trees
    right
    obtain ⟨i₃, h31, h32⟩ := fc_other i₁ i₂
    refine ⟨i₃, fun hd => ?_, fun s hs => ?_, fun s hs => ?_⟩
    · rcases (hdisp i₃).1 hd with h' | h'
      · exact hn₁ i₃ h31 h'
      · exact hn₂ i₃ h32 h'
    · rcases fc_cover i₁ i₂ i₃ s h h31 h32 hs with rfl | rfl
      · exact (hdisp _).2 (Or.inl hi₁)
      · exact (hdisp _).2 (Or.inr hi₂)
    · rcases fc_cover i₁ i₂ i₃ s h h31 h32 hs with rfl | rfl
      · rw [hcf, hcf, (hg₁ _).1 hi₁, (hg₂ _).2 (hn₂ s h), (hg₁ _).2 (hn₁ i₃ h31),
          (hg₂ _).2 (hn₂ i₃ h32)]
        nlinarith
      · rw [hcf, hcf, (hg₂ _).1 hi₂, (hg₁ _).2 (hn₁ s (Ne.symm h)), (hg₁ _).2 (hn₁ i₃ h31),
          (hg₂ _).2 (hn₂ i₃ h32)]
        nlinarith

/-- The length of the path between the two middle positions does not depend on how the four
positions are paired. -/
private theorem fc_mid (a b c e : ℕ) :
    min (max (min a b) (min c e)) (min (max a b) (max c e)) =
      min (max (min a c) (min b e)) (min (max a c) (max b e)) ∧
    max (max (min a b) (min c e)) (min (max a b) (max c e)) =
      max (max (min a c) (min b e)) (min (max a c) (max b e)) ∧
    min (max (min a b) (min c e)) (min (max a b) (max c e)) =
      min (max (min a e) (min b c)) (min (max a e) (max b c)) ∧
    max (max (min a b) (min c e)) (min (max a b) (max c e)) =
      max (max (min a e) (min b c)) (min (max a e) (max b c)) := by
  omega

/-- Of the three ways to pair four distinct positions, exactly one separates the two smallest from
the two largest. -/
private theorem fc_sep_unique {a b c e : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hae : a ≠ e)
    (hbc : b ≠ c) (hbe : b ≠ e) (hce : c ≠ e) :
    ∃! i : Fin 3, (![pathSep a b c e, pathSep a c b e, pathSep a e b c] : Fin 3 → Prop) i := by
  unfold pathSep
  by_cases h0 : max a b < min c e ∨ max c e < min a b
  · refine ⟨0, h0, fun i hi => ?_⟩
    fin_cases i
    · rfl
    · simp only [Fin.isValue, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero] at hi
      omega
    · simp only [Fin.reduceFinMk, Matrix.cons_val] at hi
      omega
  by_cases h1 : max a c < min b e ∨ max b e < min a c
  · refine ⟨1, h1, fun i hi => ?_⟩
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero] at hi
      omega
    · rfl
    · simp only [Fin.reduceFinMk, Matrix.cons_val] at hi
      omega
  · refine ⟨2, by simp only [Fin.isValue, Matrix.cons_val]; omega, fun i hi => ?_⟩
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero] at hi
      omega
    · simp only [Fin.isValue, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero] at hi
      omega
    · rfl

/-- The path between the two middle positions of four distinct positions in `[lo, hi]` has
positive length when the edges between `lo + 1` and `hi - 1` have positive lengths. -/
private theorem fc_pathLen_pos {W : ℕ → ℝ} {lo hi : ℕ}
    (hW : ∀ m, lo + 1 ≤ m → m + 2 ≤ hi → 0 < W m) {a b c e : ℕ} (hab : a ≠ b) (hac : a ≠ c)
    (hae : a ≠ e) (hbc : b ≠ c) (hbe : b ≠ e) (hce : c ≠ e) (ha : lo ≤ a ∧ a ≤ hi)
    (hb : lo ≤ b ∧ b ≤ hi) (hc : lo ≤ c ∧ c ≤ hi) (he : lo ≤ e ∧ e ≤ hi) :
    0 < pathLen W (min (max (min a b) (min c e)) (min (max a b) (max c e)))
      (max (max (min a b) (min c e)) (min (max a b) (max c e))) := by
  unfold pathLen
  refine sum_pos (fun m hm => hW m ?_ ?_) (nonempty_Ico.2 (by omega))
  · rw [mem_Ico] at hm
    omega
  · rw [mem_Ico] at hm
    omega

/-- **Four components of a cycle.** For four taxa in four distinct components of a cycle of a
metric network with distinct leaf labels, the quartet CFs have the pattern that Quartet Filtering
presumes: if the hybrid component is not among the four, the network displays one quartet, the
quartet of the tree, with CF `1 - (2/3) e^{-t}` against `(1/3) e^{-t}` for the two others; if it
is, the network displays two quartets, the quartets of its two displayed trees, and the third is
strictly less probable (the `γ`-mixture of `Brooqs.nmsc_quartetCF`). -/
theorem Net.Cycle.regularOn_of_components (hN : N.WellFormed) (Ω : N.Cycle) {s : Fin 4 → X}
    {pos : Fin 4 → ℕ} (hinj : Function.Injective pos) (hlt : ∀ l, pos l < Ω.size)
    (hs : ∀ l, s l ∈ Ω.component (pos l)) :
    N.RegularOn (s 0) (s 1) (s 2) (s 3) := by
  -- the inheritance probability and the edge lengths of the cycle
  obtain ⟨hγ0, hγ1, -⟩ := Net.isMetric_of_mem_subnets Ω.mem hN.1
  obtain ⟨M, -, hMw⟩ := Ω.exists_metricCycle hN
  have hW : ∀ m, 1 ≤ m → m + 2 ≤ Ω.size → 0 < Ω.edgeLen m := fun m h1 h2 => by
    rw [← hMw m h1 (by omega)]
    exact M.w_pos m h1 (by omega)
  have hne : ∀ {i j : Fin 4}, i ≠ j → pos i ≠ pos j := fun h h' => h (hinj h')
  set P' : Fin 4 → ℕ := fun l => toRightEnd Ω.size (pos l) with hP'
  have hP'b : ∀ l, 1 ≤ P' l ∧ P' l ≤ Ω.size := fun l => by
    have := hlt l
    simp only [hP', toRightEnd]
    split_ifs <;> omega
  have hne' : ∀ {i j : Fin 4}, i ≠ j → P' i ≠ P' j := fun {i j} h h' => by
    have := hne h
    have := hlt i
    have := hlt j
    simp only [hP', toRightEnd] at h'
    split_ifs at h' <;> omega
  -- the CFs of the three quartets: `γ`-mixtures over the two displayed trees
  have hcf : ∀ {i j k l : Fin 4}, Function.Injective ![i, j, k, l] →
      N.quartetCF (s i) (s j) (s k) (s l) =
        Ω.γ * pathCF Ω.edgeLen (pos i) (pos j) (pos k) (pos l) +
          (1 - Ω.γ) * pathCF Ω.edgeLen (P' i) (P' j) (P' k) (P' l) := by
    intro i j k l hijkl
    have hcomp : ![pos i, pos j, pos k, pos l] = pos ∘ ![i, j, k, l] := by
      funext m
      fin_cases m <;> rfl
    have h := quartetCF_eq_of_components N hN Ω ![s i, s j, s k, s l]
      (pos := ![pos i, pos j, pos k, pos l]) (hcomp ▸ hinj.comp hijkl) (fun m => by
        fin_cases m <;> exact hlt _) (fun m => by fin_cases m <;> exact hs _)
    exact h
  set t₁ := pathLen Ω.edgeLen (min (max (min (pos 0) (pos 1)) (min (pos 2) (pos 3)))
      (min (max (pos 0) (pos 1)) (max (pos 2) (pos 3))))
    (max (max (min (pos 0) (pos 1)) (min (pos 2) (pos 3)))
      (min (max (pos 0) (pos 1)) (max (pos 2) (pos 3)))) with ht₁
  set t₂ := pathLen Ω.edgeLen (min (max (min (P' 0) (P' 1)) (min (P' 2) (P' 3)))
      (min (max (P' 0) (P' 1)) (max (P' 2) (P' 3))))
    (max (max (min (P' 0) (P' 1)) (min (P' 2) (P' 3)))
      (min (max (P' 0) (P' 1)) (max (P' 2) (P' 3)))) with ht₂
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have h02 : (0 : Fin 4) ≠ 2 := by decide
  have h03 : (0 : Fin 4) ≠ 3 := by decide
  have h12 : (1 : Fin 4) ≠ 2 := by decide
  have h13 : (1 : Fin 4) ≠ 3 := by decide
  have h23 : (2 : Fin 4) ≠ 3 := by decide
  have ht₁pos : 0 < t₁ := fc_pathLen_pos (lo := 0) (hi := Ω.size - 1)
    (fun m h1 h2 => hW m (by omega) (by omega)) (hne h01) (hne h02) (hne h03) (hne h12)
    (hne h13) (hne h23) ⟨Nat.zero_le _, by have := hlt 0; omega⟩
    ⟨Nat.zero_le _, by have := hlt 1; omega⟩ ⟨Nat.zero_le _, by have := hlt 2; omega⟩
    ⟨Nat.zero_le _, by have := hlt 3; omega⟩
  have ht₂pos : 0 < t₂ := fc_pathLen_pos (lo := 1) (hi := Ω.size)
    (fun m h1 h2 => hW m (by omega) (by omega)) (hne' h01) (hne' h02) (hne' h03) (hne' h12)
    (hne' h13) (hne' h23) (hP'b 0) (hP'b 1) (hP'b 2) (hP'b 3)
  -- each `pathCF` of the three pairings reads the same middle path
  have hpath : ∀ {P : Fin 4 → ℕ} {t : ℝ}, t = pathLen Ω.edgeLen
        (min (max (min (P 0) (P 1)) (min (P 2) (P 3))) (min (max (P 0) (P 1)) (max (P 2) (P 3))))
        (max (max (min (P 0) (P 1)) (min (P 2) (P 3))) (min (max (P 0) (P 1)) (max (P 2) (P 3)))) →
      (pathCF Ω.edgeLen (P 0) (P 1) (P 2) (P 3) =
        if pathSep (P 0) (P 1) (P 2) (P 3) then 1 - 2 / 3 * Real.exp (-t)
          else 1 / 3 * Real.exp (-t)) ∧
      (pathCF Ω.edgeLen (P 0) (P 2) (P 1) (P 3) =
        if pathSep (P 0) (P 2) (P 1) (P 3) then 1 - 2 / 3 * Real.exp (-t)
          else 1 / 3 * Real.exp (-t)) ∧
      (pathCF Ω.edgeLen (P 0) (P 3) (P 1) (P 2) =
        if pathSep (P 0) (P 3) (P 1) (P 2) then 1 - 2 / 3 * Real.exp (-t)
          else 1 / 3 * Real.exp (-t)) := by
    intro P t ht
    obtain ⟨m1, m2, m3, m4⟩ := fc_mid (P 0) (P 1) (P 2) (P 3)
    refine ⟨?_, ?_, ?_⟩ <;> simp only [pathCF, pathSep] <;> rw [ht]
    · rw [m1, m2]
    · rw [m3, m4]
  obtain ⟨p0, p1, p2⟩ := hpath (P := pos) ht₁
  obtain ⟨q0, q1, q2⟩ := hpath (P := P') ht₂
  refine regularPattern_of_mixture (S₁ := ![pathSep (pos 0) (pos 1) (pos 2) (pos 3),
      pathSep (pos 0) (pos 2) (pos 1) (pos 3), pathSep (pos 0) (pos 3) (pos 1) (pos 2)])
    (S₂ := ![pathSep (P' 0) (P' 1) (P' 2) (P' 3), pathSep (P' 0) (P' 2) (P' 1) (P' 3),
      pathSep (P' 0) (P' 3) (P' 1) (P' 2)])
    (g₁ := ![pathCF Ω.edgeLen (pos 0) (pos 1) (pos 2) (pos 3),
      pathCF Ω.edgeLen (pos 0) (pos 2) (pos 1) (pos 3),
      pathCF Ω.edgeLen (pos 0) (pos 3) (pos 1) (pos 2)])
    (g₂ := ![pathCF Ω.edgeLen (P' 0) (P' 1) (P' 2) (P' 3),
      pathCF Ω.edgeLen (P' 0) (P' 2) (P' 1) (P' 3),
      pathCF Ω.edgeLen (P' 0) (P' 3) (P' 1) (P' 2)])
    (γ := Ω.γ) (u₁ := Real.exp (-t₁)) (u₂ := Real.exp (-t₂)) hγ0 hγ1 (Real.exp_pos _)
    (Real.exp_lt_one_iff.2 (by linarith)) (Real.exp_pos _) (Real.exp_lt_one_iff.2 (by linarith))
    (fc_sep_unique (hne h01) (hne h02) (hne h03) (hne h12) (hne h13) (hne h23))
    (fc_sep_unique (hne' h01) (hne' h02) (hne' h03) (hne' h12) (hne' h13) (hne' h23))
    (fun i => ?_) (fun i => ?_) (fun i => ?_) (fun i => ?_)
  · fin_cases i
    · exact displays_iff Ω hN.2 hinj hlt hs h01 h23
    · exact displays_iff Ω hN.2 hinj hlt hs h02 h13
    · exact displays_iff Ω hN.2 hinj hlt hs h03 h12
  · fin_cases i
    · exact hcf (i := 0) (j := 1) (k := 2) (l := 3) (by decide)
    · exact hcf (i := 0) (j := 2) (k := 1) (l := 3) (by decide)
    · exact hcf (i := 0) (j := 3) (k := 1) (l := 2) (by decide)
  · fin_cases i
    · show (pathSep (pos 0) (pos 1) (pos 2) (pos 3) →
          pathCF Ω.edgeLen (pos 0) (pos 1) (pos 2) (pos 3) = 1 - 2 / 3 * Real.exp (-t₁)) ∧
        (¬ pathSep (pos 0) (pos 1) (pos 2) (pos 3) →
          pathCF Ω.edgeLen (pos 0) (pos 1) (pos 2) (pos 3) = 1 / 3 * Real.exp (-t₁))
      rw [p0]
      exact ⟨fun h => ite_eq_left h, fun h => ite_eq_right h⟩
    · show (pathSep (pos 0) (pos 2) (pos 1) (pos 3) →
          pathCF Ω.edgeLen (pos 0) (pos 2) (pos 1) (pos 3) = 1 - 2 / 3 * Real.exp (-t₁)) ∧
        (¬ pathSep (pos 0) (pos 2) (pos 1) (pos 3) →
          pathCF Ω.edgeLen (pos 0) (pos 2) (pos 1) (pos 3) = 1 / 3 * Real.exp (-t₁))
      rw [p1]
      exact ⟨fun h => ite_eq_left h, fun h => ite_eq_right h⟩
    · show (pathSep (pos 0) (pos 3) (pos 1) (pos 2) →
          pathCF Ω.edgeLen (pos 0) (pos 3) (pos 1) (pos 2) = 1 - 2 / 3 * Real.exp (-t₁)) ∧
        (¬ pathSep (pos 0) (pos 3) (pos 1) (pos 2) →
          pathCF Ω.edgeLen (pos 0) (pos 3) (pos 1) (pos 2) = 1 / 3 * Real.exp (-t₁))
      rw [p2]
      exact ⟨fun h => ite_eq_left h, fun h => ite_eq_right h⟩
  · fin_cases i
    · show (pathSep (P' 0) (P' 1) (P' 2) (P' 3) →
          pathCF Ω.edgeLen (P' 0) (P' 1) (P' 2) (P' 3) = 1 - 2 / 3 * Real.exp (-t₂)) ∧
        (¬ pathSep (P' 0) (P' 1) (P' 2) (P' 3) →
          pathCF Ω.edgeLen (P' 0) (P' 1) (P' 2) (P' 3) = 1 / 3 * Real.exp (-t₂))
      rw [q0]
      exact ⟨fun h => ite_eq_left h, fun h => ite_eq_right h⟩
    · show (pathSep (P' 0) (P' 2) (P' 1) (P' 3) →
          pathCF Ω.edgeLen (P' 0) (P' 2) (P' 1) (P' 3) = 1 - 2 / 3 * Real.exp (-t₂)) ∧
        (¬ pathSep (P' 0) (P' 2) (P' 1) (P' 3) →
          pathCF Ω.edgeLen (P' 0) (P' 2) (P' 1) (P' 3) = 1 / 3 * Real.exp (-t₂))
      rw [q1]
      exact ⟨fun h => ite_eq_left h, fun h => ite_eq_right h⟩
    · show (pathSep (P' 0) (P' 3) (P' 1) (P' 2) →
          pathCF Ω.edgeLen (P' 0) (P' 3) (P' 1) (P' 2) = 1 - 2 / 3 * Real.exp (-t₂)) ∧
        (¬ pathSep (P' 0) (P' 3) (P' 1) (P' 2) →
          pathCF Ω.edgeLen (P' 0) (P' 3) (P' 1) (P' 2) = 1 / 3 * Real.exp (-t₂))
      rw [q2]
      exact ⟨fun h => ite_eq_left h, fun h => ite_eq_right h⟩

end Brooqs
