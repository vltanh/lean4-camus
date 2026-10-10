module

public import Camus.Network.RootAbove.Splits

/-!
# Displayed quartets with an outgroup and in canonical networks

Two facts on displayed quartets (Definition 1), used to compare a network built on `T` in the
sense of Definition 1 with a network built on `T` with the root kept.

* The outgroup does not change the displayed quartets on the taxa of `N`
  (`RootedNetwork.withOutgroup_displays_iff`). The switchings of `N⁺` are those of `N` with the
  two edges out of the new root, and an edge of a switching of `N` has the same clade below it in
  `N⁺`; the two new edges have the clades `N.taxa` and `{z}` below them, which cut no quartet on
  the taxa of `N`. The proof reads Definition 1 by clades of switchings
  (`RootedNetwork.displays_iff_cladeBelow`).
* The quartets displayed by the canonical network of a cycle-separated family `E`: those induced
  by `T`, and those cut by a clade of the tree displayed through one added edge
  (`Realization.displays_iff_cuts`). This is Lemma 1 (`lemma1`) with the quartets displayed by
  `T + e` (`Realization.single_displays_iff`).

## Main results

* `RootedNetwork.withOutgroup_displays_iff`: `N⁺` and `N` display the same quartets avoiding `z`.
* `Realization.displays_iff_cuts`: the quartets displayed by `Realization.graph t E`.
* `Quartet.induced_outgroup`: `T⁺` and `T` induce the same quartets on the taxa of `T`.
-/

@[expose] public section

namespace Camus

namespace Quartet

/-- `T⁺ = fork (leaf z) T` and `T` induce the same quartets on the taxa of `T`: the two extra
clades of `T⁺`, its whole set of taxa and `{z}`, cut no such quartet. -/
theorem induced_outgroup {t : PhyloTree} {z : ℕ} (hz : z ∉ t.taxa) {q : Quartet}
    (hq : q.taxa ⊆ t.taxa) : q.induced (PhyloTree.fork (.leaf z) t) = q.induced t := by
  have hqz : Disjoint q.taxa {z} := Finset.disjoint_singleton_right.mpr (fun h => hz (hq h))
  have hsup : q.taxa ⊆ (PhyloTree.fork (.leaf z) t).taxa := by
    rw [PhyloTree.outgroup_taxa]
    exact hq.trans (Finset.subset_insert _ _)
  have hsup' : q.taxa ⊆ (PhyloTree.leaf z).taxa ∪ t.taxa := hq.trans Finset.subset_union_right
  simp only [induced, PhyloTree.clades, List.any_cons, List.any_append, List.any_nil,
    decide_eq_true hsup, decide_eq_true hq, Bool.true_and, q.cutBy_eq_false_of_superset hsup',
    q.cutBy_eq_false_of_disjoint hqz, Bool.false_or]

end Quartet

namespace Realization

/-- The quartets displayed by the canonical network of a cycle-separated family `E` of pairs of a
well-labelled tree `T`: the quartets on taxa of `T` that `T` induces or that a clade of the tree
displayed through one added edge cuts. By Lemma 1 (`lemma1`), a displayed quartet that `T` does
not induce is displayed by `T + e` for an added edge `e`, and `Realization.single_displays_iff`
gives the quartets displayed by `T + e`; conversely, `T + e` and `T` are subnetworks of the
canonical network (`Realization.single_displays_full`, `DynamicProgramming.baseline_subset`). -/
theorem displays_iff_cuts {t : PhyloTree} (ht : t.WellLabelled) {E : Finset Pair}
    (hE : EdgeAbove.CycleSeparated t E) (q : Quartet) :
    (graph t E).DisplaysQuartet q ↔ q.taxa ⊆ t.taxa ∧
      (q.induced t = true ∨
        ∃ e ∈ E, ∃ C ∈ EdgeAbove.switchedClades t e, q.cutBy C = true) := by
  classical
  constructor
  · intro hq
    refine ⟨hq.1, ?_⟩
    by_cases hind : q.induced t = true
    · exact Or.inl hind
    · right
      -- by Lemma 1, some `T + e` displays `q`
      obtain ⟨d, ⟨hd, hdq⟩, _⟩ := lemma1 t ht (graph t E) (levelOne t ht E hE)
        (supportEdges t E) (support t ht E hE) q hq hind
      have hmem : (support t ht E hE).pairOf d ∈ E := by
        have h : (support t ht E hE).pairOf d ∈ (support t ht E hE).extracted :=
          Finset.mem_image.mpr ⟨d, hd, rfl⟩
        rwa [extracted_eq t ht E hE] at h
      obtain ⟨_, hcut⟩ := (single_displays_iff ht (hE.1 hmem) q).mp hdq
      exact ⟨_, hmem, hcut.resolve_left hind⟩
  · rintro ⟨htaxa, hind | ⟨e, he, hcut⟩⟩
    -- a quartet of `T` is displayed by every canonical network
    · have hbase : (graph t ∅).DisplaysQuartet q := (baseline_displays_iff t ht q).mpr hind
      have hrep : q ∈ DynamicProgramming.repertoire {q} (graph t ∅) := by
        simp only [DynamicProgramming.repertoire, Finset.mem_filter]
        exact ⟨by simp, hbase⟩
      have hsub := DynamicProgramming.baseline_subset t ht {q} E hE hrep
      simp only [DynamicProgramming.repertoire, Finset.mem_filter] at hsub
      exact hsub.2
    -- a quartet displayed by `T + e` is displayed by the canonical network
    · have hsingle := (single_displays_iff ht (hE.1 he) q).mpr ⟨htaxa, Or.inr hcut⟩
      exact single_displays_full t ht E hE he q hsingle

end Realization

namespace RootedNetwork

variable {N : RootedNetwork} {z ρ ℓ : ℕ}

/-- The clade below `y` in `S`: the taxa whose leaves `S` reaches from `y`. -/
theorem mem_cladeBelow {S : Finset (ℕ × ℕ)} {y a : ℕ} :
    a ∈ N.cladeBelow S y ↔
      a ∈ N.taxa ∧ Relation.ReflTransGen (fun u v => (u, v) ∈ S) y (N.leaf a) := by
  classical
  unfold cladeBelow
  exact Finset.mem_filter

/-- The clade below a vertex `y` of `N` in the switching `S` of `N` with the two edges out of the
new root is the clade below `y` in `S`: no directed path from `y` reaches the new vertices. -/
theorem withOutgroup_cladeBelow (hN : N.RootedBinaryLevelOne) (hρ : ρ ∉ N.vertices)
    (hℓ : ℓ ∉ N.vertices) (hz : z ∉ N.taxa) {S : Finset (ℕ × ℕ)} (hS : S ⊆ N.edges) {y : ℕ}
    (hy : y ∈ N.vertices) :
    (N.withOutgroup z ρ ℓ).cladeBelow (insert (ρ, N.root) (insert (ρ, ℓ) S)) y =
      N.cladeBelow S y := by
  ext a
  rw [mem_cladeBelow, mem_cladeBelow]
  change a ∈ insert z N.taxa ∧ Relation.ReflTransGen
      (fun u v => (u, v) ∈ insert (ρ, N.root) (insert (ρ, ℓ) S)) y
      (if a = z then ℓ else N.leaf a) ↔ _
  rw [Finset.mem_insert]
  constructor
  · rintro ⟨ha, hr⟩
    by_cases haz : a = z
    · rw [ite_eq_left haz] at hr
      have hr' := withOutgroup_reach hN hρ hS hy hr
      rcases Relation.ReflTransGen.cases_tail hr' with h | ⟨b, _, hb⟩
      · exact absurd (h ▸ hy) hℓ
      · exact absurd (hN.2.1 _ (hS hb)).2 hℓ
    · rw [ite_eq_right haz] at hr
      exact ⟨ha.resolve_left haz, withOutgroup_reach hN hρ hS hy hr⟩
  · rintro ⟨ha, hr⟩
    have haz : a ≠ z := fun h => hz (h ▸ ha)
    refine ⟨Or.inr ha, ?_⟩
    rw [ite_eq_right haz]
    exact Relation.ReflTransGen.mono (fun _ _ h =>
      Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h)) _ _ hr

/-- Adding an outgroup does not change the displayed quartets avoiding the new taxon `z`: `N⁺` and
`N` display the same such quartets. A switching of `N⁺` is a switching of `N` with the two edges
out of the new root (`RootedNetwork.withOutgroup_switching_cases`); the edges of `N` have the same
clades below them, and the two new edges have the clades `N.taxa` and `{z}`, which cut no quartet
on the taxa of `N`. -/
theorem withOutgroup_displays_iff (hN : N.RootedBinaryLevelOne) (hρ : ρ ∉ N.vertices)
    (hℓ : ℓ ∉ N.vertices) (hρℓ : ρ ≠ ℓ) (hz : z ∉ N.taxa) {q : Quartet} (hqz : z ∉ q.taxa) :
    (N.withOutgroup z ρ ℓ).DisplaysQuartet q ↔ N.DisplaysQuartet q := by
  classical
  have hP := withOutgroup_levelOne hN hρ hℓ hρℓ hz
  rw [displays_iff_cladeBelow hP, displays_iff_cladeBelow hN]
  have htaxa : q.taxa ⊆ (N.withOutgroup z ρ ℓ).taxa ↔ q.taxa ⊆ N.taxa := by
    change q.taxa ⊆ insert z N.taxa ↔ _
    constructor
    · intro h x hx
      exact (Finset.mem_insert.mp (h hx)).resolve_left (fun hxz => hqz (hxz ▸ hx))
    · intro h
      exact h.trans (Finset.subset_insert _ _)
  rw [htaxa]
  apply and_congr_right
  intro hqN
  constructor
  · rintro ⟨S', hS', x, y, hxy, hcut⟩
    obtain ⟨S, hS, rfl⟩ := withOutgroup_switching_cases hN hρ hℓ hρℓ hS'
    rcases Finset.mem_insert.mp hxy with h | h
    -- the edge into the root of `N`: all taxa of `N` lie below it
    · exfalso
      have hy : y = N.root := (Prod.ext_iff.mp h).2
      subst hy
      rw [withOutgroup_cladeBelow hN hρ hℓ hz hS.1 hN.1] at hcut
      have hall : q.taxa ⊆ N.cladeBelow S N.root := by
        intro a ha
        have haN := hqN ha
        exact mem_cladeBelow.mpr ⟨haN, switching_reachable hN hS (hN.2.2.2.2.2.2.2.1 a haN).1⟩
      rw [q.cutBy_eq_false_of_superset hall] at hcut
      exact absurd hcut (by simp)
    rcases Finset.mem_insert.mp h with h | h
    -- the edge into the new leaf: only `z` lies below it
    · exfalso
      have hy : y = ℓ := (Prod.ext_iff.mp h).2
      subst hy
      have hsub : (N.withOutgroup z ρ y).cladeBelow
          (insert (ρ, N.root) (insert (ρ, y) S)) y ⊆ {z} := by
        intro a ha
        obtain ⟨ha, hr⟩ := mem_cladeBelow.mp ha
        change a ∈ insert z N.taxa at ha
        change Relation.ReflTransGen _ y (if a = z then y else N.leaf a) at hr
        rcases Relation.ReflTransGen.cases_head hr with h | ⟨c, hc, _⟩
        · by_cases haz : a = z
          · exact Finset.mem_singleton.mpr haz
          · rw [ite_eq_right haz] at h
            have haN : a ∈ N.taxa := (Finset.mem_insert.mp ha).resolve_left haz
            exact absurd (h ▸ (hN.2.2.2.2.2.2.2.1 a haN).1) hℓ
        · rcases Finset.mem_insert.mp hc with h' | h'
          · exact absurd (Prod.ext_iff.mp h').1 hρℓ.symm
          rcases Finset.mem_insert.mp h' with h' | h'
          · exact absurd (Prod.ext_iff.mp h').1 hρℓ.symm
          · exact absurd (hN.2.1 _ (hS.1 h')).1 hℓ
      have hdis : Disjoint q.taxa ((N.withOutgroup z ρ y).cladeBelow
          (insert (ρ, N.root) (insert (ρ, y) S)) y) :=
        Finset.disjoint_of_subset_right hsub (Finset.disjoint_singleton_right.mpr hqz)
      rw [q.cutBy_eq_false_of_disjoint hdis] at hcut
      exact absurd hcut (by simp)
    -- an edge of `S`
    · refine ⟨S, hS, x, y, h, ?_⟩
      rwa [withOutgroup_cladeBelow hN hρ hℓ hz hS.1 (hN.2.1 _ (hS.1 h)).2] at hcut
  · rintro ⟨S, hS, x, y, hxy, hcut⟩
    refine ⟨_, withOutgroup_switching hN hρ hℓ hS, x, y,
      Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hxy), ?_⟩
    rwa [withOutgroup_cladeBelow hN hρ hℓ hz hS.1 (hN.2.1 _ (hS.1 hxy)).2]

end RootedNetwork

end Camus
