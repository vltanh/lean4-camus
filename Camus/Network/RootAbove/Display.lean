module

public import Camus.Network.RootAbove.Splits

/-!
# Displayed quartets with an outgroup and in canonical networks

Two facts on displayed quartets (Definition 1), used to compare a network built on `T` in the
sense of Definition 1 with a network built on `T` with the root kept.

* The outgroup does not change the displayed quartets on the taxa of `N`
  (`RootedNetwork.withOutgroup_displays_iff`). The switchings of `N⁺` are those of `N` with the
  two edges out of the new root. The new vertices hang off the root of `N`, so deleting an edge
  of a switching of `N` separates the leaves of `N` in the same way in `N⁺`
  (`RootedNetwork.withOutgroup_reachable_iff`), and deleting a new edge separates no two leaves
  of `N`.
* The quartets displayed by the canonical network of a cycle-separated family `E`: those induced
  by `T`, and those cut by a clade of the tree displayed through one added edge
  (`Realization.displays_iff_cuts`). This is Lemma 1 (`lemma1`) with the quartets displayed by
  `T + e` (`Realization.single_displays_iff`).

## Main results

* `RootedNetwork.withOutgroup_displays_iff`: `N⁺` and `N` display the same quartets avoiding `z`.
* `RootedNetwork.withOutgroup_reachable_iff`: the outgroup does not connect vertices of `N`.
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

/-- In the switching `S` of `N` with the two edges out of the new root, two vertices of `N` are
connected after deleting a set `B` of edges if and only if they are connected in `S` after deleting
`B`: the new vertices hang off the root of `N`. Collapsing them onto the root of `N` maps a walk
in the first graph to a walk in the second. -/
theorem withOutgroup_reachable_iff (hN : N.RootedBinaryLevelOne) (hρ : ρ ∉ N.vertices)
    (hℓ : ℓ ∉ N.vertices) {S : Finset (ℕ × ℕ)} (hS : S ⊆ N.edges) (B : Set (Sym2 ℕ))
    {u v : ℕ} (hu : u ∈ N.vertices) (hv : v ∈ N.vertices) :
    (({N.withOutgroup z ρ ℓ with edges := insert (ρ, N.root) (insert (ρ, ℓ) S)} :
        RootedNetwork).underlying.deleteEdges B).Reachable u v ↔
      (({N with edges := S} : RootedNetwork).underlying.deleteEdges B).Reachable u v := by
  classical
  constructor
  · intro h
    rw [SimpleGraph.reachable_iff_reflTransGen] at h ⊢
    -- collapse the new vertices onto the root of `N`
    let f : ℕ → ℕ := fun x => if x = ρ ∨ x = ℓ then N.root else x
    have hf : ∀ x ∈ N.vertices, f x = x := by
      intro x hx
      refine ite_eq_right ?_
      rintro (rfl | rfl)
      · exact hρ hx
      · exact hℓ hx
    have hfρ : f ρ = N.root := ite_eq_left (Or.inl rfl)
    have hfℓ : f ℓ = N.root := ite_eq_left (Or.inr rfl)
    -- an edge of `S` joins two vertices of `N`; a new edge is collapsed to the root of `N`
    have hedge : ∀ a b, (a, b) ∈ insert (ρ, N.root) (insert (ρ, ℓ) S) →
        f a = f b ∨ ((a, b) ∈ S ∧ f a = a ∧ f b = b) := by
      intro a b hab
      rcases Finset.mem_insert.mp hab with h | h
      · simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact Or.inl (hfρ.trans (hf _ hN.1).symm)
      rcases Finset.mem_insert.mp h with h | h
      · simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact Or.inl (hfρ.trans hfℓ.symm)
      · exact Or.inr ⟨h, hf a (hN.2.1 _ (hS h)).1, hf b (hN.2.1 _ (hS h)).2⟩
    have hstep : ∀ a b,
        (({N.withOutgroup z ρ ℓ with edges := insert (ρ, N.root) (insert (ρ, ℓ) S)} :
          RootedNetwork).underlying.deleteEdges B).Adj a b →
        Relation.ReflTransGen
          (({N with edges := S} : RootedNetwork).underlying.deleteEdges B).Adj (f a) (f b) := by
      intro a b hab
      rw [SimpleGraph.deleteEdges_adj] at hab
      obtain ⟨⟨hne, hab⟩, hB⟩ := hab
      rcases hab with h | h
      · rcases hedge a b h with h' | ⟨h', ha, hb⟩
        · rw [h']
        · rw [ha, hb]
          exact Relation.ReflTransGen.single
            (SimpleGraph.deleteEdges_adj.mpr ⟨⟨hne, Or.inl h'⟩, hB⟩)
      · rcases hedge b a h with h' | ⟨h', hb, ha⟩
        · rw [h']
        · rw [ha, hb]
          exact Relation.ReflTransGen.single
            (SimpleGraph.deleteEdges_adj.mpr ⟨⟨hne, Or.inr h'⟩, hB⟩)
    have hlift := Relation.ReflTransGen.lift' f hstep u v h
    rwa [Function.onFun, hf u hu, hf v hv] at hlift
  · apply SimpleGraph.Reachable.mono
    apply SimpleGraph.deleteEdges_mono
    intro a b hab
    exact ⟨hab.1, hab.2.imp (fun h => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
      (fun h => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))⟩

/-- Adding an outgroup does not change the displayed quartets avoiding the new taxon `z`: `N⁺` and
`N` display the same such quartets. A switching of `N⁺` is a switching `S` of `N` with the two
edges out of the new root (`RootedNetwork.withOutgroup_switching_cases`). Deleting an edge of `S`
separates the leaves of `N` in the same way in both switchings, since the new vertices hang off the
root of `N` (`RootedNetwork.withOutgroup_reachable_iff`); deleting a new edge leaves `S`, which
connects all the vertices of `N`, and separates no quartet on the taxa of `N`. -/
theorem withOutgroup_displays_iff (hN : N.RootedBinaryLevelOne) (hρ : ρ ∉ N.vertices)
    (hℓ : ℓ ∉ N.vertices) (hρℓ : ρ ≠ ℓ) {q : Quartet} (hqz : z ∉ q.taxa) :
    (N.withOutgroup z ρ ℓ).DisplaysQuartet q ↔ N.DisplaysQuartet q := by
  classical
  have htaxa : q.taxa ⊆ (N.withOutgroup z ρ ℓ).taxa ↔ q.taxa ⊆ N.taxa := by
    change q.taxa ⊆ insert z N.taxa ↔ _
    constructor
    · intro h x hx
      exact (Finset.mem_insert.mp (h hx)).resolve_left (fun hxz => hqz (hxz ▸ hx))
    · intro h
      exact h.trans (Finset.subset_insert _ _)
  -- the taxa of `q` label the same leaves in `N⁺` and in `N`
  have hleaf : ∀ a ∈ q.taxa, (N.withOutgroup z ρ ℓ).leaf a = N.leaf a :=
    fun a ha => ite_eq_right (fun h : a = z => hqz (h ▸ ha))
  have h1 : ∀ a ∈ q.sides.1, (N.withOutgroup z ρ ℓ).leaf a = N.leaf a :=
    fun a ha => hleaf a (q.sides_subset_taxa.1 ha)
  have h2 : ∀ a ∈ q.sides.2, (N.withOutgroup z ρ ℓ).leaf a = N.leaf a :=
    fun a ha => hleaf a (q.sides_subset_taxa.2 ha)
  -- separating the two sides of `q` in a switching of `N` and in the switching of `N⁺` above it
  have hsep : ∀ (S : Finset (ℕ × ℕ)), N.Switching S → q.taxa ⊆ N.taxa →
      ∀ e : Sym2 ℕ,
        ((N.withOutgroup z ρ ℓ).Separates
          (({N.withOutgroup z ρ ℓ with edges := insert (ρ, N.root) (insert (ρ, ℓ) S)} :
            RootedNetwork).underlying.deleteEdges {e}) q ↔
        N.Separates (({N with edges := S} : RootedNetwork).underlying.deleteEdges {e}) q) := by
    intro S hS hqN e
    have hmem : ∀ a ∈ q.taxa, N.leaf a ∈ N.vertices :=
      fun a ha => (hN.2.2.2.2.2.2.2.1 a (hqN ha)).1
    have hR : ∀ a ∈ q.taxa, ∀ b ∈ q.taxa, _ :=
      fun a ha b hb => withOutgroup_reachable_iff (z := z) hN hρ hℓ hS.1 {e} (hmem a ha) (hmem b hb)
    have s1 := q.sides_subset_taxa.1
    have s2 := q.sides_subset_taxa.2
    constructor
    · rintro ⟨hA, hB, hAB⟩
      refine ⟨fun a ha b hb => ?_, fun a ha b hb => ?_, fun a ha b hb hab => ?_⟩
      · have := hA a ha b hb
        rw [h1 a ha, h1 b hb] at this
        exact (hR a (s1 ha) b (s1 hb)).mp this
      · have := hB a ha b hb
        rw [h2 a ha, h2 b hb] at this
        exact (hR a (s2 ha) b (s2 hb)).mp this
      · apply hAB a ha b hb
        rw [h1 a ha, h2 b hb]
        exact (hR a (s1 ha) b (s2 hb)).mpr hab
    · rintro ⟨hA, hB, hAB⟩
      refine ⟨fun a ha b hb => ?_, fun a ha b hb => ?_, fun a ha b hb hab => ?_⟩
      · rw [h1 a ha, h1 b hb]
        exact (hR a (s1 ha) b (s1 hb)).mpr (hA a ha b hb)
      · rw [h2 a ha, h2 b hb]
        exact (hR a (s2 ha) b (s2 hb)).mpr (hB a ha b hb)
      · rw [h1 a ha, h2 b hb] at hab
        exact hAB a ha b hb ((hR a (s1 ha) b (s2 hb)).mp hab)
  -- the undirected graph of `S` lies in that of the switching of `N⁺` above it
  have hle : ∀ (S : Finset (ℕ × ℕ)), ({N with edges := S} : RootedNetwork).underlying ≤
      ({N.withOutgroup z ρ ℓ with edges := insert (ρ, N.root) (insert (ρ, ℓ) S)} :
        RootedNetwork).underlying := by
    intro S a b hab
    exact ⟨hab.1, hab.2.imp (fun h => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
      (fun h => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))⟩
  constructor
  · rintro ⟨hqt, S', hS', e, he, hsepP⟩
    have hqN := htaxa.mp hqt
    obtain ⟨S, hS, rfl⟩ := withOutgroup_switching_cases hN hρ hℓ hρℓ hS'
    by_cases heS : e ∈ ({N with edges := S} : RootedNetwork).underlying.edgeSet
    -- an edge of `S`
    · exact ⟨hqN, S, hS, e, heS, (hsep S hS hqN e).mp hsepP⟩
    -- a new edge: `S` still connects the leaves of `N`
    · exfalso
      obtain ⟨_, _, hAB⟩ := hsepP
      obtain ⟨a, ha⟩ := q.sides_nonempty.1
      obtain ⟨b, hb⟩ := q.sides_nonempty.2
      apply hAB a ha b hb
      rw [h1 a ha, h2 b hb]
      have hconn := switching_connected_vertices hN hS
        (hN.2.2.2.2.2.2.2.1 a (hqN (q.sides_subset_taxa.1 ha))).1
        (hN.2.2.2.2.2.2.2.1 b (hqN (q.sides_subset_taxa.2 hb))).1
      apply hconn.mono
      intro x y hxy
      refine SimpleGraph.deleteEdges_adj.mpr ⟨hle S hxy, fun hx => heS ?_⟩
      rw [Set.mem_singleton_iff] at hx
      rw [← hx]
      exact hxy
  · rintro ⟨hqN, S, hS, e, he, hsepN⟩
    exact ⟨htaxa.mpr hqN, _, withOutgroup_switching hN hρ hℓ hS, e,
      SimpleGraph.edgeSet_mono (hle S) he, (hsep S hS hqN e).mpr hsepN⟩

end RootedNetwork

end Camus
