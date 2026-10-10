module

public import Camus.Network.RootAbove.Display
public import Camus.Network.Reticulations

/-!
# Networks built on `T` with the root above the root of `T`

Definition 1 allows a network `N` built on `T` whose root lies above the root of `T`
(`RootedNetwork.BuiltOn`), while the dynamic program of Section 2.2 ranges over the networks
built on `T` with the root of `T` at the root (`RootedNetwork.AnchoredExtension`): "we cannot add
an edge to T that begins above the root of T". This file shows that nothing is lost: every
network built on a well-labelled `T` in the sense of Definition 1 has the same number of
reticulations and displays the same quartets as some network built on `T` with the root kept
(`RootedNetwork.BuiltOn.exists_anchored`). The edge that begins above the root of `T` is moved to
begin above a child of the root; the tree displayed through it keeps its splits.

## Main results

* `RootedNetwork.BuiltOn.exists_anchored`: the main theorem.

## Proof

1. Add an outgroup: a new taxon `z`, the tree `T⁺ = fork (leaf z) T`, and the network `N⁺`
   (`RootedNetwork.withOutgroup`), a rooted binary level-1 network with the reticulations of `N`
   (`RootedNetwork.withOutgroup_levelOne`, `RootedNetwork.withOutgroup_reticulationCount`) and
   the quartets of `N` (`RootedNetwork.withOutgroup_displays_iff`). It is built on `T⁺` with the
   root kept (`DisplayedSubdivision.toOutgroup`).
2. By the completeness theorem, `N⁺` is isomorphic to the canonical network of its pairs `E⁺`,
   which are cycle-separated in `T⁺` (`SupportSubdivision.canonical_iso`,
   `SupportSubdivision.extracted_separated`). They are pairs `(true :: u, true :: w)`
   (`DisplayedSubdivision.outgroup_extracted_mem`); the pairs `(u, w)` form a family of `T` in
   which a donor `[]` lies above the root of `T` (`EdgeAbove.outgroup_rootSeparated`).
3. Moving the donors below the root gives a cycle-separated family `E'` of `T` with as many pairs
   (`EdgeAbove.RootSeparated.image_lowerPair`, `EdgeAbove.RootSeparated.card_image_lowerPair`).
   Its canonical network `N'` is built on `T` with the root kept and has `|E'| = |E⁺|`
   reticulations, as many as `N⁺` and `N` (`Realization.reticulationCount_eq_card`,
   `RootedNetwork.Iso.reticulationCount_eq`).
4. By Lemma 1 and the quartets displayed by `T + e` (`Realization.displays_iff_cuts`), the
   canonical networks of `E⁺` and `E'` display the quartets induced by `T⁺` and `T`, which agree
   on the taxa of `T` (`Quartet.induced_outgroup`), and the quartets cut by the trees displayed
   through single edges, which agree pair by pair (`EdgeAbove.cuts_outgroup_iff`,
   `EdgeAbove.cuts_lowerPair_iff`).
-/

@[expose] public section

namespace Camus

/-- A tree with an outgroup taxon `z` that is not a taxon of `T` is well-labelled. -/
theorem PhyloTree.outgroup_wellLabelled {t : PhyloTree} (ht : t.WellLabelled) {z : ℕ}
    (hz : z ∉ t.taxa) : (PhyloTree.fork (.leaf z) t).WellLabelled := by
  change ([z] ++ t.labels).Nodup
  exact List.nodup_cons.mpr ⟨fun h => hz (List.mem_toFinset.mpr h), ht⟩

/-- Every network built on a well-labelled tree `T` in the sense of Definition 1, possibly with
its root above the root of `T`, has the same number of reticulations and displays the same
quartets as a network built on `T` with the root of `T` at its root. So the class of networks
over which the dynamic program of Section 2.2 optimizes ("we cannot add an edge to T that begins
above the root of T") loses nothing: the edge that begins above the root of `T` can begin above a
child of the root instead. The network is the canonical network `Realization.graph t E'` of a
cycle-separated family `E'`. -/
theorem RootedNetwork.BuiltOn.exists_anchored {t : PhyloTree} (ht : t.WellLabelled)
    {N : RootedNetwork} (hN : N.BuiltOn t) :
    ∃ N' : RootedNetwork, N'.AnchoredExtension t ∧
      N'.reticulationCount = N.reticulationCount ∧
      ∀ q, N.DisplaysQuartet q ↔ N'.DisplaysQuartet q := by
  classical
  obtain ⟨hbin, S, ⟨H⟩⟩ := hN
  -- 1. An outgroup: a new taxon `z`, a new root `m` and a new leaf `m + 1`.
  obtain ⟨z, hz⟩ := Infinite.exists_notMem_finset t.taxa
  have hzN : z ∉ N.taxa := H.taxa_preserved ▸ hz
  set m := N.vertices.sup id + 1 with hm
  have hfresh : ∀ v, N.vertices.sup id < v → v ∉ N.vertices := by
    intro v hv hvN
    have := Finset.le_sup (f := id) hvN
    simp only [id] at this
    omega
  have hρ : m ∉ N.vertices := hfresh m (by omega)
  have hℓ : m + 1 ∉ N.vertices := hfresh (m + 1) (by omega)
  have hρℓ : m ≠ m + 1 := by omega
  have hP := RootedNetwork.withOutgroup_levelOne hbin hρ hℓ hρℓ hzN
  have ht' := PhyloTree.outgroup_wellLabelled ht hz
  -- 2. `N⁺` is built on `T⁺` with the root kept, and is isomorphic to its canonical network.
  let H' := H.toOutgroup hbin hρ hℓ hρℓ hz
  have hEp := H'.extracted_separated hP
  have hG := Realization.levelOne _ ht' H'.extracted hEp
  obtain ⟨i⟩ := H'.canonical_iso hP
  have hform := fun e (he : e ∈ H'.extracted) =>
    H.outgroup_extracted_mem hbin hρ hℓ hρℓ hz he
  have hF := EdgeAbove.outgroup_rootSeparated hEp hform
  -- 3. Move the donors below the root.
  set F := H'.extracted.image (fun e => (e.1.tail, e.2.tail)) with hFdef
  have hE' := hF.image_lowerPair
  refine ⟨Realization.graph t (F.image EdgeAbove.lowerPair),
    ⟨Realization.levelOne t ht _ hE', _, ⟨Realization.support t ht _ hE'⟩⟩, ?_, ?_⟩
  -- the reticulations: `|E'| = |E⁺|`
  · rw [Realization.reticulationCount_eq_card t _ hE', hF.card_image_lowerPair,
      EdgeAbove.outgroup_card_image hform,
      ← Realization.reticulationCount_eq_card _ H'.extracted hEp, ← i.reticulationCount_eq hP hG,
      RootedNetwork.withOutgroup_reticulationCount hbin hρ hℓ hρℓ]
  -- 4. The displayed quartets.
  · intro q
    -- a pair of `E⁺` and its moved pair cut the same quartets on the taxa of `T`
    have hcuts : q.taxa ⊆ t.taxa → ∀ e ∈ H'.extracted,
        ((∃ C ∈ EdgeAbove.switchedClades (PhyloTree.fork (.leaf z) t) e, q.cutBy C = true) ↔
          ∃ C ∈ EdgeAbove.switchedClades t (EdgeAbove.lowerPair (e.1.tail, e.2.tail)),
            q.cutBy C = true) := by
      intro hqt e he
      obtain ⟨u, _, w, _, rfl⟩ := hform e he
      have hfF : (u, w) ∈ F := Finset.mem_image.mpr ⟨_, he, rfl⟩
      obtain ⟨_, hw, hwu⟩ := hF.1 _ hfF
      rw [EdgeAbove.cuts_outgroup_iff hz hqt u w]
      exact EdgeAbove.cuts_lowerPair_iff ht hw hwu hqt
    have hiff : q.taxa ⊆ t.taxa →
        ((Realization.graph (PhyloTree.fork (.leaf z) t) H'.extracted).DisplaysQuartet q ↔
        (Realization.graph t (F.image EdgeAbove.lowerPair)).DisplaysQuartet q) := by
      intro hqt
      have hqz : z ∉ q.taxa := fun h => hz (hqt h)
      rw [Realization.displays_iff_cuts ht' hEp, Realization.displays_iff_cuts ht hE',
        Quartet.induced_outgroup hz hqt]
      have hsub : q.taxa ⊆ (PhyloTree.fork (.leaf z) t).taxa := by
        rw [PhyloTree.outgroup_taxa]
        exact hqt.trans (Finset.subset_insert _ _)
      simp only [hsub, hqt, true_and]
      apply or_congr_right
      constructor
      · rintro ⟨e, he, hcut⟩
        exact ⟨_, Finset.mem_image.mpr ⟨_, Finset.mem_image.mpr ⟨e, he, rfl⟩, rfl⟩,
          (hcuts hqt e he).mp hcut⟩
      · rintro ⟨e', he', hcut⟩
        obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he'
        obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hf
        exact ⟨e, he, (hcuts hqt e he).mpr hcut⟩
    constructor
    · intro hq
      have hqt : q.taxa ⊆ t.taxa := H.taxa_preserved ▸ hq.1
      have hqz : z ∉ q.taxa := fun h => hz (hqt h)
      have h1 := (RootedNetwork.withOutgroup_displays_iff hbin hρ hℓ hρℓ hzN hqz).mpr hq
      exact (hiff hqt).mp ((i.displays_iff hP hG q).mp h1)
    · intro hq
      have hqt : q.taxa ⊆ t.taxa := hq.1
      have hqz : z ∉ q.taxa := fun h => hz (hqt h)
      have h1 := (i.displays_iff hP hG q).mpr ((hiff hqt).mpr hq)
      exact (RootedNetwork.withOutgroup_displays_iff hbin hρ hℓ hρℓ hzN hqz).mp h1

end Camus
