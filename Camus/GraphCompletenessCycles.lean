module

public import Camus.GraphCompletenessTree

@[expose] public section

namespace Camus.RootedNetwork

noncomputable def supportPath {N : RootedNetwork} (hN : N.RootedBinaryLevelOne)
    {S : Finset (ℕ × ℕ)} (hS : N.Switching S) {e : ℕ × ℕ}
    (he : e ∈ N.edges \ S) : ({N with edges := S}).underlying.Path e.2 e.1 :=
  ⟨Classical.choose (switching_existsUnique_path hN hS
      (hN.2.1 e (Finset.mem_sdiff.mp he).1).2
      (hN.2.1 e (Finset.mem_sdiff.mp he).1).1),
    (Classical.choose_spec (switching_existsUnique_path hN hS
      (hN.2.1 e (Finset.mem_sdiff.mp he).1).2
      (hN.2.1 e (Finset.mem_sdiff.mp he).1).1)).1⟩

/-- Add the one deleted edge to the unique path in the support switching. -/
noncomputable def fundamentalCycle {N : RootedNetwork} (hN : N.RootedBinaryLevelOne)
    {S : Finset (ℕ × ℕ)} (hS : N.Switching S) {e : ℕ × ℕ}
    (he : e ∈ N.edges \ S) : N.underlying.Walk e.1 e.1 :=
  .cons ⟨edge_ne hN (Finset.mem_sdiff.mp he).1,
      Or.inl (Finset.mem_sdiff.mp he).1⟩
    ((supportPath hN hS he).val.mapLe (switching_underlying_le hS))

theorem fundamentalCycle_isCycle {N : RootedNetwork} (hN : N.RootedBinaryLevelOne)
    {S : Finset (ℕ × ℕ)} (hS : N.Switching S) {e : ℕ × ℕ}
    (he : e ∈ N.edges \ S) : (fundamentalCycle hN hS he).IsCycle := by
  classical
  apply SimpleGraph.Walk.cons_isCycle_iff _ _ |>.mpr
  refine ⟨(supportPath hN hS he).isPath.mapLe _, ?_⟩
  rw [SimpleGraph.Walk.edges_mapLe_eq_edges]
  intro hmem
  exact deleted_edge_not_switching_edgeSet hN hS he
    ((supportPath hN hS he).val.edges_subset_edgeSet hmem)

theorem fundamentalCycle_mem_edges {N : RootedNetwork} (hN : N.RootedBinaryLevelOne)
    {S : Finset (ℕ × ℕ)} (hS : N.Switching S) {e : ℕ × ℕ}
    (he : e ∈ N.edges \ S) : s(e.1,e.2) ∈ (fundamentalCycle hN hS he).edges := by
  change s(e.1,e.2) ∈ s(e.1,e.2) :: _
  exact List.mem_cons_self

theorem directed_edge_eq_of_sym2_eq {N : RootedNetwork} (hN : N.RootedBinaryLevelOne)
    {e f : ℕ × ℕ} (he : e ∈ N.edges) (hf : f ∈ N.edges)
    (h : s(e.1,e.2) = s(f.1,f.2)) : e = f := by
  rcases Sym2.eq_iff.mp h with h | h
  · exact Prod.ext h.1 h.2
  · exact False.elim (edge_reverse_not_mem hN he (by simpa [h.1,h.2] using hf))

/-- The only deleted edge on a fundamental cycle is its defining edge. -/
theorem fundamentalCycle_deleted_edge_unique {N : RootedNetwork}
    (hN : N.RootedBinaryLevelOne) {S : Finset (ℕ × ℕ)} (hS : N.Switching S)
    {e f : ℕ × ℕ} (he : e ∈ N.edges \ S) (hf : f ∈ N.edges \ S)
    (hmem : s(f.1,f.2) ∈ (fundamentalCycle hN hS he).edges) : f = e := by
  change s(f.1,f.2) ∈ s(e.1,e.2) ::
    ((supportPath hN hS he).val.mapLe (switching_underlying_le hS)).edges at hmem
  rw [SimpleGraph.Walk.edges_mapLe_eq_edges, List.mem_cons] at hmem
  rcases hmem with h | h
  · exact directed_edge_eq_of_sym2_eq hN (Finset.mem_sdiff.mp hf).1
      (Finset.mem_sdiff.mp he).1 h
  · exact False.elim (deleted_edge_not_switching_edgeSet hN hS hf
      ((supportPath hN hS he).val.edges_subset_edgeSet h))

theorem fundamentalCycles_disjoint {N : RootedNetwork} (hN : N.RootedBinaryLevelOne)
    {S : Finset (ℕ × ℕ)} (hS : N.Switching S) {e f : ℕ × ℕ}
    (he : e ∈ N.edges \ S) (hf : f ∈ N.edges \ S) (hef : e ≠ f) :
    Disjoint (fundamentalCycle hN hS he).support.toFinset
      (fundamentalCycle hN hS hf).support.toFinset := by
  apply hN.2.2.2.2.2.2.2.2.2.2 _ _ _ _
    (fundamentalCycle_isCycle hN hS he) (fundamentalCycle_isCycle hN hS hf)
  intro heq
  have hm : s(e.1,e.2) ∈ (fundamentalCycle hN hS hf).edges := by
    apply List.mem_toFinset.mp
    rw [← heq]
    exact List.mem_toFinset.mpr (fundamentalCycle_mem_edges hN hS he)
  exact hef (fundamentalCycle_deleted_edge_unique hN hS hf he hm)

theorem fundamentalCycle_source_mem {N : RootedNetwork} (hN : N.RootedBinaryLevelOne)
    {S : Finset (ℕ × ℕ)} (hS : N.Switching S) {e : ℕ × ℕ}
    (he : e ∈ N.edges \ S) : e.1 ∈ (fundamentalCycle hN hS he).support :=
  (fundamentalCycle hN hS he).start_mem_support

theorem fundamentalCycle_target_mem {N : RootedNetwork} (hN : N.RootedBinaryLevelOne)
    {S : Finset (ℕ × ℕ)} (hS : N.Switching S) {e : ℕ × ℕ}
    (he : e ∈ N.edges \ S) : e.2 ∈ (fundamentalCycle hN hS he).support := by
  change e.2 ∈ e.1 :: ((supportPath hN hS he).val.mapLe _).support
  exact List.mem_cons_of_mem _ ((supportPath hN hS he).val.mapLe _).start_mem_support

theorem deleted_sources_injective {N : RootedNetwork} (hN : N.RootedBinaryLevelOne)
    {S : Finset (ℕ × ℕ)} (hS : N.Switching S) :
    Set.InjOn (fun e : ℕ × ℕ => e.1) (N.edges \ S : Finset (ℕ × ℕ)) := by
  intro e he f hf heq
  dsimp only at heq
  by_contra hef
  have hd := fundamentalCycles_disjoint hN hS he hf hef
  exact Finset.disjoint_left.mp hd
    (List.mem_toFinset.mpr (fundamentalCycle_source_mem hN hS he))
    (by rw [heq]; exact List.mem_toFinset.mpr (fundamentalCycle_source_mem hN hS hf))

theorem deleted_targets_injective {N : RootedNetwork} (hN : N.RootedBinaryLevelOne)
    {S : Finset (ℕ × ℕ)} (hS : N.Switching S) :
    Set.InjOn (fun e : ℕ × ℕ => e.2) (N.edges \ S : Finset (ℕ × ℕ)) := by
  intro e he f hf heq
  dsimp only at heq
  by_contra hef
  have hd := fundamentalCycles_disjoint hN hS he hf hef
  exact Finset.disjoint_left.mp hd
    (List.mem_toFinset.mpr (fundamentalCycle_target_mem hN hS he))
    (by rw [heq]; exact List.mem_toFinset.mpr (fundamentalCycle_target_mem hN hS hf))

/-- Both cycle edges incident to the reticulation recipient point into it. -/
theorem fundamentalCycle_recipient_edge_incoming {N : RootedNetwork}
    (hN : N.RootedBinaryLevelOne) {S : Finset (ℕ × ℕ)} (hS : N.Switching S)
    {e : ℕ × ℕ} (he : e ∈ N.edges \ S) {f : Sym2 ℕ}
    (hf : f ∈ (fundamentalCycle hN hS he).edges) (hr : e.2 ∈ f) :
    ∃ a, (a,e.2) ∈ N.edges ∧ f = s(a,e.2) := by
  classical
  change f ∈ s(e.1,e.2) ::
    ((supportPath hN hS he).val.mapLe (switching_underlying_le hS)).edges at hf
  rw [SimpleGraph.Walk.edges_mapLe_eq_edges, List.mem_cons] at hf
  rcases hf with hf | hf
  · exact ⟨e.1,(Finset.mem_sdiff.mp he).1,hf⟩
  · obtain ⟨a, hfa⟩ := Sym2.mem_iff_exists.mp hr
    rw [hfa] at hf
    have ha := (supportPath hN hS he).isPath.eq_snd_of_mem_edges hf
    have hin := switching_path_first_incoming hN hS
      (supportPath hN hS he).val (supportPath hN hS he).isPath
      (Finset.mem_sdiff.mp he).1
    refine ⟨a, ?_, ?_⟩
    · rw [ha]
      exact hS.1 hin
    · exact hfa.trans Sym2.eq_swap

end Camus.RootedNetwork
