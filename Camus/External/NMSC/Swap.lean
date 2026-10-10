module

public import Camus.External.NMSC.Pattern

/-!
# The exchange of the two sides of a cycle

The description `Brooqs.Net` of a level-1 network orders the two sides of each cycle: in
`cycle γ S₁ S₂ ℓ N` the side `S₁` ends with the hybrid edge of inheritance probability `γ`, and
the side `S₂` with the one of inheritance probability `1 - γ`. The description
`cycle (1 - γ) S₂ S₁ ℓ N` is the same network, with the same inheritance probability on each hybrid
edge. This file shows that the model does not depend on this order. `Brooqs.Net.SideSwap N N'` says
that `N'` is `N` with the two sides of some of its cycles exchanged (none, some or all), and then
`N` and `N'` have the same leaves up to order, the same taxa, the same distributions of forests and
of gene trees under the network multispecies coalescent (NMSC), the same quartet CFs, the same
displayed trees (CAMUS's Definition 1) and displayed quartets, and the same sets of four taxa in the
anomalous configuration.

## Main results

* `Brooqs.Net.SideSwap`, `Brooqs.Side.SideSwap`: the exchange of the two sides of some cycles.
* `Brooqs.Net.SideSwap.refl`, `Brooqs.Net.SideSwap.symm`: the relation is reflexive and symmetric.
* `Brooqs.Net.SideSwap.perm_leaves`, `Brooqs.Net.SideSwap.taxa_eq`,
  `Brooqs.Net.SideSwap.wellFormed_iff`: the leaves, the taxa and the laws of a metric network.
* `Brooqs.Net.SideSwap.forestDist_eq`, `Brooqs.Net.SideSwap.geneTreeDist_eq`,
  `Brooqs.Net.SideSwap.quartetCF_eq`: the NMSC and the quartet CFs.
* `Brooqs.Net.SideSwap.mem_displayed_iff`, `Brooqs.Net.SideSwap.displays_iff`: the displayed trees
  and the displayed quartets.
* `Brooqs.Net.SideSwap.anomalous_iff`: the anomalous configuration.

## Proof

By induction on the exchange. At an exchanged cycle:
* the NMSC sums over the set `A` of the lineages at the hybrid node that take the hybrid edge of
  `S₁`, the others taking that of `S₂`; the reindexing `A ↦ roots F \ A` of the sum over the
  subsets of the roots `roots F` turns the sum of the cycle into that of the exchanged cycle
  (`Brooqs.cycle_sum_swap`), with the symmetry of the union of independent forests
  (`Brooqs.forestUnion_comm`);
* a displayed tree hangs the hybrid component from the bottom of one of the two sides, and the
  displayed trees that hang it from `S₁` are those of the exchanged cycle that hang it from `S₁`,
  now its second side;
* the cycle has the same network below its hybrid node, the same taxa, and the same networks
  hanging from its two sides together.
-/

@[expose] public noncomputable section

namespace Brooqs

open Finset Matrix

universe u

variable {X : Type u}

mutual
/-- `N.SideSwap N'`: the network `N'` is `N` with the two sides of some of its cycles exchanged.
At a cycle `cycle γ S₁ S₂ ℓ N`, the exchange gives `cycle (1 - γ) S₂ S₁ ℓ N`: the side `S₂`, whose
hybrid edge has inheritance probability `1 - γ`, becomes the first side, and `S₁`, whose hybrid
edge has inheritance probability `γ = 1 - (1 - γ)`, the second. Each cycle is exchanged or not
(`Brooqs.Net.SideSwap.cycle`, `Brooqs.Net.SideSwap.swap`), independently of the others, and the
lengths of the edges are kept. -/
inductive Net.SideSwap : Net X → Net X → Prop
  | leaf (x : X) : Net.SideSwap (.leaf x) (.leaf x)
  | tree {ℓ₁ ℓ₂ : ℝ} {N₁ N₂ N₁' N₂' : Net X} :
      Net.SideSwap N₁ N₁' → Net.SideSwap N₂ N₂' →
      Net.SideSwap (.tree ℓ₁ N₁ ℓ₂ N₂) (.tree ℓ₁ N₁' ℓ₂ N₂')
  | cycle {γ ℓ : ℝ} {S₁ S₂ S₁' S₂' : Side X} {N N' : Net X} :
      Side.SideSwap S₁ S₁' → Side.SideSwap S₂ S₂' → Net.SideSwap N N' →
      Net.SideSwap (.cycle γ S₁ S₂ ℓ N) (.cycle γ S₁' S₂' ℓ N')
  | swap {γ ℓ : ℝ} {S₁ S₂ S₁' S₂' : Side X} {N N' : Net X} :
      Side.SideSwap S₁ S₁' → Side.SideSwap S₂ S₂' → Net.SideSwap N N' →
      Net.SideSwap (.cycle γ S₁ S₂ ℓ N) (.cycle (1 - γ) S₂' S₁' ℓ N')

/-- `S.SideSwap S'`: the side `S'` is `S` with the two sides of some of the cycles of the networks
hanging from its nodes exchanged. -/
inductive Side.SideSwap : Side X → Side X → Prop
  | hyb (ℓ : ℝ) : Side.SideSwap (.hyb ℓ) (.hyb ℓ)
  | node {ℓ b : ℝ} {M M' : Net X} {S S' : Side X} :
      Net.SideSwap M M' → Side.SideSwap S S' → Side.SideSwap (.node ℓ b M S) (.node ℓ b M' S')
end

/-! ### The relation -/

mutual
/-- Every network is related to itself: no cycle is exchanged. -/
theorem Net.SideSwap.refl : ∀ N : Net X, N.SideSwap N
  | .leaf x => .leaf x
  | .tree _ N₁ _ N₂ => .tree (Net.SideSwap.refl N₁) (Net.SideSwap.refl N₂)
  | .cycle _ S₁ S₂ _ N => .cycle (Side.SideSwap.refl S₁) (Side.SideSwap.refl S₂)
      (Net.SideSwap.refl N)

/-- Every side is related to itself. -/
theorem Side.SideSwap.refl : ∀ S : Side X, S.SideSwap S
  | .hyb ℓ => .hyb ℓ
  | .node _ _ M S => .node (Net.SideSwap.refl M) (Side.SideSwap.refl S)
end

/-- The exchange of the two sides of the top cycle of `N`, the other cycles being kept. -/
theorem Net.SideSwap.swap_top (γ : ℝ) (S₁ S₂ : Side X) (ℓ : ℝ) (N : Net X) :
    (Net.cycle γ S₁ S₂ ℓ N).SideSwap (.cycle (1 - γ) S₂ S₁ ℓ N) :=
  .swap (Side.SideSwap.refl S₁) (Side.SideSwap.refl S₂) (Net.SideSwap.refl N)

mutual
/-- The relation is symmetric: exchanging the sides of the same cycles again gives `N` back, since
`1 - (1 - γ) = γ`. -/
theorem Net.SideSwap.symm : ∀ {N N' : Net X}, N.SideSwap N' → N'.SideSwap N
  | _, _, .leaf x => .leaf x
  | _, _, .tree h₁ h₂ => .tree h₁.symm h₂.symm
  | _, _, .cycle h₁ h₂ h => .cycle h₁.symm h₂.symm h.symm
  | _, _, .swap (γ := γ) (ℓ := ℓ) h₁ h₂ h => by
      have h' := Net.SideSwap.swap (γ := 1 - γ) (ℓ := ℓ) h₂.symm h₁.symm h.symm
      rwa [sub_sub_cancel] at h'

/-- The relation on sides is symmetric. -/
theorem Side.SideSwap.symm : ∀ {S S' : Side X}, S.SideSwap S' → S'.SideSwap S
  | _, _, .hyb ℓ => .hyb ℓ
  | _, _, .node h₁ h₂ => .node h₁.symm h₂.symm
end

/-! ### Leaves, taxa and the laws of a metric network -/

mutual
/-- The leaves of `N` and of `N'` are the same, up to order. -/
theorem Net.SideSwap.perm_leaves : ∀ {N N' : Net X}, N.SideSwap N' → N.leaves.Perm N'.leaves
  | _, _, .leaf _ => List.Perm.refl _
  | _, _, .tree h₁ h₂ => by
      simp only [Net.leaves]
      exact h₁.perm_leaves.append h₂.perm_leaves
  | _, _, .cycle h₁ h₂ h => by
      simp only [Net.leaves]
      exact (h₁.perm_leaves.append h₂.perm_leaves).append h.perm_leaves
  | _, _, .swap h₁ h₂ h => by
      simp only [Net.leaves]
      exact (List.perm_append_comm.trans (h₂.perm_leaves.append h₁.perm_leaves)).append
        h.perm_leaves

/-- The leaves below two related sides are the same, up to order. -/
theorem Side.SideSwap.perm_leaves : ∀ {S S' : Side X}, S.SideSwap S' → S.leaves.Perm S'.leaves
  | _, _, .hyb _ => List.Perm.refl _
  | _, _, .node h₁ h₂ => by
      simp only [Side.leaves]
      exact h₁.perm_leaves.append h₂.perm_leaves
end

/-- Two related sides have the same number of nodes. -/
theorem Side.SideSwap.length_nodes : ∀ {S S' : Side X}, S.SideSwap S' →
    S'.nodes.length = S.nodes.length
  | _, _, .hyb _ => rfl
  | _, _, .node _ h₂ => by
      simp only [Side.nodes, List.length_cons, h₂.length_nodes]

mutual
/-- The exchange of sides keeps a network metric: the inheritance probability `1 - γ` lies in
`(0, 1)` with `γ`, and the side with a node is still there. -/
theorem Net.SideSwap.isMetric : ∀ {N N' : Net X}, N.SideSwap N' → N.IsMetric → N'.IsMetric
  | _, _, .leaf _, _ => trivial
  | _, _, .tree h₁ h₂, ⟨hℓ₁, hℓ₂, hN₁, hN₂⟩ => ⟨hℓ₁, hℓ₂, h₁.isMetric hN₁, h₂.isMetric hN₂⟩
  | _, _, .cycle h₁ h₂ h, ⟨hγ₀, hγ₁, hℓ, hS₁, hS₂, hN, hne⟩ => by
      refine ⟨hγ₀, hγ₁, hℓ, h₁.isMetric hS₁, h₂.isMetric hS₂, h.isMetric hN, ?_⟩
      simpa only [ne_eq, ← List.length_eq_zero_iff, h₁.length_nodes, h₂.length_nodes] using hne
  | _, _, .swap h₁ h₂ h, ⟨hγ₀, hγ₁, hℓ, hS₁, hS₂, hN, hne⟩ => by
      refine ⟨by linarith, by linarith, hℓ, h₂.isMetric hS₂, h₁.isMetric hS₁, h.isMetric hN, ?_⟩
      simpa only [ne_eq, ← List.length_eq_zero_iff, h₁.length_nodes, h₂.length_nodes,
        or_comm] using hne

/-- The exchange of sides keeps a side metric. -/
theorem Side.SideSwap.isMetric : ∀ {S S' : Side X}, S.SideSwap S' → S.IsMetric → S'.IsMetric
  | _, _, .hyb _, hℓ => hℓ
  | _, _, .node h₁ h₂, ⟨hℓ, hb, hM, hS⟩ => ⟨hℓ, hb, h₁.isMetric hM, h₂.isMetric hS⟩
end

/-- `N` is a metric level-1 network with distinct leaf labels iff `N'` is. -/
theorem Net.SideSwap.wellFormed_iff {N N' : Net X} (h : N.SideSwap N') :
    N.WellFormed ↔ N'.WellFormed :=
  ⟨fun hN => ⟨h.isMetric hN.1, h.perm_leaves.nodup_iff.1 hN.2⟩,
    fun hN' => ⟨h.symm.isMetric hN'.1, h.perm_leaves.nodup_iff.2 hN'.2⟩⟩

mutual
/-- Each subnetwork of `N` is related to a subnetwork of `N'`, the one below the same cut edge. -/
theorem Net.SideSwap.exists_subnets : ∀ {N N' : Net X}, N.SideSwap N' →
    ∀ {M : Net X}, M ∈ N.subnets → ∃ M' ∈ N'.subnets, M.SideSwap M'
  | _, _, .leaf x, _, hM => by
      simp only [Net.subnets, List.mem_singleton] at hM
      subst hM
      exact ⟨.leaf x, List.mem_singleton_self _, .leaf x⟩
  | _, _, .tree h₁ h₂, _, hM => by
      simp only [Net.subnets, List.mem_cons, List.mem_append] at hM
      rcases hM with rfl | hM | hM
      · exact ⟨_, List.mem_cons_self, .tree h₁ h₂⟩
      · obtain ⟨M', hM', hMM'⟩ := h₁.exists_subnets hM
        exact ⟨M', List.mem_cons_of_mem _ (List.mem_append_left _ hM'), hMM'⟩
      · obtain ⟨M', hM', hMM'⟩ := h₂.exists_subnets hM
        exact ⟨M', List.mem_cons_of_mem _ (List.mem_append_right _ hM'), hMM'⟩
  | _, _, .cycle h₁ h₂ h, _, hM => by
      simp only [Net.subnets, List.mem_cons, List.mem_append] at hM
      rcases hM with rfl | (hM | hM) | hM
      · exact ⟨_, List.mem_cons_self, .cycle h₁ h₂ h⟩
      · obtain ⟨M', hM', hMM'⟩ := h₁.exists_subnets hM
        exact ⟨M', List.mem_cons_of_mem _
          (List.mem_append_left _ (List.mem_append_left _ hM')), hMM'⟩
      · obtain ⟨M', hM', hMM'⟩ := h₂.exists_subnets hM
        exact ⟨M', List.mem_cons_of_mem _
          (List.mem_append_left _ (List.mem_append_right _ hM')), hMM'⟩
      · obtain ⟨M', hM', hMM'⟩ := h.exists_subnets hM
        exact ⟨M', List.mem_cons_of_mem _ (List.mem_append_right _ hM'), hMM'⟩
  | _, _, .swap h₁ h₂ h, _, hM => by
      simp only [Net.subnets, List.mem_cons, List.mem_append] at hM
      rcases hM with rfl | (hM | hM) | hM
      · exact ⟨_, List.mem_cons_self, .swap h₁ h₂ h⟩
      · obtain ⟨M', hM', hMM'⟩ := h₁.exists_subnets hM
        exact ⟨M', List.mem_cons_of_mem _
          (List.mem_append_left _ (List.mem_append_right _ hM')), hMM'⟩
      · obtain ⟨M', hM', hMM'⟩ := h₂.exists_subnets hM
        exact ⟨M', List.mem_cons_of_mem _
          (List.mem_append_left _ (List.mem_append_left _ hM')), hMM'⟩
      · obtain ⟨M', hM', hMM'⟩ := h.exists_subnets hM
        exact ⟨M', List.mem_cons_of_mem _ (List.mem_append_right _ hM'), hMM'⟩

/-- Each subnetwork hanging from a side is related to a subnetwork hanging from the related side. -/
theorem Side.SideSwap.exists_subnets : ∀ {S S' : Side X}, S.SideSwap S' →
    ∀ {M : Net X}, M ∈ S.subnets → ∃ M' ∈ S'.subnets, M.SideSwap M'
  | _, _, .hyb _, _, hM => by simp [Side.subnets] at hM
  | _, _, .node h₁ h₂, _, hM => by
      simp only [Side.subnets, List.mem_append] at hM
      rcases hM with hM | hM
      · obtain ⟨M', hM', hMM'⟩ := h₁.exists_subnets hM
        exact ⟨M', List.mem_append_left _ hM', hMM'⟩
      · obtain ⟨M', hM', hMM'⟩ := h₂.exists_subnets hM
        exact ⟨M', List.mem_append_right _ hM', hMM'⟩
end

variable [DecidableEq X]

/-- `N` and `N'` have the same taxa. -/
theorem Net.SideSwap.taxa_eq {N N' : Net X} (h : N.SideSwap N') : N.taxa = N'.taxa :=
  List.toFinset_eq_of_perm _ _ h.perm_leaves

/-- Two related sides have the same taxa below them. -/
theorem Side.SideSwap.taxa_eq {S S' : Side X} (h : S.SideSwap S') : S.taxa = S'.taxa :=
  List.toFinset_eq_of_perm _ _ h.perm_leaves

/-- The networks hanging from the nodes of two related sides have the same taxa, node by node. -/
theorem Side.SideSwap.map_taxa_nodes : ∀ {S S' : Side X}, S.SideSwap S' →
    S.nodes.map (fun n => n.2.2.taxa) = S'.nodes.map (fun n => n.2.2.taxa)
  | _, _, .hyb _ => rfl
  | _, _, .node h₁ h₂ => by
      simp only [Side.nodes, List.map_cons, h₁.taxa_eq, h₂.map_taxa_nodes]

/-- Each node of `S'` has a node of `S` with a pendant network on the same taxa. -/
theorem Side.SideSwap.exists_node {S S' : Side X} (h : S.SideSwap S') {n' : ℝ × ℝ × Net X}
    (hn' : n' ∈ S'.nodes) : ∃ n ∈ S.nodes, n.2.2.taxa = n'.2.2.taxa := by
  have hmem : n'.2.2.taxa ∈ S.nodes.map (fun n => n.2.2.taxa) := by
    rw [h.map_taxa_nodes]
    exact List.mem_map_of_mem hn'
  exact List.mem_map.1 hmem

/-! ### The network multispecies coalescent -/

section Coalescent

variable {L : Type*} [Fintype L] [DecidableEq L]

/-- The sum of the NMSC at a cycle, over the set `A` of the roots of the forest `F` at the hybrid
node that take the hybrid edge of the first side, is unchanged when the two sides are exchanged
and `γ` becomes `1 - γ`: reindex by `A ↦ roots F \ A`, and exchange the two independent forests
(`Brooqs.forestUnion_comm`). -/
theorem cycle_sum_swap (γ : ℝ) (F G : Finset (Finset L))
    (μ ν : Finset (Finset L) → Finset (Finset L) → ℝ) :
    ∑ A ∈ (roots F).powerset, γ ^ #A * (1 - γ) ^ #(roots F \ A) *
        forestUnion (μ (forestBelow F A)) (ν (forestBelow F (roots F \ A))) G =
      ∑ A ∈ (roots F).powerset, (1 - γ) ^ #A * (1 - (1 - γ)) ^ #(roots F \ A) *
        forestUnion (ν (forestBelow F A)) (μ (forestBelow F (roots F \ A))) G := by
  refine sum_nbij' (fun A => roots F \ A) (fun A => roots F \ A)
    (fun _ _ => mem_powerset.2 sdiff_subset) (fun _ _ => mem_powerset.2 sdiff_subset)
    (fun A hA => Finset.sdiff_sdiff_eq_self (mem_powerset.1 hA))
    (fun A hA => Finset.sdiff_sdiff_eq_self (mem_powerset.1 hA)) fun A hA => ?_
  rw [Finset.sdiff_sdiff_eq_self (mem_powerset.1 hA), sub_sub_cancel, forestUnion_comm]
  ring

mutual
/-- **The NMSC does not depend on the order of the sides of a cycle.** The forest of gene lineages
at the root has the same distribution on `N` and on `N'`. -/
theorem Net.SideSwap.forestDist_eq (s : L → X) :
    ∀ {N N' : Net X}, N.SideSwap N' → N.forestDist s = N'.forestDist s
  | _, _, .leaf _ => rfl
  | _, _, .tree h₁ h₂ => by
      simp only [Net.forestDist, h₁.forestDist_eq s, h₂.forestDist_eq s]
  | _, _, .cycle h₁ h₂ h => by
      simp only [Net.forestDist, h₁.forestDist_eq s, h₂.forestDist_eq s, h.forestDist_eq s]
  | _, _, .swap h₁ h₂ h => by
      funext G
      simp only [Net.forestDist, h₁.forestDist_eq s, h₂.forestDist_eq s, h.forestDist_eq s]
      refine sum_congr rfl fun F _ => ?_
      rw [cycle_sum_swap]

/-- The NMSC along two related sides has the same transition probabilities. -/
theorem Side.SideSwap.forestDist_eq (s : L → X) :
    ∀ {S S' : Side X}, S.SideSwap S' → S.forestDist s = S'.forestDist s
  | _, _, .hyb _ => rfl
  | _, _, .node h₁ h₂ => by
      simp only [Side.forestDist, h₁.forestDist_eq s, h₂.forestDist_eq s]
end

/-- The gene trees have the same distribution under the NMSC on `N` and on `N'`. -/
theorem Net.SideSwap.geneTreeDist_eq (s : L → X) {N N' : Net X} (h : N.SideSwap N') :
    N.geneTreeDist s = N'.geneTreeDist s := by
  simp only [Net.geneTreeDist, h.forestDist_eq s]

end Coalescent

/-- The quartet CFs of `N` and of `N'` are equal. -/
theorem Net.SideSwap.quartetCF_eq {N N' : Net X} (h : N.SideSwap N') (a b c e : X) :
    N.quartetCF a b c e = N'.quartetCF a b c e := by
  simp only [Net.quartetCF, h.geneTreeDist_eq]

/-! ### Displayed trees and quartets -/

mutual
/-- Every displayed tree of `N` is a displayed tree of `N'`: at an exchanged cycle, the tree that
hangs the hybrid component from the bottom of `S₁` hangs it from the bottom of the same side, now
the second one. -/
theorem Net.SideSwap.mem_displayed : ∀ {N N' : Net X}, N.SideSwap N' →
    ∀ {K : Finset (Finset X)}, K ∈ N.displayed → K ∈ N'.displayed
  | _, _, .leaf _, _, hK => hK
  | _, _, .tree h₁ h₂, _, hK => by
      simp only [Net.displayed, List.mem_flatMap, List.mem_map] at hK ⊢
      obtain ⟨K₁, hK₁, K₂, hK₂, rfl⟩ := hK
      exact ⟨K₁, h₁.mem_displayed hK₁, K₂, h₂.mem_displayed hK₂, by
        rw [h₁.taxa_eq, h₂.taxa_eq]⟩
  | _, _, .cycle h₁ h₂ h, _, hK => by
      simp only [Net.displayed, List.mem_flatMap, List.mem_append, List.mem_map] at hK ⊢
      rw [← h.taxa_eq, ← h₁.taxa_eq, ← h₂.taxa_eq]
      obtain ⟨K₀, hK₀, ⟨K₁, hK₁, K₂, hK₂, rfl⟩ | ⟨K₁, hK₁, K₂, hK₂, rfl⟩⟩ := hK
      · exact ⟨K₀, h.mem_displayed hK₀,
          Or.inl ⟨K₁, h₁.mem_displayed hK₁, K₂, h₂.mem_displayed hK₂, rfl⟩⟩
      · exact ⟨K₀, h.mem_displayed hK₀,
          Or.inr ⟨K₁, h₁.mem_displayed hK₁, K₂, h₂.mem_displayed hK₂, rfl⟩⟩
  | _, _, .swap (S₁ := S₁) (S₂ := S₂) (N := N) h₁ h₂ h, _, hK => by
      simp only [Net.displayed, List.mem_flatMap, List.mem_append, List.mem_map] at hK ⊢
      rw [← h.taxa_eq, ← h₁.taxa_eq, ← h₂.taxa_eq, union_comm S₂.taxa S₁.taxa]
      obtain ⟨K₀, hK₀, ⟨K₁, hK₁, K₂, hK₂, rfl⟩ | ⟨K₁, hK₁, K₂, hK₂, rfl⟩⟩ := hK
      -- the hybrid component hangs from `S₁`, the second side after the exchange
      · exact ⟨K₀, h.mem_displayed hK₀,
          Or.inr ⟨K₂, h₂.mem_displayed hK₂, K₁, h₁.mem_displayed hK₁,
            by rw [union_right_comm K₀]⟩⟩
      -- the hybrid component hangs from `S₂`, the first side after the exchange
      · exact ⟨K₀, h.mem_displayed hK₀,
          Or.inl ⟨K₂, h₂.mem_displayed hK₂, K₁, h₁.mem_displayed hK₁,
            by rw [union_right_comm K₀]⟩⟩

/-- The clusters of the displayed trees along two related sides are the same. -/
theorem Side.SideSwap.mem_displayed : ∀ {S S' : Side X}, S.SideSwap S' →
    ∀ {T : Finset X} {K : Finset (Finset X)}, K ∈ S.displayed T → K ∈ S'.displayed T
  | _, _, .hyb _, _, _, hK => hK
  | _, _, .node h₁ h₂, _, _, hK => by
      simp only [Side.displayed, List.mem_flatMap, List.mem_map] at hK ⊢
      obtain ⟨K₁, hK₁, K₂, hK₂, rfl⟩ := hK
      exact ⟨K₁, h₂.mem_displayed hK₁, K₂, h₁.mem_displayed hK₂, by
        rw [h₁.taxa_eq, h₂.taxa_eq]⟩
end

/-- **The displayed trees do not depend on the order of the sides of a cycle.** `N` and `N'` have
the same displayed trees (CAMUS's Definition 1), each given by its clusters. -/
theorem Net.SideSwap.mem_displayed_iff {N N' : Net X} (h : N.SideSwap N')
    (K : Finset (Finset X)) : K ∈ N.displayed ↔ K ∈ N'.displayed :=
  ⟨h.mem_displayed, h.symm.mem_displayed⟩

/-- `N` and `N'` display the same quartets. -/
theorem Net.SideSwap.displays_iff {N N' : Net X} (h : N.SideSwap N') (a b c e : X) :
    N.Displays a b c e ↔ N'.Displays a b c e := by
  simp only [Net.Displays, h.mem_displayed_iff]

/-! ### Cycles and the anomalous configuration -/

/-- Two related networks hold the same lineages among the four sampled ones: they have the same
taxa. -/
theorem Net.SideSwap.lin_eq {M M' : Net X} (h : M.SideSwap M') (s : Fin 4 → X) :
    M.lin s = M'.lin s := by
  simp only [Net.lin, h.taxa_eq]

/-- The networks hanging from two sides together, as the anomalous configuration counts them: if
each holds at most one of the lineages, so does each network hanging from the related sides. -/
theorem Side.SideSwap.card_lin_le {S₁ S₂ S₁' S₂' : Side X} (h₁ : S₁.SideSwap S₁')
    (h₂ : S₂.SideSwap S₂') {s : Fin 4 → X}
    (h : ∀ n ∈ S₁.nodes ++ S₂.nodes, #(n.2.2.lin s) ≤ 1) :
    ∀ n ∈ S₁'.nodes ++ S₂'.nodes, #(n.2.2.lin s) ≤ 1 := by
  have hlin : ∀ {n n' : ℝ × ℝ × Net X}, n.2.2.taxa = n'.2.2.taxa →
      n.2.2.lin s = n'.2.2.lin s := fun hn => by
    simp only [Net.lin, hn]
  intro n' hn'
  rcases List.mem_append.1 hn' with hn' | hn'
  · obtain ⟨n, hn, hnn'⟩ := h₁.exists_node hn'
    rw [← hlin hnn']
    exact h n (List.mem_append_left _ hn)
  · obtain ⟨n, hn, hnn'⟩ := h₂.exists_node hn'
    rw [← hlin hnn']
    exact h n (List.mem_append_right _ hn)

/-- If four taxa of `N` are in the anomalous configuration, they are in `N'`: the cycle of `N'`
related to the anomalous cycle has the same taxa below its hybrid node and below its top node, and
the networks hanging from its two sides together have the same taxa. -/
theorem Net.SideSwap.anomalous {N N' : Net X} (h : N.SideSwap N') {s : Fin 4 → X}
    (hA : N.Anomalous s) : N'.Anomalous s := by
  obtain ⟨Ω, h2, h3, h1⟩ := hA
  obtain ⟨M', hM', hΩM'⟩ := h.exists_subnets Ω.mem
  have h3' : 3 ≤ #(M'.lin s) := le_of_le_of_eq h3 (congrArg card (hΩM'.lin_eq s))
  rcases hΩM' with _ | _ | ⟨h₁, h₂, hb⟩ | ⟨h₁, h₂, hb⟩
  · exact ⟨⟨_, _, _, _, _, hM'⟩, (congrArg card (hb.lin_eq s)).symm.trans h2, h3',
      h₁.card_lin_le h₂ h1⟩
  · have h1' : ∀ n ∈ Ω.side₂.nodes ++ Ω.side₁.nodes, #(n.2.2.lin s) ≤ 1 := fun n hn =>
      h1 n (List.perm_append_comm.mem_iff.1 hn)
    exact ⟨⟨_, _, _, _, _, hM'⟩, (congrArg card (hb.lin_eq s)).symm.trans h2, h3',
      h₂.card_lin_le h₁ h1'⟩

/-- **The anomalous configuration does not depend on the order of the sides of a cycle.** Four
taxa of `N` are in the anomalous configuration iff they are in `N'`. -/
theorem Net.SideSwap.anomalous_iff {N N' : Net X} (h : N.SideSwap N') (s : Fin 4 → X) :
    N.Anomalous s ↔ N'.Anomalous s :=
  ⟨h.anomalous, h.symm.anomalous⟩

end Brooqs
