module

public import Camus.External.NMSC.Displayed
public import Camus.External.NMSC.GeneLaw

/-!
# The three quartets on four taxa

The quartet CF `Brooqs.Net.quartetCF N a b c e` samples the lineages `0, 1, 2, 3` from the taxa
`a, b, c, e` and gives the probability of the split `{0, 1} | {2, 3}`. To compare the three quartets
on the same four taxa, this file fixes the sampling `s` and varies the split: `Brooqs.Net.splitCF N s
A` is the probability of the split `A | Aᶜ` (`Brooqs.Net.quartetCF_eq_splitCF_of`). Relabelling the
lineages relabels the splits (`Brooqs.Net.splitCF_comp`), and the three splits have probabilities
adding up to `1` (`Brooqs.Net.splitCF_sum`, `Brooqs.Net.quartetCF_add`).

Two lineages sampled from the taxa of a subnetwork `C` (below a cut edge), the two others from
outside it, are exchangeable: at the root of `C` they have coalesced or not, and the rest of the
network treats them alike (`Brooqs.Net.splitCF_swap`). So if `C` contains `x` and `y` but neither `z`
nor `w`, then `CF(xz|yw) = CF(xw|yz)` (`Brooqs.Net.quartetCF_pair`), the equality that Section 3.3
of CAMUS expects of the two quartets that the network does not display.

## Main results

* `Brooqs.Net.splitCF`, `Brooqs.Net.quartetCF_eq_splitCF_of`, `Brooqs.Net.splitCF_comp`,
  `Brooqs.Net.splitCF_compl`: split CFs and relabelling.
* `Brooqs.Net.forestDist_support`, `Brooqs.Net.geneTreeDist_support`: the forests and gene trees.
* `Brooqs.Net.splitCF_sum`, `Brooqs.Net.quartetCF_add`: the three CFs add up to `1`.
* `Brooqs.Net.splitCF_swap`, `Brooqs.Net.quartetCF_pair`: exchangeability below a cut edge.
-/

@[expose] public noncomputable section

namespace Brooqs

open Finset Matrix

universe u

variable {X : Type u} [DecidableEq X]

/-- The probability that the gene tree of the four lineages sampled by `s` (lineage `l` from the
taxon `s l`) has the split `A | Aᶜ`. The quartet CF is the case `A = {0, 1}`
(`Brooqs.Net.quartetCF_eq_splitCF`). -/
def Net.splitCF (N : Net X) (s : Fin 4 → X) (A : Finset (Fin 4)) : ℝ :=
  ∑ G, if A ∈ unroot G then N.geneTreeDist s G else 0

theorem Net.quartetCF_eq_splitCF (N : Net X) (a b c e : X) :
    N.quartetCF a b c e = N.splitCF ![a, b, c, e] {0, 1} := rfl

/-! ### Relabelling the four lineages -/

private theorem sp_relabel_relabel_symm (σ : Equiv.Perm (Fin 4)) (H : Finset (Finset (Fin 4))) :
    ADR11.relabelFamily σ (ADR11.relabelFamily σ.symm H) = H := by
  simpa using ADR11.relabelFamily_symm σ.symm H

/-- Relabelling the four lineages by `σ` relabels the forests at the root. -/
theorem Net.forestDist_comp_symm (N : Net X) (s : Fin 4 → X) (σ : Equiv.Perm (Fin 4))
    (G : Finset (Finset (Fin 4))) :
    N.forestDist (s ∘ σ.symm) (ADR11.relabelFamily σ G) = N.forestDist s G := by
  have key : (fun a H => sampledInput s a (ADR11.relabelFamily σ.symm H)) =
      sampledInput (s ∘ σ.symm) := by
    funext a H
    simp only [sampledInput, Pi.single_apply]
    have h : ADR11.relabelFamily σ.symm H = sampledAt s a ↔ H = sampledAt (s ∘ σ.symm) a := by
      rw [← relabel_sampledAt]
      constructor
      · intro h
        rw [← h, sp_relabel_relabel_symm]
      · rintro rfl
        exact ADR11.relabelFamily_symm σ _
    simp only [h]
  rw [Net.forestDist_eq, Net.forestDist_eq, ← key]
  exact Net.forestDistOf_relabel σ (sampledInput s) N G

/-- Relabelling the four lineages by `σ` relabels the gene trees. -/
theorem Net.geneTreeDist_comp_symm (N : Net X) (s : Fin 4 → X) (σ : Equiv.Perm (Fin 4))
    (G : Finset (Finset (Fin 4))) :
    N.geneTreeDist (s ∘ σ.symm) (ADR11.relabelFamily σ G) = N.geneTreeDist s G := by
  unfold Net.geneTreeDist
  simp only [vecMul, dotProduct]
  rw [← Equiv.sum_comp (ADR11.relabelFamilyEquiv σ)]
  refine sum_congr rfl fun F _ => ?_
  rw [ADR11.relabelFamilyEquiv_apply, Net.forestDist_comp_symm, kingmanAbsorption_relabel]

/-- Relabelling the four lineages by `σ` maps the splits by `σ`. -/
theorem Net.splitCF_comp (N : Net X) (s : Fin 4 → X) (σ : Equiv.Perm (Fin 4))
    (A : Finset (Fin 4)) : N.splitCF (s ∘ σ) A = N.splitCF s (A.map σ.toEmbedding) := by
  have hs : s ∘ σ = s ∘ σ.symm.symm := by rw [Equiv.symm_symm]
  unfold Net.splitCF
  rw [hs, ← Equiv.sum_comp (ADR11.relabelFamilyEquiv σ.symm)]
  refine sum_congr rfl fun G _ => ?_
  rw [ADR11.relabelFamilyEquiv_apply, Net.geneTreeDist_comp_symm]
  refine if_congr ?_ rfl rfl
  rw [unroot_eq_adr11, ADR11.unroot_relabelFamily, ADR11.mem_relabelFamily, Equiv.symm_symm]
  rfl

/-- A split and its complement are the same split. -/
theorem Net.splitCF_compl (N : Net X) (s : Fin 4 → X) (A : Finset (Fin 4)) :
    N.splitCF s Aᶜ = N.splitCF s A := by
  unfold Net.splitCF
  refine sum_congr rfl fun G _ => if_congr ?_ rfl rfl
  rw [unroot_eq_adr11, ADR11.absorb_mem_unroot, ADR11.absorb_mem_unroot, compl_compl]
  tauto

/-- The quartet CF of `s i, s j | s k, s l` is the split CF of `{i, j}`. -/
theorem Net.quartetCF_eq_splitCF_of (N : Net X) (s : Fin 4 → X) {i j k l : Fin 4}
    (h : Function.Injective ![i, j, k, l]) :
    N.quartetCF (s i) (s j) (s k) (s l) = N.splitCF s {i, j} := by
  set σ : Equiv.Perm (Fin 4) := Equiv.ofBijective ![i, j, k, l] (Finite.injective_iff_bijective.1 h)
  have hs : ![s i, s j, s k, s l] = s ∘ σ := by
    funext m
    fin_cases m <;> rfl
  rw [Net.quartetCF_eq_splitCF, hs, Net.splitCF_comp]
  congr 1
  simp [σ]

/-! ### The three splits -/

private theorem sp_lineages_sampledAt (s : Fin 4 → X) (x : X) :
    ADR11.lineages (sampledAt s x) = univ.filter fun l => s l = x :=
  lineages_singletons _

/-- The forests at the root of a subnetwork `C`: good forests on the lineages sampled from the
taxa of `C`, containing their singletons. -/
theorem Net.forestDist_support {C : Net X} (hC : C.leaves.Nodup) (s : Fin 4 → X)
    {F : Finset (Finset (Fin 4))} (hF : C.forestDist s F ≠ 0) :
    IsGood F ∧ (∀ l, s l ∈ C.taxa → {l} ∈ F) ∧
      ADR11.lineages F = univ.filter fun l => s l ∈ C.taxa := by
  rw [Net.forestDist_eq] at hF
  obtain ⟨hFg, hsub, hFl⟩ := Net.forestDistOf_single_support C hC (sampledAt s)
    (fun _ _ => isGood_singletons _) (fun _ _ _ _ hab => disjoint_lineages_sampledAt s hab) hF
  refine ⟨hFg, fun l hl => hsub (s l) (by simpa [Net.taxa] using hl) ?_, ?_⟩
  · exact mem_image.2 ⟨l, by simp, rfl⟩
  · rw [hFl]
    ext l
    simp [sp_lineages_sampledAt, Net.taxa]

/-- The gene trees of four lineages sampled from taxa of `N` are good trees on the four
lineages. -/
theorem Net.geneTreeDist_support {N : Net X} (hN : N.leaves.Nodup) {s : Fin 4 → X}
    (hsN : ∀ l, s l ∈ N.taxa) {G : Finset (Finset (Fin 4))} (hG : N.geneTreeDist s G ≠ 0) :
    IsGood G ∧ (univ : Finset (Fin 4)) ∈ G := by
  unfold Net.geneTreeDist at hG
  simp only [vecMul, dotProduct] at hG
  obtain ⟨F, -, hF⟩ := exists_ne_zero_of_sum_ne_zero hG
  obtain ⟨hFg, -, hFl⟩ := Net.forestDist_support hN s (left_ne_zero_of_mul hF)
  have hlin : ADR11.lineages F = univ := by
    rw [hFl]
    exact filter_true_of_mem fun l _ => hsN l
  obtain ⟨hGg, -, hGl, hroot⟩ := kingmanAbsorption_support hFg (right_ne_zero_of_mul hF)
  have hne : F.Nonempty := by
    rw [nonempty_iff_ne_empty]
    rintro rfl
    rw [ADR11.lineages_empty] at hlin
    exact univ_nonempty.ne_empty hlin.symm
  have := ADR11.lineages_mem_of_card_roots_eq_one (hroot hne)
  rw [hGl, hlin] at this
  exact ⟨hGg, this⟩

private theorem sp_exists_two_of_three {G : Finset (Finset (Fin 4))} (hG : IsGood G)
    {D : Finset (Fin 4)} (hD : D ∈ G) (hD3 : #D = 3) : ∃ C ∈ G, #C = 2 := by
  obtain ⟨E, hE, E', hE', hEE', hEU⟩ := hG.2 D hD (by omega)
  have hc := card_union_of_disjoint hEE'
  rw [hEU] at hc
  have := (hG.1.1 E hE).card_pos
  have := (hG.1.1 E' hE').card_pos
  by_cases h : #E = 2
  · exact ⟨E, hE, h⟩
  · exact ⟨E', hE', by omega⟩

/-- A good tree on the four lineages has a cluster of two lineages. -/
private theorem sp_exists_two {G : Finset (Finset (Fin 4))} (hG : IsGood G)
    (huniv : (univ : Finset (Fin 4)) ∈ G) : ∃ C ∈ G, #C = 2 := by
  obtain ⟨B, hB, C, hC, hBC, hU⟩ := hG.2 univ huniv (by simp)
  have hc := card_union_of_disjoint hBC
  rw [hU, card_univ, Fintype.card_fin] at hc
  have := (hG.1.1 B hB).card_pos
  have := (hG.1.1 C hC).card_pos
  by_cases h2 : #B = 2
  · exact ⟨B, hB, h2⟩
  by_cases h3 : #B = 3
  · exact sp_exists_two_of_three hG hB h3
  · exact sp_exists_two_of_three hG hC (by omega)

private theorem sp_laminar_two : ∀ A C : Finset (Fin 4), #A = 2 → #C = 2 →
    (A ⊆ C ∨ C ⊆ A ∨ Disjoint A C) → A = C ∨ A = Cᶜ := by
  decide

/-- In a good tree on the four lineages with the cluster `C` of two lineages, the split of the
unrooted tree is `C | Cᶜ`. -/
private theorem sp_mem_unroot_iff {G : Finset (Finset (Fin 4))} (hG : IsGood G)
    {C : Finset (Fin 4)} (hC : C ∈ G) (hC2 : #C = 2) {A : Finset (Fin 4)} (hA : #A = 2) :
    A ∈ unroot G ↔ A = C ∨ A = Cᶜ := by
  have hcA : #Aᶜ = 2 := by rw [card_compl, hA, Fintype.card_fin]
  have hu : ∀ D : Finset (Fin 4), #D = 2 → D ≠ univ := fun D hD h => by
    rw [h, card_univ, Fintype.card_fin] at hD
    omega
  rw [unroot_eq_adr11, ADR11.absorb_mem_unroot]
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩)
    · exact sp_laminar_two A C hA hC2 (hG.1.2 A h C hC)
    · rcases sp_laminar_two Aᶜ C hcA hC2 (hG.1.2 _ h C hC) with h' | h'
      · exact Or.inr (by rw [← h', compl_compl])
      · exact Or.inl (compl_injective h')
  · rintro (rfl | rfl)
    · exact Or.inl ⟨hC, hu _ hC2⟩
    · rw [compl_compl]
      exact Or.inr ⟨hC, hu _ hC2⟩

private theorem sp_count : ∀ C : Finset (Fin 4), #C = 2 →
    (if ({0, 1} : Finset (Fin 4)) = C ∨ {0, 1} = Cᶜ then (1 : ℕ) else 0) +
      (if ({0, 2} : Finset (Fin 4)) = C ∨ {0, 2} = Cᶜ then 1 else 0) +
      (if ({0, 3} : Finset (Fin 4)) = C ∨ {0, 3} = Cᶜ then 1 else 0) = 1 := by
  decide

/-- The CFs of the three splits of four distinct lineages sampled from taxa of `N` add up to
`1`. -/
theorem Net.splitCF_sum {N : Net X} (hN : N.leaves.Nodup) {s : Fin 4 → X}
    (hsN : ∀ l, s l ∈ N.taxa) :
    N.splitCF s {0, 1} + N.splitCF s {0, 2} + N.splitCF s {0, 3} = 1 := by
  rw [← Net.geneTreeDist_sum hN s]
  unfold Net.splitCF
  rw [← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun G _ => ?_
  by_cases hG : N.geneTreeDist s G = 0
  · simp [hG]
  obtain ⟨hGg, huniv⟩ := Net.geneTreeDist_support hN hsN hG
  obtain ⟨C, hC, hC2⟩ := sp_exists_two hGg huniv
  rw [if_congr (sp_mem_unroot_iff hGg hC hC2 (by decide)) rfl rfl,
    if_congr (sp_mem_unroot_iff hGg hC hC2 (by decide)) rfl rfl,
    if_congr (sp_mem_unroot_iff hGg hC hC2 (by decide)) rfl rfl]
  have h := congrArg (fun n : ℕ => (n : ℝ) * N.geneTreeDist s G) (sp_count C hC2)
  simp only [Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, add_mul, ite_mul, one_mul,
    zero_mul] at h
  simpa only [eq_comm (a := ({0, 1} : Finset (Fin 4))), eq_comm (a := ({0, 2} : Finset (Fin 4))),
    eq_comm (a := ({0, 3} : Finset (Fin 4)))] using h

/-! ### Two lineages below a cut edge are exchangeable -/

private theorem sp_swap_pair : ∀ i j : Fin 4, ∀ D : Finset (Fin 4), D ⊆ {i, j} → D.Nonempty →
    D.map (Equiv.swap i j).toEmbedding = D ∨ D.map (Equiv.swap i j).toEmbedding = {i} ∨
      D.map (Equiv.swap i j).toEmbedding = {j} := by
  decide

/-- The split CF as the expectation, over the forest at the root of a subnetwork `C`, of the
probability of the split after the kernel `Φ` of the rest of the network and the population above
the root. -/
private theorem sp_expect {N C : Net X} {s : Fin 4 → X}
    {M : Matrix (Finset (Finset (Fin 4))) (Finset (Finset (Fin 4))) ℝ}
    (hNM : N.forestDist s = C.forestDist s ᵥ* M) (B : Finset (Fin 4)) :
    N.splitCF s B = ∑ F, C.forestDist s F *
      ∑ G, (M * kingmanAbsorption : Matrix (Finset (Finset (Fin 4))) (Finset (Finset (Fin 4))) ℝ)
        F G * (if B ∈ unroot G then 1 else 0) := by
  unfold Net.splitCF Net.geneTreeDist
  rw [hNM, vecMul_vecMul]
  have h : ∀ G, (if B ∈ unroot G then (C.forestDist s ᵥ* (M * kingmanAbsorption)) G else 0) =
      ∑ F, C.forestDist s F * ((M * kingmanAbsorption :
        Matrix (Finset (Finset (Fin 4))) (Finset (Finset (Fin 4))) ℝ) F G *
          if B ∈ unroot G then 1 else 0) := by
    intro G
    rw [← mul_boole]
    simp only [vecMul, dotProduct, sum_mul, mul_assoc]
  rw [sum_congr rfl fun G _ => h G, sum_comm]
  refine sum_congr rfl fun F _ => ?_
  rw [mul_sum]

/-- **Exchangeability.** If a subnetwork `C` of `N` contains exactly the lineages `i` and `j` of
the four (those sampled from its taxa), swapping `i` and `j` does not change the split CFs. At the
root of `C` the two lineages have coalesced or not, and the forest is fixed by the swap; the rest of
`N` and the population above the root treat them alike (`Brooqs.exists_context_kernel`,
`Brooqs.NiceKernel`). -/
theorem Net.splitCF_swap {N : Net X} (hN : N.leaves.Nodup) {C : Net X} (hC : C ∈ N.subnets)
    {s : Fin 4 → X} (hsN : ∀ l, s l ∈ N.taxa) {i j : Fin 4}
    (hin : ∀ l, s l ∈ C.taxa ↔ l = i ∨ l = j) (A : Finset (Fin 4)) :
    N.splitCF s (A.map (Equiv.swap i j).toEmbedding) = N.splitCF s A := by
  obtain ⟨M, hNM, hnice⟩ := exists_context_kernel N hN hC s hsN
  set σ := Equiv.swap i j with hσ
  have hΦ : NiceKernel (univ.filter fun l => s l ∉ C.taxa) (M * kingmanAbsorption) := by
    have := hnice.mul niceKernel_kingmanAbsorption (disjoint_empty_right _)
    rwa [union_empty] at this
  have hσS : ∀ l ∈ univ.filter (fun l => s l ∉ C.taxa), σ l = l := by
    intro l hl
    simp only [mem_filter, mem_univ, true_and, hin, not_or] at hl
    exact Equiv.swap_apply_of_ne_of_ne hl.1 hl.2
  have hCnd : C.leaves.Nodup := (Net.leaves_sublist_of_mem_subnets hC).nodup hN
  -- the forests at the root of `C` are fixed by the swap
  have hfix : ∀ F, C.forestDist s F ≠ 0 → ADR11.relabelFamily σ F = F := by
    intro F hF
    obtain ⟨hFg, hsing, hFl⟩ := Net.forestDist_support hCnd s hF
    have hi : {i} ∈ F := hsing i ((hin i).2 (Or.inl rfl))
    have hj : {j} ∈ F := hsing j ((hin j).2 (Or.inr rfl))
    have hsub : F.image (fun D => D.map σ.toEmbedding) ⊆ F := by
      intro D' hD'
      obtain ⟨D, hD, rfl⟩ := mem_image.1 hD'
      have hDij : D ⊆ {i, j} := fun l hl => by
        have := ADR11.subset_lineages hD hl
        rw [hFl, mem_filter, hin] at this
        rcases this.2 with rfl | rfl <;> simp
      rcases sp_swap_pair i j D hDij (hFg.1.1 D hD) with h | h | h
      · rwa [h]
      · rwa [h]
      · rwa [h]
    show F.image (fun D => D.map σ.toEmbedding) = F
    exact eq_of_subset_of_card_le hsub (by
      rw [card_image_of_injective _ (Finset.map_injective _)])
  rw [sp_expect hNM, sp_expect hNM]
  refine sum_congr rfl fun F _ => ?_
  by_cases hF : C.forestDist s F = 0
  · rw [hF, zero_mul, zero_mul]
  congr 1
  rw [← Equiv.sum_comp (ADR11.relabelFamilyEquiv σ)]
  refine sum_congr rfl fun G _ => ?_
  rw [ADR11.relabelFamilyEquiv_apply]
  have h1 := hΦ.relabel σ hσS F G
  rw [hfix F hF] at h1
  rw [h1]
  congr 1
  refine if_congr ?_ rfl rfl
  rw [unroot_eq_adr11, unroot_eq_adr11, ADR11.unroot_relabelFamily, ADR11.mem_relabelFamily,
    Finset.map_map]
  have : (σ.toEmbedding.trans σ.symm.toEmbedding) = Function.Embedding.refl _ := by
    ext x
    simp
  rw [this, Finset.map_refl]

/-! ### The three quartet CFs of four taxa -/

/-- The quartet CFs of the three quartets on four taxa of `N` add up to `1`. -/
theorem Net.quartetCF_add {N : Net X} (hN : N.leaves.Nodup) {x y z w : X} (hx : x ∈ N.taxa)
    (hy : y ∈ N.taxa) (hz : z ∈ N.taxa) (hw : w ∈ N.taxa) :
    N.quartetCF x y z w + N.quartetCF x z y w + N.quartetCF x w y z = 1 := by
  have hsN : ∀ l, ![x, y, z, w] l ∈ N.taxa := fun l => by fin_cases l <;> assumption
  have h2 := N.quartetCF_eq_splitCF_of ![x, y, z, w] (i := 0) (j := 2) (k := 1) (l := 3)
    (by decide)
  have h3 := N.quartetCF_eq_splitCF_of ![x, y, z, w] (i := 0) (j := 3) (k := 1) (l := 2)
    (by decide)
  change N.quartetCF x z y w = _ at h2
  change N.quartetCF x w y z = _ at h3
  rw [Net.quartetCF_eq_splitCF, h2, h3]
  exact Net.splitCF_sum hN hsN

/-- **A pair below a cut edge (exchangeability).** If a subnetwork `C` of `N` contains the taxa `x`
and `y` but not the taxa `z` and `w` of `N`, the quartets `xz|yw` and `xw|yz` have equal CFs. -/
theorem Net.quartetCF_pair {N : Net X} (hN : N.leaves.Nodup) {C : Net X} (hC : C ∈ N.subnets)
    {x y z w : X} (hx : x ∈ C.taxa) (hy : y ∈ C.taxa) (hz : z ∉ C.taxa) (hw : w ∉ C.taxa) (hzN : z ∈ N.taxa)
    (hwN : w ∈ N.taxa) :
    N.quartetCF x z y w = N.quartetCF x w y z := by
  have hCN := Net.taxa_subset_of_mem_subnets hC
  set s : Fin 4 → X := ![x, z, y, w]
  have hsN : ∀ l, s l ∈ N.taxa := fun l => by
    fin_cases l
    exacts [hCN hx, hzN, hCN hy, hwN]
  have hin : ∀ l, s l ∈ C.taxa ↔ l = 0 ∨ l = 2 := fun l => by
    fin_cases l <;> simp [s, hx, hy, hz, hw]
  have h3 := N.quartetCF_eq_splitCF_of s (i := 0) (j := 3) (k := 2) (l := 1) (by decide)
  change N.quartetCF x w y z = _ at h3
  rw [Net.quartetCF_eq_splitCF, h3, ← Net.splitCF_compl N s {0, 3},
    show ({0, 3} : Finset (Fin 4))ᶜ = ({0, 1} : Finset (Fin 4)).map (Equiv.swap 0 2).toEmbedding
      by decide, Net.splitCF_swap hN hC hsN hin]

end Brooqs
