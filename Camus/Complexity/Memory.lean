module

public import Camus.Complexity.Program

/-!
# Section 2.3: the memory of the program

Section 2.3 of the paper bounds the memory of CAMUS: "We can represent Q in O(n⁴) space, since we
consider integers to require O(1) memory. All other data structures needed for the algorithm, such
as the precomputed LCAs, etc., can be stored in O(n²); hence the total memory usage is O(n⁴)." The
cost monad of `Camus/Complexity/Timed.lean` counts time only. This file bounds the data that the
program `Complexity.camus` keeps: each of its tables is a function that differs from its initial
value only on a set of keys determined by `T` (`Complexity.SupportedIn`): the vertices of `T` for
the parents, depths, kinds and `M`, the taxa for the leaves, the pairs of vertices for the lowest
common ancestors, the targets for the buckets (which hold `|candidates|` pairs in all), and the
candidate pairs for the weights. Counting the integers stored at these keys
(`Complexity.storedIntegers`) gives at most three times the count `Complexity.scalarSpace` of
`Camus/Complexity/Operations.lean`, hence `O(n⁴)` by `Complexity.scalarSpace_bound`.

## Main results

* `Complexity.preprocess_support`, `Complexity.enumerate_support`, `Complexity.fill_support`: the
  keys at which the tables of `camus` are written.
* `Complexity.storedIntegers`: the integers stored at these keys, and by `Q`.
* `Complexity.storedIntegers_le`: at most `3 · scalarSpace t Q`.
* `Complexity.storedIntegers_bound`: at most `96 n⁴` when the quartets of `Q` are on taxa of `T`.
-/

@[expose] public section

namespace Camus.Complexity

open Timed DynamicProgramming

/-- The table `f` differs from the default value `d` only at keys of `S`: it is stored by its
entries at the keys of `S`. -/
def SupportedIn {κ β : Type} (f : κ → β) (d : β) (S : Finset κ) : Prop := ∀ k ∉ S, f k = d

/-- Section 2.3: the preprocessing writes the tables of parents, depths and kinds at the vertices of
`T`, the table of leaves at its taxa, and the table of lowest common ancestors at the pairs of its
vertices. -/
theorem preprocess_support (t : PhyloTree) :
    let T := (preprocess t).val.1
    SupportedIn T.parent [] t.nodes ∧ SupportedIn T.depth 0 t.nodes ∧
      SupportedIn T.kind default t.nodes ∧ SupportedIn T.leafOf none t.taxa ∧
      SupportedIn T.lca [] (t.nodes ×ˢ t.nodes) := by
  intro T
  have hT := preprocess_correct t
  set T₀ := (t.preorder.map (entryAt t)).foldl (fun T x => (record T x).val) Tables.empty
    with hT₀
  have hrec : (preprocess t).val.1 = (lcaTable t.preorder T₀).val := by
    simp [preprocess, val_visit_root, T₀, List.map_map, Function.comp_def, entryAt]
  obtain ⟨hpar, hdep, hkind, hleaf, -⟩ := lcaTable_correct t T₀ (record_correct t).2.1
    (record_correct t).1
  have hout : ∀ (p : Address), p ∉ t.nodes →
      ∀ x ∈ t.preorder.map (entryAt t), x.addr ≠ p := by
    intro p hp x hx h
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    exact hp (h ▸ (PhyloTree.mem_preorder t q).mp hq)
  refine ⟨fun p hp => ?_, fun p hp => ?_, fun p hp => ?_, fun a ha => ?_, fun x hx => ?_⟩
  · simp only [T, hrec, hpar, T₀, foldl_record_parent]
    exact foldl_update_of_not_mem Entry.addr Entry.parent _ _ (hout p hp)
  · simp only [T, hrec, hdep, T₀, foldl_record_depth]
    exact foldl_update_of_not_mem Entry.addr Entry.depth _ _ (hout p hp)
  · simp only [T, hrec, hkind, T₀, foldl_record_kind]
    exact foldl_update_of_not_mem Entry.addr Entry.kind _ _ (hout p hp)
  · cases h : T.leafOf a with
    | none => rfl
    | some p =>
      exact (ha (List.mem_toFinset.mpr (PhyloTree.leaf_label_mem (hT.leafOf_sound a p h)))).elim
  · -- the entries of the table of lowest common ancestors are written at pairs of vertices
    simp only [T, hrec, lcaTable, val_forList]
    refine foldl_invariant t.preorder _ (fun _ (U : Tables) => U.lca x = []) ?_ ?_
    · simp only [T₀, foldl_record_lca]
      rfl
    · intro A p B U hsplit hU
      have hp : p ∈ t.nodes := (PhyloTree.mem_preorder t p).mp (by rw [hsplit]; simp)
      simp only [lcaRow, val_forList]
      refine foldl_invariant t.preorder _ (fun _ (V : Tables) => V.lca x = []) hU ?_
      intro A' q B' V hsplit' hV
      have hq : q ∈ t.nodes := (PhyloTree.mem_preorder t q).mp (by rw [hsplit']; simp)
      have hne : (p, q) ≠ x := fun h => hx (h ▸ Finset.mem_product.mpr ⟨hp, hq⟩)
      simp only [val_bind, val_step]
      rw [Function.update_of_ne hne.symm]
      exact hV

/-- Section 2.3: the enumeration writes the buckets at the vertices of `T`, which hold the
`|candidates|` candidate pairs in all, and the weights at the candidate pairs. -/
theorem enumerate_support {t : PhyloTree} {T : Tables} (hT : T.Correct t) (Q : Multiset Quartet) :
    let S := (enumerate T Q t.preorder).val
    SupportedIn S.1 [] t.nodes ∧ SupportedIn S.2 0 (EdgeAbove.candidates t) ∧
      ∑ v ∈ t.nodes, (S.1 v).length = (EdgeAbove.candidates t).card := by
  intro S
  obtain ⟨hB, -⟩ := enumerate_buckets hT Q
  have hlen : ∀ v, (S.1 v).length = (pairsAt t v).card := by
    intro v
    rw [← List.toFinset_card_of_nodup (hB v).1]
    congr 1
    ext e
    simp [(hB v).2]
  refine ⟨fun v hv => ?_, fun e he => ?_, ?_⟩
  · -- no candidate pair has its target outside `T`
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro e he
    have hp := ((hB v).2 e).mp he
    obtain ⟨hc, htarget⟩ := Finset.mem_filter.mp hp
    exact hv (htarget ▸ EdgeAbove.target_mem_nodes (Finset.mem_filter.mp hc).2)
  · -- the weights are written at admissible pairs only
    simp only [S, enumerate, val_forList]
    refine foldl_invariant (pairList t.preorder) _
      (fun _ (U : Buckets) => U.2 e = 0) rfl ?_
    intro A f B U hsplit hU
    rw [val_visitPair]
    split_ifs with hok
    · have hf : f ∈ pairList t.preorder := by rw [hsplit]; simp
      obtain ⟨hu, hw⟩ := (mem_pairList _ f).mp hf
      rw [PhyloTree.mem_preorder] at hu hw
      rw [val_admissibleTest hT hu hw] at hok
      have hfc : f ∈ EdgeAbove.candidates t :=
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hu, hw⟩, of_decide_eq_true hok⟩
      have hne : e ≠ f := fun h => he (h ▸ hfc)
      simp only
      rw [Function.update_of_ne hne]
      exact hU
    · exact hU
  · simp only [hlen]
    exact candidate_visits t

/-- Section 2.3: the fill writes `M` at the vertices of `T`. -/
theorem fill_support {t : PhyloTree} (T : Tables) (B : Address → List (Address × Address))
    (W : Address × Address → ℕ) : SupportedIn (fill T B W t.preorder.reverse).val 0 t.nodes := by
  intro x hx
  simp only [fill, val_forList]
  refine foldl_invariant t.preorder.reverse _ (fun _ (M : Address → ℕ) => M x = 0) rfl ?_
  intro A v B' M hsplit hM
  have hv : v ∈ t.nodes := by
    rw [← PhyloTree.mem_preorder, ← List.mem_reverse, hsplit]; simp
  have hne : x ≠ v := fun h => hx (h ▸ hv)
  unfold solveVertex
  cases T.kind v with
  | leaf a =>
    simp only [val_bind, val_step]
    rw [Function.update_of_ne hne]
    exact hM
  | fork l r =>
    simp only [val_bind, val_step, val_steps]
    rw [Function.update_of_ne hne]
    exact hM

/-- Section 2.3: the integers stored by `camus`, each of unit size: six per distinct quartet of `Q`
(four labels, the split and the multiplicity); per vertex of `T` its parent, its depth, its kind
(a label, or the names of two children) and `M[v]`; per taxon its leaf; per pair of vertices their
lowest common ancestor; per candidate pair its weight and its two ends in a bucket. -/
noncomputable def storedIntegers (t : PhyloTree) (Q : Multiset Quartet) : ℕ :=
  6 * Q.toFinset.card + 5 * t.nodes.card + t.taxa.card + t.nodes.card ^ 2 +
    3 * (EdgeAbove.candidates t).card

/-- The integers stored by `camus` are at most three times those counted by `scalarSpace`: the
program keeps the leaf of each taxon instead of the leaf set of each vertex, and the buckets in
addition. -/
theorem storedIntegers_le {t : PhyloTree} (ht : t.WellLabelled) (Q : Multiset Quartet) :
    storedIntegers t Q ≤ 3 * scalarSpace t Q := by
  have htaxa : t.taxa.card = t.labels.length := List.toFinset_card_of_nodup ht
  have hnodes := t.nodes_count
  have hn := t.labels_nonempty
  unfold storedIntegers scalarSpace
  simp only [Finset.card_product]
  rw [htaxa]
  have h1 : t.labels.length ≤ t.nodes.card := by omega
  have h2 : t.nodes.card ≤ t.nodes.card * t.labels.length :=
    Nat.le_mul_of_pos_right _ hn
  nlinarith

/-- **Section 2.3: the memory `O(n⁴)`.** For a well-labelled tree `T` with `n` leaves and a
multiset `Q` whose quartets are on taxa of `T`, the integers stored by `camus` and by `Q` number at
most `96 n⁴`. -/
theorem storedIntegers_bound {t : PhyloTree} (ht : t.WellLabelled) (Q : Multiset Quartet)
    (hQ : ∀ q ∈ Q.toFinset, q.taxa ⊆ t.taxa) : storedIntegers t Q ≤ 96 * t.taxa.card ^ 4 := by
  have h1 := storedIntegers_le ht Q
  have h2 := scalarSpace_bound ht Q hQ
  omega

end Camus.Complexity
