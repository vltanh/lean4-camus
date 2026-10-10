module

public import Camus.Complexity.Program

/-!
# Section 2.2: backtracking, within the running time of Section 2.3

"Once this array is filled in, the solution is obtained at the root r, and backtracking allow us to
infer the optimal network" (Section 2.2). This file writes the backtracking as a program in the cost
monad (`Complexity.backtrack`) and the whole of CAMUS, array and network
(`Complexity.camusNetwork`), and proves that the family of pairs it returns is a backtracking trace
of the array (`DynamicProgramming.Trace`), so that, by Theorem 1, its network is an optimal level-1
network built on `T`, and that the whole computation still runs in time `O(n²(|Q| + n))`.

The backtracking from a vertex `v` follows the two cases of Equation (2): if
`M[v] = M[l(v)] + M[r(v)]` it continues at the two children; otherwise it looks in the bucket of
`v` for a pair `e` with `s_e + s_dp = M[v]` (`Complexity.findPair`), keeps it, and continues at the
roots of the subtrees hanging off its cycle, listed by the walks of `Complexity.hangingList`. The
subtrees it continues in are disjoint and lie below `v`, so it spends at a vertex `x` at most
`O(n + |Pairs(x)| · n)` operations of its own, and `O(n + |candidates| · n)` in all
(`Complexity.time_backtrack`).

## Main results

* `Complexity.backtrack_trace`: the backtracking returns a trace of the array.
* `Complexity.camusNetwork`: CAMUS with backtracking, as a program.
* `Complexity.camusNetwork_optimal`: for a well-labelled `T`, the network of the returned pairs is
  built on `T`, satisfies `M[root]` quartets of `Q`, and no network built on `T` satisfies more
  (Theorem 1).
* `Complexity.camusNetwork_time`: at most `700 n² (|Q| + n)` operations, array and
  backtracking together.
-/

@[expose] public section

namespace Camus

/-- A vertex of `T` has fewer ancestors than `T` has vertices: its depth is less than `|V(T)|`. -/
theorem PhyloTree.length_lt_card {t : PhyloTree} {p : Address} (hp : p ∈ t.nodes) :
    p.length < t.nodes.card := by
  have hsub : (Finset.range (p.length + 1)).image (fun i => p.take i) ⊆ t.nodes := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact t.nodes_prefix_closed hp (List.take_prefix _ _)
  have hinj : Set.InjOn (fun i => p.take i) (Finset.range (p.length + 1) : Set ℕ) := by
    intro i hi j hj h
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    have := congrArg List.length h
    simp only [List.length_take] at this
    omega
  have := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, Finset.card_range] at this
  omega

namespace Complexity

open Timed DynamicProgramming

/-- The vertices of `T` below `v`, `v` included: the vertices of the subtree `T_v`. -/
def cone (t : PhyloTree) (v : Address) : Finset Address := t.nodes.filter fun x => v <+: x

theorem mem_cone {t : PhyloTree} {v x : Address} : x ∈ cone t v ↔ x ∈ t.nodes ∧ v <+: x :=
  Finset.mem_filter

/-- The first pair of the list whose value `s_e + s_dp` (`pairValue`) is `target`: one iteration,
the value, and a comparison per pair examined. -/
def findPair (T : Tables) (W : Address × Address → ℕ) (M : Address → ℕ) (target : ℕ) :
    List (Address × Address) → Timed (Option (Address × Address))
  | [] => pure none
  | e :: es => do
      tick
      let x ← pairValue T W M e
      let ok ← step (decide (x = target))
      if ok then pure (some e) else findPair T W M target es

theorem findPair_sound (T : Tables) (W : Address × Address → ℕ) (M : Address → ℕ) (target : ℕ) :
    ∀ (l : List (Address × Address)) (e : Address × Address),
      (findPair T W M target l).val = some e → e ∈ l ∧ (pairValue T W M e).val = target := by
  intro l
  induction l with
  | nil => intro e h; simp [findPair] at h
  | cons f l ih =>
    intro e h
    by_cases hf : (pairValue T W M f).val = target
    · simp only [findPair, val_bind, val_step, hf, decide_true, ↓reduceIte,
        val_pure, Option.some.injEq] at h
      subst h
      exact ⟨by simp, hf⟩
    · simp only [findPair, val_bind, val_step, hf, decide_false, Bool.false_eq_true,
        ↓reduceIte] at h
      obtain ⟨he, hv⟩ := ih e h
      exact ⟨by simp [he], hv⟩

theorem findPair_complete (T : Tables) (W : Address × Address → ℕ) (M : Address → ℕ)
    (target : ℕ) : ∀ (l : List (Address × Address)), (∃ e ∈ l, (pairValue T W M e).val = target) →
      ∃ e, (findPair T W M target l).val = some e := by
  intro l
  induction l with
  | nil => intro h; simp at h
  | cons f l ih =>
    intro h
    by_cases hf : (pairValue T W M f).val = target
    · exact ⟨f, by simp [findPair, hf]⟩
    · obtain ⟨e, he, hv⟩ := h
      rcases List.mem_cons.mp he with rfl | he
      · exact (hf hv).elim
      · obtain ⟨e', h'⟩ := ih ⟨e, he, hv⟩
        exact ⟨e', by simp [findPair, hf, h']⟩

theorem time_findPair (T : Tables) (W : Address × Address → ℕ) (M : Address → ℕ) (target : ℕ) :
    ∀ (l : List (Address × Address)),
      (findPair T W M target l).time ≤ (l.map fun e => (pairValue T W M e).time + 2).sum := by
  intro l
  induction l with
  | nil => simp [findPair]
  | cons f l ih =>
    by_cases hf : (pairValue T W M f).val = target
    · simp [findPair, hf]
      omega
    · simp only [findPair, time_bind, time_tick, time_step, val_step, hf,
        decide_false, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.sum_cons]
      omega

/-- Backtracking (Section 2.2) from the vertex `v`, with fuel `n`: at a leaf, nothing; at an
internal vertex, if `M[v] = M[l(v)] + M[r(v)]`, the results at the two children; otherwise a pair
`e` of the bucket of `v` with `s_e + s_dp = M[v]`, and the results at the roots of the subtrees
hanging off its cycle. The pairs found are put in front of `acc`. -/
def backtrack (T : Tables) (B : Address → List (Address × Address)) (W : Address × Address → ℕ)
    (M : Address → ℕ) : ℕ → Address → List (Address × Address) →
      Timed (List (Address × Address))
  | 0, _, acc => pure acc
  | n + 1, v, acc => do
      let k ← step (T.kind v)
      match k with
      | .leaf _ => pure acc
      | .fork l r => do
          let a ← step (M l)
          let b ← step (M r)
          let mv ← step (M v)
          let split ← steps 2 (decide (a + b = mv))
          if split then do
            let acc ← backtrack T B W M n l acc
            backtrack T B W M n r acc
          else do
            let bucket ← step (B v)
            let found ← findPair T W M mv bucket
            match found with
            | none => pure acc
            | some e => do
                let L ← hangingList T e
                forList (fun acc r => backtrack T B W M n r acc) L (e :: acc)

/-- Prepending in a loop. -/
theorem foldl_prepend {α β : Type} (f : α → List β) (L : List α) (a c : List β) :
    L.foldl (fun acc r => f r ++ acc) (a ++ c) = L.foldl (fun acc r => f r ++ acc) a ++ c := by
  induction L generalizing a with
  | nil => rfl
  | cons r L ih =>
    simp only [List.foldl_cons]
    rw [← List.append_assoc, ih]

theorem toFinset_foldl_prepend {α β : Type} [DecidableEq α] [DecidableEq β] (f : α → List β)
    (L : List α) (a : List β) :
    (L.foldl (fun acc r => f r ++ acc) a).toFinset =
      a.toFinset ∪ L.toFinset.biUnion fun r => (f r).toFinset := by
  induction L generalizing a with
  | nil => simp
  | cons r L ih =>
    simp only [List.foldl_cons, ih, List.toFinset_append, List.toFinset_cons,
      Finset.biUnion_insert]
    ext x
    simp only [Finset.mem_union]
    tauto

/-- The backtracking only puts pairs in front of the accumulator. -/
theorem backtrack_acc (T : Tables) (B : Address → List (Address × Address))
    (W : Address × Address → ℕ) (M : Address → ℕ) :
    ∀ (n : ℕ) (v : Address) (acc : List (Address × Address)),
      (backtrack T B W M n v acc).val = (backtrack T B W M n v []).val ++ acc := by
  intro n
  induction n with
  | zero => intro v acc; simp [backtrack]
  | succ n ih =>
    intro v acc
    have hfun : (fun (acc : List (Address × Address)) r => (backtrack T B W M n r acc).val) =
        fun acc r => (backtrack T B W M n r []).val ++ acc := by
      funext acc r
      exact ih r acc
    cases hk : T.kind v with
    | leaf a => simp [backtrack, hk]
    | fork l r =>
      by_cases hs : M l + M r = M v
      · simp only [backtrack, val_bind, val_step, hk, val_steps, hs, decide_true, ↓reduceIte]
        rw [ih r, ih l, ih r (backtrack T B W M n l []).val, List.append_assoc]
      · cases hf : (findPair T W M (M v) (B v)).val with
        | none => simp [backtrack, hk, hs, hf]
        | some e =>
          simp only [backtrack, val_bind, val_step, hk, val_steps, hs, decide_false,
            Bool.false_eq_true, ↓reduceIte, hf, val_forList, hfun]
          rw [show e :: acc = [e] ++ acc from rfl, foldl_prepend]

/-- Section 2.2: if `M` satisfies the recurrence, the backtracking from a vertex `v`, with fuel
larger than the height of `T_v`, returns a backtracking trace of `M` from `v`
(`DynamicProgramming.Trace`). -/
theorem backtrack_trace {t : PhyloTree} {T : Tables} (hT : T.Correct t)
    {B : Address → List (Address × Address)} (hB : ∀ v e, e ∈ B v ↔ e ∈ pairsAt t v)
    {w : Pair → ℕ} {W : Address × Address → ℕ} (hW : ∀ e ∈ EdgeAbove.candidates t, W e = w e)
    {M : Address → ℕ} (hM : Array t w M) :
    ∀ (n : ℕ) (v : Address), v ∈ t.nodes → remainingDepth t v < n →
      Trace t w M v (backtrack T B W M n v []).val.toFinset := by
  intro n
  induction n with
  | zero => intro v _ h; omega
  | succ n ih =>
    intro v hv hn
    obtain ⟨sub, hsub⟩ := (t.mem_nodes_iff v).mp hv
    have hk := hT.kind v hv
    have hrec := hM v hv
    rw [hsub] at hrec
    cases sub with
    | leaf a =>
      have hk' : T.kind v = .leaf a := by rw [hk]; simp [kindAt, hsub]
      simpa [backtrack, hk'] using Trace.leaf v a hsub
    | fork l r =>
      change M v = max (M (v ++ [false]) + M (v ++ [true])) (s t w M v) at hrec
      have hk' : T.kind v = .fork (v ++ [false]) (v ++ [true]) := by
        rw [hk]; simp [kindAt, hsub]
      have hchild (b : Bool) : Trace t w M (v ++ [b]) (backtrack T B W M n (v ++ [b]) []).val.toFinset := by
        have hmem := PhyloTree.child_mem_nodes hsub b
        exact ih _ hmem (by
          have := remainingDepth_lt hmem (List.prefix_append _ _) (by simp)
          omega)
      by_cases hs : M (v ++ [false]) + M (v ++ [true]) = M v
      · -- first case of Equation (2): continue at the two children
        have hval : (backtrack T B W M (n + 1) v []).val =
            (backtrack T B W M n (v ++ [true]) []).val ++
              (backtrack T B W M n (v ++ [false]) []).val := by
          simp only [backtrack, val_bind, val_step, hk', val_steps, hs, decide_true, ↓reduceIte]
          rw [backtrack_acc]
        rw [hval, List.toFinset_append, Finset.union_comm]
        exact Trace.fork v l r _ _ hsub (hchild false) (hchild true) hs
      · -- second case: an edge with target `v` attains `M[v] = s(v)`
        have hsv : M v = s t w M v := by
          rw [hrec]; rw [hrec] at hs; omega
        have hne : (pairsAt t v).Nonempty := by
          by_contra h
          rw [Finset.not_nonempty_iff_eq_empty] at h
          have hz : s t w M v = 0 := by simp [s, h]
          rw [hrec, hz] at hs
          omega
        obtain ⟨e₀, he₀, hsup⟩ := Finset.exists_mem_eq_sup (pairsAt t v) hne
          (fun e => w e + sdp t M e)
        have hpv : ∀ e ∈ pairsAt t v, (pairValue T W M e).val = w e + sdp t M e := by
          intro e he
          obtain ⟨hc, _⟩ := Finset.mem_filter.mp he
          have hae := (Finset.mem_filter.mp hc).2
          rw [val_pairValue hT hae, hW e hc, hanging_score t M e hae]
        obtain ⟨e, hfound⟩ := findPair_complete T W M (M v) (B v)
          ⟨e₀, (hB v e₀).mpr he₀, by rw [hpv e₀ he₀, hsv]; exact hsup.symm⟩
        obtain ⟨heB, hev⟩ := findPair_sound T W M (M v) (B v) e hfound
        have he := (hB v e).mp heB
        obtain ⟨hc, htarget⟩ := Finset.mem_filter.mp he
        have hae := (Finset.mem_filter.mp hc).2
        obtain ⟨hnd, hmem⟩ := hangingList_spec hT hae
        have hfun : (fun (acc : List (Address × Address)) r =>
            (backtrack T B W M n r acc).val) =
            fun acc r => (backtrack T B W M n r []).val ++ acc := by
          funext acc r
          exact backtrack_acc T B W M n r acc
        have hval : (backtrack T B W M (n + 1) v []).val =
            (hangingList T e).val.foldl
              (fun acc r => (backtrack T B W M n r []).val ++ acc) [e] := by
          simp only [backtrack, val_bind, val_step, hk', val_steps, hs, decide_false,
            Bool.false_eq_true, ↓reduceIte, hfound, val_forList, hfun]
        have hL : (hangingList T e).val.toFinset = hanging t e := by
          ext r
          simp [hmem]
        rw [hval, toFinset_foldl_prepend, hL]
        have hset : ([e] : List (Address × Address)).toFinset ∪
            (hanging t e).biUnion (fun r => (backtrack T B W M n r []).val.toFinset) =
              insert e ((hanging t e).biUnion
                fun r => (backtrack T B W M n r []).val.toFinset) := by
          ext x
          simp
        rw [hset]
        refine Trace.gall v e _ he (fun r hr => ?_) ?_
        · -- continue at the roots of the subtrees hanging off the cycle of `e`
          have hgeo := frontier_below (EdgeAbove.footprint_region t e hae) hr
          have hrn := (Finset.mem_filter.mp hr).1
          exact ih r hrn (by
            have := remainingDepth_lt hrn (htarget ▸ hgeo.1) (htarget ▸ hgeo.2)
            omega)
        · rw [← hpv e he, hev]

/-- The subtrees below the two children of `v` are disjoint and lie strictly below `v`. -/
theorem cone_children {t : PhyloTree} {v : Address} :
    Disjoint (cone t (v ++ [false])) (cone t (v ++ [true])) ∧
      cone t (v ++ [false]) ∪ cone t (v ++ [true]) ⊆ (cone t v).erase v := by
  refine ⟨Finset.disjoint_left.mpr fun x h1 h2 =>
    child_cones_disjoint v ⟨x, (mem_cone.mp h1).2, (mem_cone.mp h2).2⟩, ?_⟩
  intro x hx
  have hb : ∃ b : Bool, x ∈ t.nodes ∧ v ++ [b] <+: x := by
    rcases Finset.mem_union.mp hx with h | h
    · exact ⟨false, mem_cone.mp h⟩
    · exact ⟨true, mem_cone.mp h⟩
  obtain ⟨b, hxn, hbx⟩ := hb
  refine Finset.mem_erase.mpr ⟨?_, mem_cone.mpr ⟨hxn, (List.prefix_append _ _).trans hbx⟩⟩
  intro h
  rw [h] at hbx
  have := hbx.length_le
  simp at this

/-- The subtrees hanging off the cycle of a pair with target `v` are disjoint and lie strictly
below `v`. -/
theorem cone_hanging {t : PhyloTree} {e : Address × Address} (he : EdgeAbove.Admissible t e) :
    (↑(hanging t e) : Set Address).PairwiseDisjoint (cone t) ∧
      (hanging t e).biUnion (cone t) ⊆ (cone t (EdgeAbove.target e)).erase (EdgeAbove.target e) := by
  have hS := EdgeAbove.footprint_region t e he
  refine ⟨fun r hr r' hr' hne => Finset.disjoint_left.mpr fun x h1 h2 => hne ?_, ?_⟩
  · rcases List.prefix_or_prefix_of_prefix (mem_cone.mp h1).2 (mem_cone.mp h2).2 with h | h
    · exact frontier_antichain hS hr hr' h
    · exact (frontier_antichain hS hr' hr h).symm
  · intro x hx
    obtain ⟨r, hr, hxr⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨hxn, hrx⟩ := mem_cone.mp hxr
    have hgeo := frontier_below hS hr
    refine Finset.mem_erase.mpr ⟨fun h => hgeo.2 ?_, mem_cone.mpr ⟨hxn, hgeo.1.trans hrx⟩⟩
    rw [h] at hrx
    exact prefix_antisymm hgeo.1 hrx

/-- The operations the backtracking performs at the vertex `x` itself, at most: the tests of
Equation (2), the scan of the bucket of `x`, and the walks of the pair found. -/
def ownCost (t : PhyloTree) (B : Address → List (Address × Address)) (x : Address) : ℕ :=
  15 + 7 * t.nodes.card + (B x).length * (12 + 9 * t.nodes.card)

/-- Section 2.3 for the backtracking: from `v`, it takes at most `ownCost` operations at each
vertex of `T_v`, since the subtrees it continues in are disjoint and lie strictly below `v`. -/
theorem time_backtrack {t : PhyloTree} {T : Tables} (hT : T.Correct t)
    {B : Address → List (Address × Address)} (hB : ∀ v e, e ∈ B v ↔ e ∈ pairsAt t v)
    (W : Address × Address → ℕ) (M : Address → ℕ) :
    ∀ (n : ℕ) (v : Address) (acc : List (Address × Address)), v ∈ t.nodes →
      (backtrack T B W M n v acc).time ≤ ∑ x ∈ cone t v, ownCost t B x := by
  intro n
  induction n with
  | zero => intro v acc _; simp [backtrack]
  | succ n ih =>
    intro v acc hv
    have hvc : v ∈ cone t v := mem_cone.mpr ⟨hv, List.prefix_refl v⟩
    have hsplit : ∑ x ∈ cone t v, ownCost t B x =
        ownCost t B v + ∑ x ∈ (cone t v).erase v, ownCost t B x :=
      (Finset.add_sum_erase _ _ hvc).symm
    rw [hsplit]
    obtain ⟨sub, hsub⟩ := (t.mem_nodes_iff v).mp hv
    have hk := hT.kind v hv
    cases sub with
    | leaf a =>
      have hk' : T.kind v = .leaf a := by rw [hk]; simp [kindAt, hsub]
      simp only [backtrack, time_bind, time_step, val_step, hk', time_pure, ownCost]
      omega
    | fork l r =>
      have hk' : T.kind v = .fork (v ++ [false]) (v ++ [true]) := by
        rw [hk]; simp [kindAt, hsub]
      have hl := PhyloTree.child_mem_nodes hsub false
      have hr := PhyloTree.child_mem_nodes hsub true
      obtain ⟨hdisj, hsubset⟩ := cone_children (t := t) (v := v)
      have hchildren : ∑ x ∈ cone t (v ++ [false]), ownCost t B x +
          ∑ x ∈ cone t (v ++ [true]), ownCost t B x ≤
            ∑ x ∈ (cone t v).erase v, ownCost t B x := by
        rw [← Finset.sum_union hdisj]
        exact Finset.sum_le_sum_of_subset hsubset
      have hown : 7 ≤ ownCost t B v := by unfold ownCost; omega
      have hov : ownCost t B v =
          15 + 7 * t.nodes.card + (B v).length * (12 + 9 * t.nodes.card) := rfl
      by_cases hs : M (v ++ [false]) + M (v ++ [true]) = M v
      · simp only [backtrack, time_bind, time_step, val_step, hk', time_steps, val_steps, hs,
          decide_true, ↓reduceIte]
        have h1 := ih (v ++ [false]) acc hl
        have h2 := ih (v ++ [true]) (backtrack T B W M n (v ++ [false]) acc).val hr
        omega
      · -- the bucket of `v`, then the subtrees hanging off the cycle of the pair found
        have hfind : (findPair T W M (M v) (B v)).time ≤
            (B v).length * (12 + 9 * t.nodes.card) := by
          calc
            _ ≤ ((B v).map fun e => (pairValue T W M e).time + 2).sum :=
              time_findPair T W M (M v) (B v)
            _ ≤ ((B v).map fun _ => 12 + 9 * t.nodes.card).sum := by
              apply List.sum_le_sum
              intro e he
              have hae := (Finset.mem_filter.mp
                (Finset.mem_filter.mp ((hB v e).mp he)).1).2
              have := time_pairValue hT hae W M
              omega
            _ = _ := by rw [sum_map_const_nat]
        cases hf : (findPair T W M (M v) (B v)).val with
        | none =>
          simp only [backtrack, time_bind, time_step, val_step, hk', time_steps, val_steps, hs,
            decide_false, Bool.false_eq_true, ↓reduceIte, hf, time_pure]
          omega
        | some e =>
          obtain ⟨heB, -⟩ := findPair_sound T W M (M v) (B v) e hf
          have he := (hB v e).mp heB
          obtain ⟨hc, htarget⟩ := Finset.mem_filter.mp he
          have hae := (Finset.mem_filter.mp hc).2
          obtain ⟨hnd, hmem⟩ := hangingList_spec hT hae
          have hlen := length_hangingList hT hae
          have hhl := time_hangingList T e
          obtain ⟨hpd, hsub'⟩ := cone_hanging hae
          rw [htarget] at hsub'
          -- the recursive calls at the hanging subtrees
          have hloop : (forList (fun acc r => backtrack T B W M n r acc) (hangingList T e).val
              (e :: acc)).time ≤ t.nodes.card + ∑ x ∈ (cone t v).erase v, ownCost t B x := by
            calc
              _ ≤ ((hangingList T e).val.map
                  fun r => (∑ x ∈ cone t r, ownCost t B x) + 1).sum := by
                apply time_forList_le
                intro acc' r hr'
                have hrh : r ∈ hanging t e := (hmem r).mp hr'
                exact ih r acc' (Finset.mem_filter.mp hrh).1
              _ = (hangingList T e).val.length +
                  ∑ r ∈ hanging t e, ∑ x ∈ cone t r, ownCost t B x := by
                rw [List.sum_map_add, sum_map_const_nat, ← List.sum_toFinset _ hnd]
                have hL : (hangingList T e).val.toFinset = hanging t e := by
                  ext r; simp [hmem]
                rw [hL]
                ring
              _ ≤ t.nodes.card + ∑ x ∈ (cone t v).erase v, ownCost t B x := by
                rw [← Finset.sum_biUnion hpd]
                exact Nat.add_le_add hlen (Finset.sum_le_sum_of_subset hsub')
          simp only [backtrack, time_bind, time_step, val_step, hk', time_steps, val_steps, hs,
            decide_false, Bool.false_eq_true, ↓reduceIte, hf]
          omega

/-- **CAMUS with backtracking** (Section 2.2), as a program: the array of `camus`, then the
backtracking from the root, with fuel `|V(T)|`, larger than the height of `T`. Returns the pairs
`(u, w)` of the added edges. -/
def camusNetwork (t : PhyloTree) (Q : Multiset Quartet) :
    Timed (List (Address × Address)) := do
  let P ← preprocess t
  let S ← enumerate P.1 Q P.2
  let order ← reverseList P.2
  let M ← fill P.1 S.1 S.2 order
  let N ← forList (fun c _ => step (c + 1)) P.2 0
  backtrack P.1 S.1 S.2 M N [] []

theorem count_eq_length (l : List Address) :
    (forList (fun c _ => step (c + 1)) l 0).val = l.length := by
  have h : ∀ (c : ℕ), l.foldl (fun c _ => c + 1) c = c + l.length := by
    induction l with
    | nil => simp
    | cons a l ih => intro c; simp [ih]; omega
  simp [h]

/-- **Theorem 1** for the network computed by CAMUS. For a well-labelled tree `T` and a multiset
`Q`, the pairs `E` returned by `camusNetwork` form a backtracking trace of the array computed by
`camus`, so the network `Realization.graph t E` is built on `T`, satisfies `M[root]` quartets of
`Q`, and no network built on `T` satisfies more. -/
theorem camusNetwork_optimal {t : PhyloTree} (ht : t.WellLabelled) (Q : Multiset Quartet) :
    let E := (camusNetwork t Q).val.toFinset
    Trace t (edgeWeight t Q) (camus t Q).val [] E ∧
      (Realization.graph t E).AnchoredExtension t ∧
      score Q (novel t Q (Realization.graph t E)) = (camus t Q).val [] ∧
      ∀ N : RootedNetwork, N.AnchoredExtension t →
        score Q (novel t Q N) ≤ score Q (novel t Q (Realization.graph t E)) := by
  intro E
  have hT := preprocess_correct t
  have hpre := preprocess_order t
  obtain ⟨hB, hW⟩ := enumerate_buckets hT Q
  have hM := camus_array ht Q
  have htrace : Trace t (edgeWeight t Q) (camus t Q).val [] E := by
    have hcamus : (camus t Q).val = (fill (preprocess t).val.1
        (enumerate (preprocess t).val.1 Q t.preorder).val.1
        (enumerate (preprocess t).val.1 Q t.preorder).val.2 t.preorder.reverse).val := by
      simp [camus, val_reverseList, hpre]
    have h := backtrack_trace hT (fun v e => (hB v).2 e)
      (fun e he => (hW e he).trans (val_weightScan ht hT Q he)) (hcamus ▸ hM)
      t.nodes.card [] (PhyloTree.root_mem_nodes t) (by
        unfold remainingDepth
        have hle : t.nodes.sup List.length < t.nodes.card := by
          rw [Finset.sup_lt_iff (by
            exact Finset.card_pos.mpr ⟨[], PhyloTree.root_mem_nodes t⟩)]
          intro p hp
          exact PhyloTree.length_lt_card hp
        simp only [List.length_nil, Nat.sub_zero]
        exact hle)
    have hE : E = (backtrack (preprocess t).val.1
        (enumerate (preprocess t).val.1 Q t.preorder).val.1
        (enumerate (preprocess t).val.1 Q t.preorder).val.2
        (camus t Q).val t.nodes.card [] []).val.toFinset := by
      simp only [E, camusNetwork, val_bind, val_reverseList, hpre, count_eq_length,
        PhyloTree.preorder_length]
      rw [hcamus]
    rw [hE, ← hcamus] at *
    exact hcamus ▸ h
  obtain ⟨h1, h2, h3, -⟩ := theorem1 t ht Q _ hM E htrace
  exact ⟨htrace, h1, h2, h3⟩

theorem time_count (l : List Address) :
    (forList (fun c _ => step (c + 1)) l 0).time = 2 * l.length := by
  rw [time_forList_eq _ _ _ (fun _ => 1) (fun _ _ _ => rfl)]
  simp only [sum_map_const_nat]
  ring

/-- The backtracking from the root spends `O(n + |candidates| · n)` operations in all: each
candidate pair is in one bucket (`candidate_visits`). -/
theorem sum_ownCost {t : PhyloTree} {B : Address → List (Address × Address)}
    (hB : ∀ v e, e ∈ B v ↔ e ∈ pairsAt t v) (hnd : ∀ v, (B v).Nodup) :
    ∑ x ∈ cone t [], ownCost t B x = t.nodes.card * (15 + 7 * t.nodes.card) +
      (EdgeAbove.candidates t).card * (12 + 9 * t.nodes.card) := by
  have hcone : cone t [] = t.nodes := by
    ext x
    simp [mem_cone]
  have hlen : ∀ v, (B v).length = (pairsAt t v).card := by
    intro v
    rw [← List.toFinset_card_of_nodup (hnd v)]
    congr 1
    ext e
    simp [hB]
  rw [hcone]
  unfold ownCost
  rw [Finset.sum_add_distrib]
  simp only [hlen, ← Finset.sum_mul, candidate_visits, Finset.sum_const, smul_eq_mul]

/-- **Section 2.3 with backtracking.** For a well-labelled tree `T` with `n` leaves and a
multiset `Q` with `|Q|` distinct quartets, `camusNetwork t Q`, which computes the array and
backtracks the network, performs at most `700 n² (|Q| + n)` operations. -/
theorem camusNetwork_time {t : PhyloTree} (ht : t.WellLabelled) (Q : Multiset Quartet) :
    (camusNetwork t Q).time ≤ 700 * t.taxa.card ^ 2 * (Q.toFinset.card + t.taxa.card) := by
  have hT := preprocess_correct t
  have hpre := preprocess_order t
  obtain ⟨hB, -⟩ := enumerate_buckets hT Q
  have t1 := preprocess_time t
  have t2 := time_enumerate hT Q
  have t3 := time_reverseList t.preorder
  have t4 := time_fill hT (fun v e => (hB v).2 e) (fun v => (hB v).1)
    (enumerate (preprocess t).val.1 Q t.preorder).val.2
  have t5 := time_count t.preorder
  have t6 := time_backtrack hT (fun v e => (hB v).2 e)
    (enumerate (preprocess t).val.1 Q t.preorder).val.2
    (fill (preprocess t).val.1 (enumerate (preprocess t).val.1 Q t.preorder).val.1
      (enumerate (preprocess t).val.1 Q t.preorder).val.2 t.preorder.reverse).val
    t.preorder.length [] [] (PhyloTree.root_mem_nodes t)
  rw [sum_ownCost (fun v e => (hB v).2 e) (fun v => (hB v).1)] at t6
  simp only [camusNetwork, time_bind, val_reverseList]
  rw [hpre, count_eq_length]
  rw [PhyloTree.preorder_length] at t3 t5
  have hnodes := t.nodes_count
  have htaxa : t.taxa.card = t.labels.length := List.toFinset_card_of_nodup ht
  have hn := t.labels_nonempty
  have hc := candidates_bound t
  rw [htaxa]
  set N := t.nodes.card
  set n := t.labels.length
  set C := (EdgeAbove.candidates t).card
  set q := Q.toFinset.card
  have hN : N ≤ 2 * n := by omega
  have hN2 : N ^ 2 ≤ 4 * n ^ 2 := by
    have := Nat.mul_le_mul hN hN
    nlinarith
  have hC : C ≤ 4 * n ^ 2 := le_trans hc hN2
  have hn2 : n ≤ n ^ 2 := by nlinarith
  have hn3 : n ^ 2 ≤ n ^ 3 := by nlinarith
  have hCN : C * N ≤ 8 * n ^ 3 := by
    have := Nat.mul_le_mul hC hN
    have h : 4 * n ^ 2 * (2 * n) = 8 * n ^ 3 := by ring
    linarith
  have hCq : C * q ≤ 4 * (n ^ 2 * q) := by
    have := Nat.mul_le_mul_right q hC
    have h : 4 * n ^ 2 * q = 4 * (n ^ 2 * q) := by ring
    linarith
  have hNN : N * N ≤ 4 * n ^ 2 := by
    have := Nat.mul_le_mul hN hN
    have h : 2 * n * (2 * n) = 4 * n ^ 2 := by ring
    linarith
  have hgoal : 700 * n ^ 2 * (q + n) = 700 * (n ^ 2 * q) + 700 * n ^ 3 := by ring
  have e2 : C * (133 * q + 4) = 133 * (C * q) + 4 * C := by ring
  have e4 : C * (12 + 9 * N) = 12 * C + 9 * (C * N) := by ring
  have e6 : N * (15 + 7 * N) = 15 * N + 7 * (N * N) := by ring
  rw [hgoal]
  rw [e2] at t2
  rw [e4] at t4
  rw [e6, e4] at t6
  linarith

end Complexity

end Camus
