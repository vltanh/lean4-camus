module

public import Camus.Complexity.Operations
public import Camus.Network.Clades
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# The single site model of Warnow, Tabatabaee and Evans

Section 3.2 of the paper argues that its SNP pipeline is statistically consistent under the model
of Warnow, Tabatabaee and Evans (2025), Section 4.2 ("WTE"), in which every site picks a tree
displayed by the network `N` and evolves down it. This file defines that model on a rooted binary
level-1 network `N`, with any finite set of states `σ` (WTE use the four nucleotides). Its
parameters, with the constraints that WTE list (`External.SiteParameters`), are a positive
transmission probability `j(e)` on each edge `e` into a reticulation, summing to 1 at each
reticulation; a positive distribution of the state at the root; and substitution probabilities
`p(e, s, s')`, a stochastic matrix on each edge, with `p(e, s, s') > 0` for `s ≠ s'` on the tree
edges (the edges into vertices of indegree 1) and no change on the reticulation edges. The model
(`External.SiteModel`) also asks `p(e, s, s) > 0` on the tree edges, as WTE's Theorem 7 does. A
site history (`External.SiteHistory`) is a switching `S` of `N` (the tree the site evolves down,
before the clean-up of Definition 1) and a state at every vertex. Its probability
(`External.SiteParameters.weight`) is the product of the transmission probabilities of the edges
of `S` into reticulations, the probability of the root state, and the substitution probabilities
along the edges of `S`; these probabilities sum to 1 (`External.SiteParameters.weight_sum`),
which makes the model a distribution on histories (`External.SiteParameters.pmf`).

An SNP, in WTE's sense (the sites that their Oracle selects), is a history whose state changes on
exactly one edge `(x, y)` of its switching (`External.SiteHistory.IsSNP`). Its quartets are the
quartets on taxa of `N` cut by the clade below `y` in `S` (`External.SiteHistory.quartets`): these
are the quartets `ab|cd` with `a`, `b` in one state and `c`, `d` in the other that the paper's
pipeline adds to `Q` (`External.SiteHistory.quartets_eq_pattern`). Every quartet of an SNP is
displayed by `N` (`External.SiteHistory.displays_of_mem_quartets`), and every quartet displayed by
`N` is a quartet of some SNP of positive probability (`External.SiteModel.exists_snp`); this is
the step of the proof of WTE's Theorem 6 that the paper's Section 3.2 relies on, for quartets
instead of clades. `External.SiteModel.uniform` is a model on every network, so the hypotheses are
not vacuous.

## Main results

* `External.SiteParameters`: the parameters of WTE's single site model, with the constraints of
  their Section 4.2.
* `External.SiteModel`: the model, with `p(e, s, s) > 0` on the tree edges.
* `External.SiteHistory`: a switching and a state at every vertex.
* `External.SiteParameters.weight`, `External.SiteParameters.weight_sum`,
  `External.SiteParameters.pmf`, `External.SiteParameters.law`: the probability of a history, and
  the law of a site.
* `External.SiteHistory.IsSNP`, `External.SiteHistory.quartets`: WTE's SNPs and the quartets
  they contribute to `Q`.
* `External.SiteHistory.quartets_eq_pattern`: these are the quartets of the paper's pipeline,
  read off the states at the leaves.
* `External.SiteHistory.displays_of_mem_quartets`: every quartet of an SNP is displayed by `N`.
* `External.SiteModel.exists_snp`: every quartet displayed by `N` is a quartet of an SNP of
  positive probability.
* `External.SiteModel.uniform`: a model on every network.

## Proof (WTE's, for Theorem 6)

WTE's argument, adapted to quartets: if `N` displays `q`, some switching `S` has an edge `(x, y)`
into a vertex of indegree 1 whose clade below `y` cuts `q`
(`RootedNetwork.displays_iff_treeEdge_cladeBelow`). WTE: "the probability of a character
evolving down T is strictly positive, since 0 < j(e) < 1 for all reticulation edges"; "it is easy
to see that the probability that c changes on e and no other edge in T is strictly positive";
and "if c evolves down T and changes only on edge e, then c is two-state and homoplasy-free, and
hence is an SNP". The history that follows `S`, takes one state above `(x, y)` and another below
it (`External.SiteHistory.snp`), has positive probability
(`External.SiteModel.weight_snp_pos`): the transmission and root probabilities are positive, the
substitution on `(x, y)` is a change on a tree edge, and on every other edge of `S` the state
stays the same, which has probability 1 on a reticulation edge and `p(f, s, s)` on a tree edge
`f`. WTE's list of constraints does not make `p(f, s, s)` positive, which their "it is easy to
see" needs: with `p(f, s, s) = 0` the state must change on `f`, and the step fails
(`External.theorem6_step_needs_stay`). Their Theorem 7 assumes it (`0 < p_on ≤ p(e, s, s)`), and
so does `External.SiteModel` (`stay_pos`).

The probabilities sum to 1: for a fixed switching, the substitution part is a Markov chain on a
rooted tree, and summing out the state of a deepest vertex removes its edge
(`External.markov_tree_sum`); the switchings are the independent choices of one incoming edge at
each vertex (`External.Switchings.sum_prod`), and the transmission probabilities at each
reticulation sum to 1.
-/

@[expose] public section

open scoped NNReal ENNReal
open Finset

namespace Camus

namespace Quartet

/-- The quartets whose four taxa lie in `X`. -/
noncomputable def onTaxa (X : Finset ℕ) : Finset Quartet :=
  (X ×ˢ (X ×ˢ (X ×ˢ (X ×ˢ (Finset.univ : Finset (Fin 3)))))).preimage Complexity.quartetKey
    Complexity.quartetKey_injective.injOn

theorem mem_onTaxa {X : Finset ℕ} {q : Quartet} : q ∈ onTaxa X ↔ q.taxa ⊆ X := by
  simp only [onTaxa, Finset.mem_preimage, Complexity.quartetKey, Finset.mem_product,
    Finset.mem_univ, and_true, taxa, Finset.insert_subset_iff, Finset.singleton_subset_iff]

end Quartet

namespace External

section MarkovTree

variable {V σ : Type*} [Fintype V] [DecidableEq V] [Fintype σ]

/-- Summing out the state at one vertex `b`: if `G`, `k₁` and `k₂` do not depend on the state at
`b`, and the rows `k₁ f` and `k₂ f` have the same total, then weighting `G` by `k₁` or by `k₂` at
the state of `b` gives the same sum over the state functions `f`. -/
theorem sum_mul_coordinate (b : V) (G : (V → σ) → ℝ≥0) (k₁ k₂ : (V → σ) → σ → ℝ≥0)
    (hG : ∀ f s, G (Function.update f b s) = G f)
    (hk₁ : ∀ f s, k₁ (Function.update f b s) = k₁ f)
    (hk₂ : ∀ f s, k₂ (Function.update f b s) = k₂ f)
    (hk : ∀ f, ∑ s, k₁ f s = ∑ s, k₂ f s) :
    ∑ f, G f * k₁ f (f b) = ∑ f, G f * k₂ f (f b) := by
  rcases isEmpty_or_nonempty σ with hσ | ⟨⟨s₀⟩⟩
  · have : IsEmpty (V → σ) := ⟨fun f => hσ.false (f b)⟩
    simp
  let e := Equiv.funSplitAt b σ
  -- the state function `e.symm (s, g)` is `e.symm (s₀, g)` with the state at `b` set to `s`
  have hupd : ∀ s g, e.symm (s, g) = Function.update (e.symm (s₀, g)) b s := by
    intro s g
    funext j
    by_cases hj : j = b
    · subst hj
      simp [e, Equiv.funSplitAt_symm_apply]
    · simp [e, Equiv.funSplitAt_symm_apply, hj]
  have hb : ∀ s g, e.symm (s, g) b = s := by
    intro s g
    simp [e, Equiv.funSplitAt_symm_apply]
  -- both sides are sums over the other states of `G` times the total of `k₁` or `k₂`
  have key : ∀ k : (V → σ) → σ → ℝ≥0, (∀ f s, k (Function.update f b s) = k f) →
      ∑ f, G f * k f (f b) =
        ∑ g : {j // j ≠ b} → σ, G (e.symm (s₀, g)) * ∑ s, k (e.symm (s₀, g)) s := by
    intro k hk
    rw [← e.symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hb, hupd, hG, hk]
  rw [key k₁ hk₁, key k₂ hk₂]
  exact Finset.sum_congr rfl fun g _ => by rw [hk]

/-- A Markov chain on a rooted tree: the tree is given by its edge set `E`, in which every vertex
other than the root `r` is the head of exactly one edge and the root of none, and `rank`
increases along the edges. The root state has law `π`, and the state at the head of each edge `e`
is drawn from the row `K e` of the state at its tail. Then the probabilities of the state
functions sum to 1. -/
theorem markov_tree_sum (E : Finset (V × V)) (r : V) (rank : V → ℕ)
    (hrank : ∀ e ∈ E, rank e.1 < rank e.2)
    (hhead : ∀ e ∈ E, ∀ e' ∈ E, e.2 = e'.2 → e = e')
    (hroot : ∀ e ∈ E, e.2 ≠ r)
    (hcover : ∀ v, v ≠ r → ∃ e ∈ E, e.2 = v)
    (π : σ → ℝ≥0) (hπ : ∑ s, π s = 1) (K : V × V → σ → σ → ℝ≥0)
    (hK : ∀ e ∈ E, ∀ s, ∑ s', K e s s' = 1) :
    ∑ f : V → σ, π (f r) * ∏ e ∈ E, K e (f e.1) (f e.2) = 1 := by
  classical
  -- the vertices other than the root that are the head of no edge of `F` get the law `π`
  let free : Finset (V × V) → Finset V := fun F =>
    univ.filter fun v => v ≠ r ∧ ∀ e ∈ F, e.2 ≠ v
  have claim : ∀ n, ∀ F ⊆ E, F.card = n →
      ∑ f : V → σ, π (f r) * (∏ e ∈ F, K e (f e.1) (f e.2)) * ∏ v ∈ free F, π (f v) = 1 := by
    intro n
    induction n with
    | zero =>
      intro F _ hF
      rw [Finset.card_eq_zero.mp hF]
      have hfree : free ∅ = univ.erase r := by
        ext v
        simp [free]
      simp only [Finset.prod_empty, mul_one, hfree]
      calc ∑ f : V → σ, π (f r) * ∏ v ∈ univ.erase r, π (f v)
          = ∑ f : V → σ, ∏ v, π (f v) := by
            refine Finset.sum_congr rfl fun f _ => ?_
            rw [Finset.mul_prod_erase _ (fun v => π (f v)) (Finset.mem_univ r)]
        _ = ∏ _v : V, ∑ s, π s := (Fintype.prod_sum fun _ s => π s).symm
        _ = 1 := by simp [hπ]
    | succ n ih =>
      intro F hFE hF
      have hne : F.Nonempty := Finset.card_pos.mp (by omega)
      -- remove an edge whose head has the largest rank
      obtain ⟨e₀, he₀, hmax⟩ := Finset.exists_max_image F (fun e => rank e.2) hne
      set a := e₀.1
      set b := e₀.2
      have hab : a ≠ b := fun h => by
        have := hrank e₀ (hFE he₀)
        rw [show e₀.1 = e₀.2 from h] at this
        exact lt_irrefl _ this
      have hbr : b ≠ r := hroot e₀ (hFE he₀)
      set F' := F.erase e₀
      have hF' : F'.card = n := by
        rw [Finset.card_erase_of_mem he₀]
        omega
      have hheadF' : ∀ e ∈ F', e.2 ≠ b := by
        intro e he heb
        exact (Finset.mem_erase.mp he).1 (hhead e (hFE (Finset.mem_of_mem_erase he)) e₀
          (hFE he₀) heb)
      have htailF' : ∀ e ∈ F', e.1 ≠ b := by
        intro e he heb
        have h1 := hrank e (hFE (Finset.mem_of_mem_erase he))
        have h2 := hmax e (Finset.mem_of_mem_erase he)
        rw [heb] at h1
        exact absurd h2 (not_le.mpr h1)
      have hfree : free F' = insert b (free F) := by
        ext v
        simp only [free, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        constructor
        · rintro ⟨hvr, hv⟩
          by_cases hvb : v = b
          · exact Or.inl hvb
          · refine Or.inr ⟨hvr, fun e he hev => ?_⟩
            by_cases hee : e = e₀
            · exact hvb (by subst hee; exact hev.symm)
            · exact hv e (Finset.mem_erase.mpr ⟨hee, he⟩) hev
        · rintro (rfl | ⟨hvr, hv⟩)
          · exact ⟨hbr, hheadF'⟩
          · exact ⟨hvr, fun e he => hv e (Finset.mem_of_mem_erase he)⟩
      have hbfree : b ∉ free F := by
        simp only [free, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_forall]
        exact fun _ => ⟨e₀, he₀, fun h => h rfl⟩
      -- the part of the summand that does not involve the state at `b`
      let G : (V → σ) → ℝ≥0 := fun f =>
        π (f r) * (∏ e ∈ F', K e (f e.1) (f e.2)) * ∏ v ∈ free F, π (f v)
      have hG : ∀ f s, G (Function.update f b s) = G f := by
        intro f s
        have h1 : Function.update f b s r = f r := Function.update_of_ne hbr.symm _ _
        have h2 : ∏ e ∈ F', K e (Function.update f b s e.1) (Function.update f b s e.2) =
            ∏ e ∈ F', K e (f e.1) (f e.2) := by
          refine Finset.prod_congr rfl fun e he => ?_
          rw [Function.update_of_ne (htailF' e he), Function.update_of_ne (hheadF' e he)]
        have h3 : ∏ v ∈ free F, π (Function.update f b s v) = ∏ v ∈ free F, π (f v) := by
          refine Finset.prod_congr rfl fun v hv => ?_
          have hvb : v ≠ b := fun h => hbfree (by rw [← h]; exact hv)
          rw [Function.update_of_ne hvb]
        simp only [G, h1, h2, h3]
      -- summing out the state at `b` replaces the row of `e₀` by the law `π`
      have hstep := sum_mul_coordinate b G (fun f s => K e₀ (f a) s) (fun _ s => π s) hG
        (fun f s => by rw [Function.update_of_ne hab]) (fun _ _ => rfl)
        (fun f => by rw [hK e₀ (hFE he₀), hπ])
      calc ∑ f : V → σ, π (f r) * (∏ e ∈ F, K e (f e.1) (f e.2)) * ∏ v ∈ free F, π (f v)
          = ∑ f : V → σ, G f * K e₀ (f a) (f b) := by
            refine Finset.sum_congr rfl fun f _ => ?_
            simp only [G]
            rw [← Finset.mul_prod_erase F _ he₀]
            ring
        _ = ∑ f : V → σ, G f * π (f b) := hstep
        _ = ∑ f : V → σ, π (f r) * (∏ e ∈ F', K e (f e.1) (f e.2)) *
              ∏ v ∈ free F', π (f v) := by
            refine Finset.sum_congr rfl fun f _ => ?_
            simp only [G]
            rw [hfree, Finset.prod_insert hbfree]
            ring
        _ = 1 := ih F' ((Finset.erase_subset _ _).trans hFE) hF'
  -- with `F = E`, every vertex other than the root is the head of an edge
  have hfreeE : free E = ∅ := by
    ext v
    simp only [free, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
      iff_false, not_and, not_forall, not_not]
    intro hvr
    obtain ⟨e, he, hev⟩ := hcover v hvr
    exact ⟨e, he, hev⟩
  have h := claim E.card E (Finset.Subset.refl _) rfl
  simpa only [hfreeE, Finset.prod_empty, mul_one] using h

end MarkovTree

/-- The parameters of WTE's single site model (their Section 4.2) on the network `N`, with
states in the finite type `σ` (WTE use the four nucleotides), and exactly the constraints that
WTE list. A tree edge is an edge into a vertex of indegree 1, a reticulation edge an edge into a
vertex of indegree 2.
* `transmission e` is the transmission probability j(e) of an edge `e` into a reticulation:
  positive, and summing to 1 over the edges into each reticulation (so also below 1, as WTE ask).
* `root s` is the probability of the state `s` at the root, positive for every state.
* `substitution e s s'` is the probability p(e, s, s') of the state `s'` at the head of `e` given
  the state `s` at its tail: each row sums to 1, a change `s ≠ s'` has positive probability on a
  tree edge, and probability 0 on a reticulation edge.

These constraints do not give the step of the proof of WTE's Theorem 6 that every clade, or
quartet, of `N` comes from an SNP of positive probability
(`External.theorem6_step_needs_stay`); `External.SiteModel` adds the missing one. -/
structure SiteParameters (N : RootedNetwork) (σ : Type*) [Fintype σ] where
  transmission : ℕ × ℕ → ℝ≥0
  transmission_pos : ∀ e ∈ N.edges, N.indegree e.2 = 2 → 0 < transmission e
  transmission_sum : ∀ v ∈ N.vertices, N.indegree v = 2 →
    ∑ e ∈ N.edges.filter (fun e => e.2 = v), transmission e = 1
  root : σ → ℝ≥0
  root_pos : ∀ s, 0 < root s
  root_sum : ∑ s, root s = 1
  substitution : ℕ × ℕ → σ → σ → ℝ≥0
  substitution_sum : ∀ e ∈ N.edges, ∀ s, ∑ s', substitution e s s' = 1
  change_pos : ∀ e ∈ N.edges, N.indegree e.2 = 1 → ∀ s s', s ≠ s' → 0 < substitution e s s'
  no_change : ∀ e ∈ N.edges, N.indegree e.2 = 2 → ∀ s s', s ≠ s' → substitution e s s' = 0

/-- WTE's single site model (their Section 4.2) on the network `N`: the parameters of
`External.SiteParameters`, and `stay_pos`: no change, p(e, s, s), has positive probability on a
tree edge. WTE's list of constraints does not state this, but the proof of their Theorem 6 needs
it ("it is easy to see that the probability that c changes on e and no other edge in T is
strictly positive"; without it the step fails, `External.theorem6_step_needs_stay`), and their
Theorem 7 assumes it (`0 < p_on ≤ p(e, s, s)`). -/
structure SiteModel (N : RootedNetwork) (σ : Type*) [Fintype σ] extends SiteParameters N σ where
  stay_pos : ∀ e ∈ N.edges, N.indegree e.2 = 1 → ∀ s, 0 < substitution e s s

/-- A site history on `N`: the switching `S` of `N` that the site evolves down (WTE: "each
character essentially picks a tree in T_N down which to evolve"), and a state at every vertex.
The states at numbers that are not vertices of `N` play no role; they are those of the root, so
that a history is determined by finitely many states. -/
@[ext]
structure SiteHistory (N : RootedNetwork) (σ : Type*) where
  switching : Finset (ℕ × ℕ)
  state : ℕ → σ
  isSwitching : N.Switching switching
  state_off : ∀ x ∉ N.vertices, state x = state N.root

/-- The root of a rooted binary level-1 network is one of its vertices. -/
theorem root_mem_vertices {N : RootedNetwork} (hN : N.RootedBinaryLevelOne) :
    N.root ∈ N.vertices := hN.1

namespace SiteHistory

variable {N : RootedNetwork} {σ : Type*}

/-- A history is determined by its switching and its states at the root and at the vertices. -/
theorem code_injective :
    Function.Injective (fun h : SiteHistory N σ =>
      ((⟨h.switching, Finset.mem_powerset.mpr h.isSwitching.1⟩ : N.edges.powerset),
        fun x : (insert N.root N.vertices : Finset ℕ) => h.state x)) := by
  intro h h' heq
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at heq
  obtain ⟨hS, hst⟩ := heq
  have hroot : h.state N.root = h'.state N.root :=
    congrFun hst ⟨N.root, Finset.mem_insert_self _ _⟩
  ext1
  · exact hS
  · funext x
    by_cases hx : x ∈ N.vertices
    · exact congrFun hst ⟨x, Finset.mem_insert_of_mem hx⟩
    · rw [h.state_off x hx, h'.state_off x hx, hroot]

noncomputable instance [Fintype σ] : Fintype (SiteHistory N σ) :=
  Fintype.ofInjective _ code_injective

/-- The state function on all of `ℕ` that extends the states `f` of the vertices of `N` by the
state of the root. -/
noncomputable def extend (hr : N.root ∈ N.vertices) (f : N.vertices → σ) (x : ℕ) : σ :=
  if hx : x ∈ N.vertices then f ⟨x, hx⟩ else f ⟨N.root, hr⟩

theorem extend_of_mem (hr : N.root ∈ N.vertices) (f : N.vertices → σ) {x : ℕ}
    (hx : x ∈ N.vertices) : extend hr f x = f ⟨x, hx⟩ := dite_eq_left hx

/-- When the root of `N` is a vertex, a history is a switching and a state for every vertex. -/
noncomputable def equivProd (hr : N.root ∈ N.vertices) :
    SiteHistory N σ ≃ {S // N.Switching S} × (N.vertices → σ) where
  toFun h := (⟨h.switching, h.isSwitching⟩, fun v => h.state v)
  invFun p := ⟨p.1.1, extend hr p.2, p.1.2, fun x hx => by
    rw [extend, dite_eq_right hx, extend_of_mem hr _ hr]⟩
  left_inv h := by
    ext1
    · rfl
    · funext x
      by_cases hx : x ∈ N.vertices
      · exact extend_of_mem hr _ hx
      · simp only [extend, dite_eq_right hx]
        exact (h.state_off x hx).symm
  right_inv p := by
    ext v
    · rfl
    · exact extend_of_mem hr _ v.2

end SiteHistory

namespace Switchings

variable {N : RootedNetwork}

noncomputable instance : Fintype {S // N.Switching S} := by
  classical
  exact Fintype.subtype (N.edges.powerset.filter N.Switching) fun S => by
    simp only [Finset.mem_filter, Finset.mem_powerset, and_iff_right_iff_imp]
    exact fun h => h.1

/-- The vertices of `N` other than the root. -/
abbrev Slot (N : RootedNetwork) := (N.vertices.erase N.root : Finset ℕ)

/-- The edges of `N` into the vertex `v`. -/
abbrev Into (N : RootedNetwork) (v : Slot N) := (N.edges.filter (fun e => e.2 = v.1) : Finset _)

/-- The head of an edge of a rooted binary level-1 network is a vertex other than the root. -/
theorem head_mem_slot (hN : N.RootedBinaryLevelOne) {e : ℕ × ℕ} (he : e ∈ N.edges) :
    e.2 ∈ N.vertices.erase N.root := by
  refine Finset.mem_erase.mpr ⟨fun h => ?_, (hN.2.1 e he).2⟩
  have hz : N.indegree N.root = 0 := hN.2.2.2.1
  have hmem : e ∈ N.edges.filter (fun e => e.2 = N.root) := Finset.mem_filter.mpr ⟨he, h⟩
  rw [RootedNetwork.indegree, Finset.card_eq_zero] at hz
  rw [hz] at hmem
  exact Finset.notMem_empty _ hmem

/-- The edge of the switching `S` into the vertex `v` other than the root. -/
noncomputable def pick (S : {S // N.Switching S}) (v : Slot N) : ℕ × ℕ :=
  Classical.choose (Finset.card_eq_one.mp (S.2.2 v.1 (Finset.mem_erase.mp v.2).2
    (Finset.mem_erase.mp v.2).1))

theorem pick_spec (S : {S // N.Switching S}) (v : Slot N) :
    S.1.filter (fun e => e.2 = v.1) = {pick S v} :=
  Classical.choose_spec (Finset.card_eq_one.mp (S.2.2 v.1 (Finset.mem_erase.mp v.2).2
    (Finset.mem_erase.mp v.2).1))

theorem pick_mem (S : {S // N.Switching S}) (v : Slot N) :
    pick S v ∈ S.1 ∧ (pick S v).2 = v.1 := by
  have h : pick S v ∈ S.1.filter (fun e => e.2 = v.1) := by
    rw [pick_spec]
    exact Finset.mem_singleton_self _
  exact Finset.mem_filter.mp h

/-- The switching that keeps the edge `c v` into each vertex `v` other than the root. -/
noncomputable def ofChoice (c : (v : Slot N) → Into N v) : Finset (ℕ × ℕ) :=
  Finset.univ.image fun v => (c v).1

theorem ofChoice_filter (c : (v : Slot N) → Into N v) (v : Slot N) :
    (ofChoice c).filter (fun e => e.2 = v.1) = {(c v).1} := by
  ext e
  simp only [ofChoice, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · rintro ⟨⟨w, rfl⟩, hw⟩
    have hcw := (Finset.mem_filter.mp (c w).2).2
    have hwv : w = v := Subtype.ext (hcw.symm.trans hw)
    rw [hwv]
  · rintro rfl
    exact ⟨⟨v, rfl⟩, (Finset.mem_filter.mp (c v).2).2⟩

theorem ofChoice_switching (c : (v : Slot N) → Into N v) : N.Switching (ofChoice c) := by
  refine ⟨?_, fun v hv hvr => ?_⟩
  · intro e he
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp he
    exact (Finset.mem_filter.mp (c w).2).1
  · rw [ofChoice_filter c ⟨v, Finset.mem_erase.mpr ⟨hvr, hv⟩⟩, Finset.card_singleton]

/-- The switchings of a rooted binary level-1 network are the independent choices of one
incoming edge at each vertex other than the root. -/
noncomputable def equivChoice (hN : N.RootedBinaryLevelOne) :
    {S // N.Switching S} ≃ ((v : Slot N) → Into N v) where
  toFun S v := ⟨pick S v, Finset.mem_filter.mpr ⟨S.2.1 (pick_mem S v).1, (pick_mem S v).2⟩⟩
  invFun c := ⟨ofChoice c, ofChoice_switching c⟩
  left_inv S := by
    apply Subtype.ext
    ext e
    simp only [ofChoice, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨v, rfl⟩
      exact (pick_mem S v).1
    · intro he
      let v : Slot N := ⟨e.2, head_mem_slot hN (S.2.1 he)⟩
      refine ⟨v, ?_⟩
      have h : e ∈ S.1.filter (fun e' => e'.2 = v.1) := Finset.mem_filter.mpr ⟨he, rfl⟩
      rw [pick_spec] at h
      exact (Finset.mem_singleton.mp h).symm
  right_inv c := by
    funext v
    apply Subtype.ext
    have h := pick_spec ⟨ofChoice c, ofChoice_switching c⟩ v
    rw [ofChoice_filter] at h
    exact (Finset.singleton_inj.mp h).symm

/-- The sum, over the switchings `S`, of the product of the weights `ω e` of the edges of `S` is
the product, over the vertices other than the root, of the total weight of the edges into
them. -/
theorem sum_prod (hN : N.RootedBinaryLevelOne) (ω : ℕ × ℕ → ℝ≥0) :
    ∑ S : {S // N.Switching S}, ∏ e ∈ S.1, ω e =
      ∏ v ∈ N.vertices.erase N.root, ∑ e ∈ N.edges.filter (fun e => e.2 = v), ω e := by
  rw [← (equivChoice hN).symm.sum_comp]
  have hprod : ∀ c : (v : Slot N) → Into N v,
      ∏ e ∈ ((equivChoice hN).symm c).1, ω e = ∏ v, ω (c v).1 := by
    intro c
    change ∏ e ∈ ofChoice c, ω e = _
    unfold ofChoice
    rw [Finset.prod_image]
    intro v _ w _ hvw
    have hv := (Finset.mem_filter.mp (c v).2).2
    have hw := (Finset.mem_filter.mp (c w).2).2
    exact Subtype.ext (hv.symm.trans ((congrArg Prod.snd hvw).trans hw))
  simp only [hprod]
  rw [← Fintype.prod_sum (fun (v : Slot N) (e : Into N v) => ω e.1)]
  rw [← Finset.prod_coe_sort (N.vertices.erase N.root)]
  refine Finset.prod_congr rfl fun v _ => ?_
  exact Finset.sum_coe_sort _ ω

end Switchings

namespace SiteParameters

open Switchings

variable {N : RootedNetwork} {σ : Type*} [Fintype σ]

/-- The probability of the history `h` = (S, states) under the model `M`: the product of the
transmission probabilities j(e) of the edges `e` of `S` into reticulations (the probability that
the site evolves down `S`), the probability of the state at the root, and the substitution
probabilities p(e, s, s') along the edges of `S`. -/
noncomputable def weight (M : SiteParameters N σ) (h : SiteHistory N σ) : ℝ≥0 :=
  (∏ e ∈ h.switching.filter (fun e => N.indegree e.2 = 2), M.transmission e) *
    M.root (h.state N.root) *
    ∏ e ∈ h.switching, M.substitution e (h.state e.1) (h.state e.2)

/-- For a fixed switching, the root and substitution part of `weight` sums to 1 over the states
of the vertices: a Markov chain on the tree `S` (`markov_tree_sum`). -/
theorem substitution_sum_states (M : SiteParameters N σ) (hN : N.RootedBinaryLevelOne)
    (S : {S // N.Switching S}) :
    ∑ f : N.vertices → σ, M.root (SiteHistory.extend (root_mem_vertices hN) f N.root) *
      ∏ e ∈ S.1, M.substitution e (SiteHistory.extend (root_mem_vertices hN) f e.1)
        (SiteHistory.extend (root_mem_vertices hN) f e.2) = 1 := by
  classical
  have hmem : ∀ e ∈ S.1, e.1 ∈ N.vertices ∧ e.2 ∈ N.vertices := fun e he => hN.2.1 e (S.2.1 he)
  let r : N.vertices := ⟨N.root, root_mem_vertices hN⟩
  let E : Finset (N.vertices × N.vertices) :=
    Finset.univ.filter fun e => (e.1.1, e.2.1) ∈ S.1
  have hE : ∀ e ∈ E, (e.1.1, e.2.1) ∈ S.1 := fun e he => (Finset.mem_filter.mp he).2
  -- the edges of `S` as edges between vertices of `N`
  have hconv : ∀ f : N.vertices → σ,
      ∏ e ∈ S.1, M.substitution e (SiteHistory.extend (root_mem_vertices hN) f e.1)
        (SiteHistory.extend (root_mem_vertices hN) f e.2) =
      ∏ e ∈ E, M.substitution (e.1.1, e.2.1) (f e.1) (f e.2) := by
    intro f
    symm
    refine Finset.prod_bij' (fun e _ => (e.1.1, e.2.1))
      (fun e he => (⟨e.1, (hmem e he).1⟩, ⟨e.2, (hmem e he).2⟩)) (fun e he => hE e he)
      (fun e he => Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩) (fun e _ => rfl)
      (fun e _ => rfl) (fun e he => ?_)
    rw [SiteHistory.extend_of_mem _ f e.1.2, SiteHistory.extend_of_mem _ f e.2.2]
  simp only [hconv, SiteHistory.extend_of_mem (root_mem_vertices hN) _ (root_mem_vertices hN)]
  refine markov_tree_sum E r (fun v => N.dagRank v.1) ?_ ?_ ?_ ?_ M.root M.root_sum
    (fun e => M.substitution (e.1.1, e.2.1)) ?_
  · -- the number of strict ancestors increases along every edge
    intro e he
    exact RootedNetwork.dagRank_lt hN (S.2.1 (hE e he))
  · -- a switching has one edge into each vertex
    intro e he e' he' heq
    have h1 := RootedNetwork.switching_incoming_unique hN S.2 (hE e he)
      (by rw [show e.2.1 = e'.2.1 from congrArg Subtype.val heq]; exact hE e' he')
    exact Prod.ext (Subtype.ext h1) heq
  · -- and none into the root
    intro e he heq
    exact (Finset.mem_erase.mp (head_mem_slot hN (S.2.1 (hE e he)))).1
      (congrArg Subtype.val heq)
  · intro v hv
    have hvr : v.1 ≠ N.root := fun h => hv (Subtype.ext h)
    let w : Slot N := ⟨v.1, Finset.mem_erase.mpr ⟨hvr, v.2⟩⟩
    obtain ⟨hp, hpv⟩ := pick_mem S w
    refine ⟨(⟨(pick S w).1, (hmem _ hp).1⟩, v), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
      rfl⟩
    change ((pick S w).1, v.1) ∈ S.1
    rw [← hpv]
    exact hp
  · intro e he s
    exact M.substitution_sum _ (S.2.1 (hE e he)) s

/-- The probability of the history with switching `S` and states `f`: the product of the
transmission probabilities of the edges of `S` into reticulations, and the root and substitution
part. -/
theorem weight_equivProd_symm (M : SiteParameters N σ) (hN : N.RootedBinaryLevelOne)
    (S : {S // N.Switching S}) (f : N.vertices → σ) :
    M.weight ((SiteHistory.equivProd (root_mem_vertices hN)).symm (S, f)) =
      (∏ e ∈ S.1.filter (fun e => N.indegree e.2 = 2), M.transmission e) *
        (M.root (SiteHistory.extend (root_mem_vertices hN) f N.root) *
          ∏ e ∈ S.1, M.substitution e (SiteHistory.extend (root_mem_vertices hN) f e.1)
            (SiteHistory.extend (root_mem_vertices hN) f e.2)) := by
  change (∏ e ∈ S.1.filter (fun e => N.indegree e.2 = 2), M.transmission e) *
      M.root (SiteHistory.extend (root_mem_vertices hN) f N.root) *
      ∏ e ∈ S.1, M.substitution e (SiteHistory.extend (root_mem_vertices hN) f e.1)
        (SiteHistory.extend (root_mem_vertices hN) f e.2) = _
  ring

/-- The probabilities of the histories of a rooted binary level-1 network sum to 1. -/
theorem weight_sum (M : SiteParameters N σ) (hN : N.RootedBinaryLevelOne) :
    ∑ h, M.weight h = 1 := by
  classical
  rw [← (SiteHistory.equivProd (σ := σ) (root_mem_vertices hN)).symm.sum_comp,
    Fintype.sum_prod_type]
  -- the transmission part depends only on the switching
  let ω : ℕ × ℕ → ℝ≥0 := fun e => if N.indegree e.2 = 2 then M.transmission e else 1
  have hω : ∀ S : {S // N.Switching S},
      ∏ e ∈ S.1.filter (fun e => N.indegree e.2 = 2), M.transmission e = ∏ e ∈ S.1, ω e := by
    intro S
    simp only [ω, Finset.prod_ite, Finset.prod_const_one, mul_one]
  -- the states sum out to 1 for each switching
  have hstates : ∀ S : {S // N.Switching S}, ∑ f : N.vertices → σ,
      M.weight ((SiteHistory.equivProd (σ := σ) (root_mem_vertices hN)).symm (S, f)) =
        ∏ e ∈ S.1, ω e := by
    intro S
    rw [Finset.sum_congr rfl fun f _ => weight_equivProd_symm M hN S f, ← Finset.mul_sum,
      substitution_sum_states M hN S, mul_one, hω]
  -- the switchings are independent choices at the vertices
  rw [Finset.sum_congr rfl fun S _ => hstates S, sum_prod hN ω]
  refine Finset.prod_eq_one fun v hv => ?_
  obtain ⟨hvr, hvN⟩ := Finset.mem_erase.mp hv
  have hin : N.indegree v = 1 ∨ N.indegree v = 2 := by
    rcases hN.2.2.2.2.2.2.2.2.2.1 v hvN hvr with h | h | h
    exacts [Or.inl h.1, Or.inl h.1, Or.inr h.1]
  rcases hin with h | h
  · -- a vertex of indegree 1 has one incoming edge, of weight 1
    obtain ⟨e, he⟩ := Finset.card_eq_one.mp h
    have hev : e.2 = v := (Finset.mem_filter.mp
      (show e ∈ N.edges.filter (fun e => e.2 = v) from he ▸ Finset.mem_singleton_self e)).2
    rw [he, Finset.sum_singleton]
    simp [ω, hev, h]
  · -- at a reticulation, the transmission probabilities sum to 1
    rw [← M.transmission_sum v hvN h]
    refine Finset.sum_congr rfl fun e he => ?_
    have hev : e.2 = v := (Finset.mem_filter.mp he).2
    simp [ω, hev, h]

/-- The probability that a site evolves down the switching `S₀`: the product of the transmission
probabilities of the edges of `S₀` into reticulations. -/
theorem sum_weight_switching (M : SiteParameters N σ) (hN : N.RootedBinaryLevelOne)
    {S₀ : Finset (ℕ × ℕ)} (hS₀ : N.Switching S₀) :
    ∑ h ∈ Finset.univ.filter (fun h : SiteHistory N σ => h.switching = S₀), M.weight h =
      ∏ e ∈ S₀.filter (fun e => N.indegree e.2 = 2), M.transmission e := by
  classical
  rw [Finset.sum_filter, ← (SiteHistory.equivProd (σ := σ) (root_mem_vertices hN)).symm.sum_comp,
    Fintype.sum_prod_type]
  have hsw : ∀ (S : {S // N.Switching S}) (f : N.vertices → σ),
      ((SiteHistory.equivProd (root_mem_vertices hN)).symm (S, f)).switching = S.1 := fun _ _ => rfl
  simp only [hsw]
  rw [Finset.sum_eq_single (⟨S₀, hS₀⟩ : {S // N.Switching S})]
  · rw [Finset.sum_congr rfl fun f _ => ite_eq_left rfl,
      Finset.sum_congr rfl fun f _ => weight_equivProd_symm M hN _ f, ← Finset.mul_sum,
      substitution_sum_states M hN, mul_one]
  · intro S _ hS
    have hne : S.1 ≠ S₀ := fun h => hS (Subtype.ext h)
    simp [hne]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The distribution of a site under the model `M`, on a rooted binary level-1 network. -/
noncomputable def pmf (M : SiteParameters N σ) (hN : N.RootedBinaryLevelOne) :
    PMF (SiteHistory N σ) :=
  PMF.ofFintype (fun h => (M.weight h : ℝ≥0∞)) (by
    rw [← ENNReal.ofNNReal_finsetSum, M.weight_sum hN, ENNReal.coe_one])

end SiteParameters

namespace SiteHistory

variable {N : RootedNetwork} {σ : Type*}

/-- Histories form a finite set with every subset measurable. -/
instance : MeasurableSpace (SiteHistory N σ) := ⊤

instance : DiscreteMeasurableSpace (SiteHistory N σ) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

end SiteHistory

namespace SiteParameters

variable {N : RootedNetwork} {σ : Type*} [Fintype σ]

/-- The law of a site under the model `M`, as a probability measure on the histories. -/
noncomputable def law (M : SiteParameters N σ) (hN : N.RootedBinaryLevelOne) :
    MeasureTheory.Measure (SiteHistory N σ) :=
  (M.pmf hN).toMeasure

instance (M : SiteParameters N σ) (hN : N.RootedBinaryLevelOne) :
    MeasureTheory.IsProbabilityMeasure (M.law hN) := by
  unfold law
  infer_instance

/-- The law of a set of histories is the sum of their probabilities. -/
theorem law_apply (M : SiteParameters N σ) (hN : N.RootedBinaryLevelOne) (A : Set (SiteHistory N σ))
    [DecidablePred (· ∈ A)] :
    M.law hN A = ((∑ h ∈ Finset.univ.filter (· ∈ A), M.weight h : ℝ≥0) : ℝ≥0∞) := by
  rw [law, PMF.toMeasure_apply_fintype, ENNReal.ofNNReal_finsetSum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun h _ => ?_
  by_cases hA : h ∈ A
  · simp [hA, pmf]
  · simp [hA]

/-- On a reticulation edge the state stays the same with probability 1. -/
theorem stay_eq_one (M : SiteParameters N σ) {e : ℕ × ℕ} (he : e ∈ N.edges)
    (h2 : N.indegree e.2 = 2) (s : σ) : M.substitution e s s = 1 := by
  rw [← M.substitution_sum e he s]
  exact (Finset.sum_eq_single s (fun b _ hb => M.no_change e he h2 s b (Ne.symm hb))
    (by simp)).symm

/-- The head of an edge of a rooted binary level-1 network has indegree 1 or 2. -/
theorem indegree_head (hN : N.RootedBinaryLevelOne) {e : ℕ × ℕ} (he : e ∈ N.edges) :
    N.indegree e.2 = 1 ∨ N.indegree e.2 = 2 := by
  obtain ⟨hr, hv⟩ := Finset.mem_erase.mp (Switchings.head_mem_slot hN he)
  rcases hN.2.2.2.2.2.2.2.2.2.1 e.2 hv hr with h | h | h
  exacts [Or.inl h.1, Or.inl h.1, Or.inr h.1]

end SiteParameters

namespace SiteModel

variable {N : RootedNetwork} {σ : Type*} [Fintype σ]

/-- On every edge of a rooted binary level-1 network, no change has positive probability. -/
theorem stay_pos_edge (M : SiteModel N σ) (hN : N.RootedBinaryLevelOne) {e : ℕ × ℕ}
    (he : e ∈ N.edges) (s : σ) : 0 < M.substitution e s s := by
  rcases SiteParameters.indegree_head hN he with h | h
  · exact M.stay_pos e he h s
  · rw [M.stay_eq_one he h s]
    exact one_pos

end SiteModel

section Below

open Relation

variable {N : RootedNetwork} {S : Finset (ℕ × ℕ)} {x y : ℕ}

/-- In the switching `S` with the edge `(x, y)`, the tail of an edge of `S` other than `(x, y)`
is below `y` exactly when its head is. -/
theorem below_head_iff (hN : N.RootedBinaryLevelOne) (hS : N.Switching S) (hxy : (x, y) ∈ S)
    {u v : ℕ} (huv : (u, v) ∈ S) (hne : (u, v) ≠ (x, y)) :
    ReflTransGen (fun a b => (a, b) ∈ S) y v ↔ ReflTransGen (fun a b => (a, b) ∈ S) y u := by
  constructor
  · intro h
    rcases h.cases_tail with hv | ⟨c, hc, hcv⟩
    · subst hv
      exact absurd (by rw [RootedNetwork.switching_incoming_unique hN hS huv hxy]) hne
    · rwa [RootedNetwork.switching_incoming_unique hN hS huv hcv]
  · exact fun h => h.tail huv

/-- The tail `x` of the edge `(x, y)` is not below `y`: `N` has no directed cycle. -/
theorem not_below_tail (hN : N.RootedBinaryLevelOne) (hS : N.Switching S) (hxy : (x, y) ∈ S) :
    ¬ ReflTransGen (fun a b => (a, b) ∈ S) y x := by
  intro h
  have hN' : ReflTransGen (fun a b => (a, b) ∈ N.edges) y x :=
    ReflTransGen.mono (fun a b hab => hS.1 hab) _ _ h
  exact hN.2.2.1 x (TransGen.head' (hS.1 hxy) hN')

/-- The root is not below the head `y` of an edge. -/
theorem not_below_root (hN : N.RootedBinaryLevelOne) (hS : N.Switching S) (hxy : (x, y) ∈ S) :
    ¬ ReflTransGen (fun a b => (a, b) ∈ S) y N.root := by
  intro h
  rcases h.cases_tail with hr | ⟨c, -, hc⟩
  · exact (Finset.mem_erase.mp (Switchings.head_mem_slot hN (hS.1 hxy))).1 hr.symm
  · exact (Finset.mem_erase.mp (Switchings.head_mem_slot hN (hS.1 hc))).1 rfl

/-- A number that is not a vertex of `N` is not below `y`. -/
theorem not_below_of_not_mem (hN : N.RootedBinaryLevelOne) (hS : N.Switching S)
    (hxy : (x, y) ∈ S) {v : ℕ} (hv : v ∉ N.vertices) :
    ¬ ReflTransGen (fun a b => (a, b) ∈ S) y v := by
  intro h
  rcases h.cases_tail with rfl | ⟨c, -, hc⟩
  · exact hv (hN.2.1 _ (hS.1 hxy)).2
  · exact hv (hN.2.1 _ (hS.1 hc)).2

end Below

namespace SiteHistory

open Relation

variable {N : RootedNetwork} {σ : Type*} [DecidableEq σ]

/-- The edges of the switching on which the state changes. -/
def changes (h : SiteHistory N σ) : Finset (ℕ × ℕ) :=
  h.switching.filter fun e => h.state e.1 ≠ h.state e.2

/-- WTE's SNP: a history whose state changes on exactly one edge of its switching. Such a site is
two-state and homoplasy-free; WTE's Oracle selects these sites from the alignment. -/
def IsSNP (h : SiteHistory N σ) : Prop := h.changes.card = 1

instance : DecidablePred (IsSNP (N := N) (σ := σ)) :=
  fun h => inferInstanceAs (Decidable (h.changes.card = 1))

/-- The quartets on taxa of `N` cut by the clade below `y` in the switching `S`. -/
noncomputable def cutQuartets (N : RootedNetwork) (S : Finset (ℕ × ℕ)) (y : ℕ) :
    Finset Quartet :=
  (Quartet.onTaxa N.taxa).filter fun q => q.cutBy (N.cladeBelow S y) = true

/-- The quartets that the site `h` contributes to `Q`, one copy each: if `h` is an SNP whose state
changes on the edge `(x, y)`, the quartets on taxa of `N` cut by the clade below `y` in its
switching, and none otherwise (the Oracle discards the site). By
`External.SiteHistory.quartets_eq_pattern`, these are the quartets `ab|cd` with `a`, `b` in one
state and `c`, `d` in the other that Section 3.2 of the paper adds to `Q`. -/
noncomputable def quartets (h : SiteHistory N σ) : Finset Quartet :=
  if h.IsSNP then h.changes.biUnion fun e => cutQuartets N h.switching e.2 else ∅

/-- The quartets of an SNP changing on `(x, y)` are those cut by the clade below `y`. -/
theorem quartets_of_changes {h : SiteHistory N σ} {x y : ℕ} (hch : h.changes = {(x, y)}) :
    h.quartets = cutQuartets N h.switching y := by
  have hsnp : h.IsSNP := by
    unfold IsSNP
    rw [hch, Finset.card_singleton]
  rw [quartets, ite_eq_left hsnp, hch, Finset.singleton_biUnion]

/-- The quartets that Section 3.2 of the paper reads off a site: the quartets `ab|cd` on taxa of
`N` such that the leaves `a`, `b` are in one state and `c`, `d` in another. -/
noncomputable def patternQuartets (h : SiteHistory N σ) : Finset Quartet :=
  (Quartet.onTaxa N.taxa).filter fun q =>
    (∀ a ∈ q.sides.1, ∀ b ∈ q.sides.1, h.state (N.leaf a) = h.state (N.leaf b)) ∧
    (∀ a ∈ q.sides.2, ∀ b ∈ q.sides.2, h.state (N.leaf a) = h.state (N.leaf b)) ∧
    (∀ a ∈ q.sides.1, ∀ b ∈ q.sides.2, h.state (N.leaf a) ≠ h.state (N.leaf b))

open scoped Classical in
/-- In an SNP changing on `(x, y)`, every vertex below `y` has the state of `y`, and every other
vertex the state of the root. -/
theorem state_eq_of_changes (hN : N.RootedBinaryLevelOne) {h : SiteHistory N σ} {x y : ℕ}
    (hch : h.changes = {(x, y)}) {v : ℕ} (hv : v ∈ N.vertices) :
    h.state v = if ReflTransGen (fun a b => (a, b) ∈ h.switching) y v then h.state y
      else h.state N.root := by
  classical
  have hxy : (x, y) ∈ h.switching :=
    (Finset.mem_filter.mp (hch ▸ Finset.mem_singleton_self (x, y))).1
  -- induction along the path of the switching from the root
  have hreach := RootedNetwork.switching_reachable hN h.isSwitching hv
  induction hreach with
  | refl =>
    rw [ite_eq_right (not_below_root hN h.isSwitching hxy)]
  | @tail b c _ hbc ih =>
    by_cases he : (b, c) = (x, y)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      rw [ite_eq_left ReflTransGen.refl]
    · have hstay : h.state b = h.state c := by
        by_contra hne
        have hmem : (b, c) ∈ h.changes := Finset.mem_filter.mpr ⟨hbc, hne⟩
        rw [hch] at hmem
        exact he (Finset.mem_singleton.mp hmem)
      rw [← hstay, ih (hN.2.1 _ (h.isSwitching.1 hbc)).1,
        propext (below_head_iff hN h.isSwitching hxy hbc he)]

/-- In an SNP changing on `(x, y)`, the root and `y` have different states. -/
theorem state_root_ne (hN : N.RootedBinaryLevelOne) {h : SiteHistory N σ} {x y : ℕ}
    (hch : h.changes = {(x, y)}) : h.state N.root ≠ h.state y := by
  have hmem := Finset.mem_filter.mp (hch ▸ Finset.mem_singleton_self (x, y))
  have hx := state_eq_of_changes hN hch (hN.2.1 _ (h.isSwitching.1 hmem.1)).1
  rw [ite_eq_right (not_below_tail hN h.isSwitching hmem.1)] at hx
  rw [← hx]
  exact hmem.2

/-- Section 3.2: for an SNP, the quartets of `External.SiteHistory.quartets` are those the paper
reads off the states at the leaves. -/
theorem quartets_eq_pattern (hN : N.RootedBinaryLevelOne) {h : SiteHistory N σ}
    (hsnp : h.IsSNP) : h.quartets = h.patternQuartets := by
  classical
  obtain ⟨⟨x, y⟩, hch⟩ := Finset.card_eq_one.mp hsnp
  rw [quartets_of_changes hch]
  ext q
  simp only [cutQuartets, patternQuartets, Finset.mem_filter]
  refine and_congr_right fun hq => ?_
  have hqt : q.taxa ⊆ N.taxa := Quartet.mem_onTaxa.mp hq
  -- the state of a leaf records whether its taxon lies in the clade below `y`
  let P : ℕ → Prop := fun a => a ∈ N.cladeBelow h.switching y
  have hleaf : ∀ a ∈ q.taxa, h.state (N.leaf a) = if P a then h.state y else h.state N.root := by
    intro a ha
    have haN := hqt ha
    rw [state_eq_of_changes hN hch (hN.2.2.2.2.2.2.2.1 a haN).1]
    simp only [P, RootedNetwork.cladeBelow, Finset.mem_filter, haN, true_and]
  have hne := state_root_ne hN hch
  have heq : ∀ a ∈ q.taxa, ∀ b ∈ q.taxa,
      (h.state (N.leaf a) = h.state (N.leaf b) ↔ (P a ↔ P b)) := by
    intro a ha b hb
    rw [hleaf a ha, hleaf b hb]
    by_cases hPa : P a <;> by_cases hPb : P b <;> simp [hPa, hPb, hne, Ne.symm hne]
  have h1 : ∀ a ∈ q.sides.1, a ∈ q.taxa := fun a ha => q.sides_subset_taxa.1 ha
  have h2 : ∀ a ∈ q.sides.2, a ∈ q.taxa := fun a ha => q.sides_subset_taxa.2 ha
  have hbool : q.cutBy (N.cladeBelow h.switching y) = true ↔
      ((∀ a ∈ q.sides.1, P a) ∧ (∀ b ∈ q.sides.2, ¬P b) ∨
        (∀ a ∈ q.sides.1, ¬P a) ∧ (∀ b ∈ q.sides.2, P b)) := by
    simp only [Quartet.cutBy, decide_eq_true_eq, Finset.subset_iff, Finset.disjoint_left, P]
    tauto
  rw [hbool, ← Realization.side_partition_iff q.sides_nonempty.1 q.sides_nonempty.2 P]
  constructor
  · rintro ⟨hAA, hBB, hAB⟩
    exact ⟨fun a ha b hb => (heq a (h1 a ha) b (h1 b hb)).mpr (hAA a ha b hb),
      fun a ha b hb => (heq a (h2 a ha) b (h2 b hb)).mpr (hBB a ha b hb),
      fun a ha b hb hab => hAB a ha b hb ((heq a (h1 a ha) b (h2 b hb)).mp hab)⟩
  · rintro ⟨hAA, hBB, hAB⟩
    exact ⟨fun a ha b hb => (heq a (h1 a ha) b (h1 b hb)).mp (hAA a ha b hb),
      fun a ha b hb => (heq a (h2 a ha) b (h2 b hb)).mp (hBB a ha b hb),
      fun a ha b hb hab => hAB a ha b hb ((heq a (h1 a ha) b (h2 b hb)).mpr hab)⟩

/-- Every quartet of an SNP is displayed by `N`: it is cut by the clade below the head `y` of an
edge `(x, y)` of a switching (`RootedNetwork.displays_iff_cladeBelow`). -/
theorem displays_of_mem_quartets (hN : N.RootedBinaryLevelOne) {h : SiteHistory N σ}
    {q : Quartet} (hq : q ∈ h.quartets) : N.DisplaysQuartet q := by
  unfold quartets at hq
  split_ifs at hq with hsnp
  · obtain ⟨e, he, hqe⟩ := Finset.mem_biUnion.mp hq
    obtain ⟨hqt, hcut⟩ := Finset.mem_filter.mp hqe
    exact (RootedNetwork.displays_iff_cladeBelow hN q).mpr ⟨Quartet.mem_onTaxa.mp hqt,
      h.switching, h.isSwitching, e.1, e.2, (Finset.mem_filter.mp he).1, hcut⟩
  · exact absurd hq (Finset.notMem_empty q)

end SiteHistory

namespace SiteHistory

open Relation

variable {N : RootedNetwork} {σ : Type*}

/-- The history that evolves down the switching `S` and changes only on its edge `(x, y)`: the
state `s₁` at the vertices below `y` in `S`, and `s₀` at the others. -/
noncomputable def snp (hN : N.RootedBinaryLevelOne) {S : Finset (ℕ × ℕ)} (hS : N.Switching S)
    {x y : ℕ} (hxy : (x, y) ∈ S) (s₀ s₁ : σ) : SiteHistory N σ := by
  classical
  exact ⟨S, fun v => if ReflTransGen (fun a b => (a, b) ∈ S) y v then s₁ else s₀, hS,
    fun v hv => by
      simp only [ite_eq_right (not_below_of_not_mem hN hS hxy hv),
        ite_eq_right (not_below_root hN hS hxy)]⟩

variable (hN : N.RootedBinaryLevelOne) {S : Finset (ℕ × ℕ)} (hS : N.Switching S) {x y : ℕ}
  (hxy : (x, y) ∈ S) (s₀ s₁ : σ)

theorem snp_switching : (snp hN hS hxy s₀ s₁).switching = S := rfl

theorem snp_state_tail : (snp hN hS hxy s₀ s₁).state x = s₀ := by
  classical
  exact ite_eq_right (not_below_tail hN hS hxy)

theorem snp_state_head : (snp hN hS hxy s₀ s₁).state y = s₁ := by
  classical
  exact ite_eq_left ReflTransGen.refl

/-- The state of `snp` does not change on the edges of `S` other than `(x, y)`. -/
theorem snp_state_eq {e : ℕ × ℕ} (he : e ∈ S) (hne : e ≠ (x, y)) :
    (snp hN hS hxy s₀ s₁).state e.1 = (snp hN hS hxy s₀ s₁).state e.2 := by
  classical
  have hiff := below_head_iff hN hS hxy (u := e.1) (v := e.2) he hne
  change (if ReflTransGen (fun a b => (a, b) ∈ S) y e.1 then s₁ else s₀) =
    (if ReflTransGen (fun a b => (a, b) ∈ S) y e.2 then s₁ else s₀)
  by_cases h1 : ReflTransGen (fun a b => (a, b) ∈ S) y e.1
  · rw [ite_eq_left h1, ite_eq_left (hiff.mpr h1)]
  · rw [ite_eq_right h1, ite_eq_right (fun h2 => h1 (hiff.mp h2))]

variable {s₀ s₁} [DecidableEq σ]

/-- With two different states, `snp` changes on `(x, y)` and nowhere else. -/
theorem snp_changes (hs : s₀ ≠ s₁) : (snp hN hS hxy s₀ s₁).changes = {(x, y)} := by
  ext e
  simp only [changes, Finset.mem_filter, Finset.mem_singleton, snp_switching]
  constructor
  · rintro ⟨he, hne⟩
    by_contra hexy
    exact hne (snp_state_eq hN hS hxy s₀ s₁ he hexy)
  · rintro rfl
    refine ⟨hxy, ?_⟩
    rw [snp_state_tail, snp_state_head]
    exact hs

/-- With two different states, `snp` is an SNP whose quartets are those cut by the clade below
`y` in `S`. -/
theorem snp_quartets (hs : s₀ ≠ s₁) :
    (snp hN hS hxy s₀ s₁).quartets = cutQuartets N S y :=
  quartets_of_changes (snp_changes hN hS hxy hs)

theorem snp_isSNP (hs : s₀ ≠ s₁) : (snp hN hS hxy s₀ s₁).IsSNP := by
  unfold IsSNP
  rw [snp_changes hN hS hxy hs, Finset.card_singleton]

end SiteHistory

namespace SiteParameters

variable {N : RootedNetwork} {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The probability that a site contributes the quartet `q` to `Q`: the total probability of the
histories whose quartets contain `q`. -/
noncomputable def quartetProb (M : SiteParameters N σ) (q : Quartet) : ℝ≥0 :=
  ∑ h ∈ Finset.univ.filter (fun h : SiteHistory N σ => q ∈ h.quartets), M.weight h

/-- The law of the set of histories that contribute `q` is `quartetProb q`. -/
theorem law_quartets (M : SiteParameters N σ) (hN : N.RootedBinaryLevelOne) (q : Quartet) :
    M.law hN {h | q ∈ h.quartets} = (M.quartetProb q : ℝ≥0∞) := by
  classical
  rw [law_apply]
  rfl

end SiteParameters

namespace SiteModel

open Relation

variable {N : RootedNetwork} {σ : Type*} [Fintype σ] [DecidableEq σ]

omit [DecidableEq σ] in
/-- The history `SiteHistory.snp`, which follows a switching `S` and changes only on an edge
`(x, y)` of `S` into a vertex of indegree 1, has positive probability: the transmission and root
probabilities are positive, the change on `(x, y)` is a change on a tree edge, and on every other
edge of `S` the state stays the same, which has probability 1 on a reticulation edge and
`p(f, s, s) > 0` on a tree edge `f` (`stay_pos`). -/
theorem weight_snp_pos (M : SiteModel N σ) (hN : N.RootedBinaryLevelOne)
    {S : Finset (ℕ × ℕ)} (hS : N.Switching S) {x y : ℕ} (hxy : (x, y) ∈ S)
    (hy : N.indegree y = 1) {s₀ s₁ : σ} (hs : s₀ ≠ s₁) :
    0 < M.weight (SiteHistory.snp hN hS hxy s₀ s₁) := by
  simp only [SiteParameters.weight, SiteHistory.snp_switching]
  refine mul_pos (mul_pos ?_ (M.root_pos _)) ?_
  · refine Finset.prod_pos fun e he => ?_
    obtain ⟨heS, h2⟩ := Finset.mem_filter.mp he
    exact M.transmission_pos e (hS.1 heS) h2
  · refine Finset.prod_pos fun e he => ?_
    by_cases hexy : e = (x, y)
    · subst hexy
      rw [SiteHistory.snp_state_tail, SiteHistory.snp_state_head]
      exact M.change_pos _ (hS.1 he) hy s₀ s₁ hs
    · rw [SiteHistory.snp_state_eq hN hS hxy s₀ s₁ he hexy]
      exact M.stay_pos_edge hN (hS.1 he) _

/-- The proof of WTE's Theorem 6, for quartets: every quartet `q` displayed by `N` is a quartet
of an SNP of positive probability. Some switching `S` has an edge `(x, y)` into a vertex of
indegree 1 whose clade below `y` cuts `q` (`RootedNetwork.displays_iff_treeEdge_cladeBelow`);
the history that follows `S`, with one state above `(x, y)` and another below
(`SiteHistory.snp`), changes only on `(x, y)`, and its probability is positive
(`weight_snp_pos`, which uses `stay_pos`). -/
theorem exists_snp (M : SiteModel N σ) (hN : N.RootedBinaryLevelOne) [Nontrivial σ]
    {q : Quartet} (hq : N.DisplaysQuartet q) :
    ∃ h : SiteHistory N σ, 0 < M.weight h ∧ h.IsSNP ∧ q ∈ h.quartets := by
  -- WTE: a tree of the network containing the edge `e = (x, y)` whose clade is cut by `q`
  obtain ⟨hqt, S, hS, x, y, hxy, hy, hcut⟩ :=
    (RootedNetwork.displays_iff_treeEdge_cladeBelow hN q).mp hq
  obtain ⟨s₀, s₁, hs⟩ := exists_pair_ne σ
  -- WTE: the character changes on `e` and no other edge of the tree, so it is an SNP, and this
  -- has strictly positive probability
  refine ⟨SiteHistory.snp hN hS hxy s₀ s₁, M.weight_snp_pos hN hS hxy hy hs,
    SiteHistory.snp_isSNP hN hS hxy hs, ?_⟩
  rw [SiteHistory.snp_quartets hN hS hxy hs]
  exact Finset.mem_filter.mpr ⟨Quartet.mem_onTaxa.mpr hqt, hcut⟩

/-- A quartet displayed by `N` is contributed by a site with positive probability. -/
theorem quartetProb_pos (M : SiteModel N σ) (hN : N.RootedBinaryLevelOne) [Nontrivial σ]
    {q : Quartet} (hq : N.DisplaysQuartet q) : 0 < M.quartetProb q := by
  obtain ⟨h, hpos, -, hqh⟩ := M.exists_snp hN hq
  exact lt_of_lt_of_le hpos (Finset.single_le_sum (fun _ _ => zero_le)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ h, hqh⟩))

end SiteModel

namespace SiteModel

/-- A model on every network `N`, so that the hypotheses of the consistency theorems are not
vacuous: transmission probabilities 1/2 (an edge into a reticulation of a rooted binary network
is one of two), the uniform distribution at the root, the uniform row on tree edges, and no change
on reticulation edges. -/
noncomputable def uniform (N : RootedNetwork) (σ : Type*) [Fintype σ] [DecidableEq σ]
    [Nonempty σ] : SiteModel N σ where
  transmission _ := 2⁻¹
  transmission_pos _ _ _ := by positivity
  transmission_sum v _ h2 := by
    rw [Finset.sum_const, nsmul_eq_mul]
    have hc : (N.edges.filter fun e => e.2 = v).card = 2 := h2
    rw [hc]
    norm_num
  root _ := (Fintype.card σ : ℝ≥0)⁻¹
  root_pos _ := by
    have := Fintype.card_pos (α := σ)
    positivity
  root_sum := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)
  substitution e s s' :=
    if N.indegree e.2 = 2 then (if s = s' then 1 else 0) else (Fintype.card σ : ℝ≥0)⁻¹
  substitution_sum e _ s := by
    by_cases h2 : N.indegree e.2 = 2
    · simp [h2]
    · simp only [h2, ite_false, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)
  change_pos e _ h1 _ _ _ := by
    have := Fintype.card_pos (α := σ)
    simp only [h1, show (1 : ℕ) ≠ 2 by decide, ite_false]
    positivity
  stay_pos e _ h1 _ := by
    have := Fintype.card_pos (α := σ)
    simp only [h1, show (1 : ℕ) ≠ 2 by decide, ite_false]
    positivity
  no_change e _ h2 s s' hs := by simp [h2, hs]

end SiteModel

end External

end Camus
