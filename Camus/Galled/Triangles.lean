module

public import Camus.Galled.Bounds
public import Camus.Galled.TreeIsomorphism
public import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# Networks of triangles display only the quartets of their trees

In the block grammar, a valid network with `n` leaves and `n − 1` reticulations has slack `0`
(`GalledNetwork.reticulations_add_slack`): it has no fork, and every gall is a triangle, with a
single hanging subnetwork. The two switchings of a triangle give the same tree up to swapping two
children. Hence all displayed trees of such a network have the same clusters, and the network
displays exactly the quartets of any one of its displayed trees. This is the block-grammar form of
the argument behind the counterexample E3 of the report (`Counterexamples.exact_three_score_zero`).

## Main results

* `GalledNetwork.saturated_cluster_eq`: all displayed trees of a valid network with slack `0` have
  the same clusters.
* `GalledNetwork.saturated_contains_eq`: a valid network with `n` leaves and `n − 1` reticulations
  displays a quartet iff any one of its displayed trees induces it.
-/

@[expose] public section

namespace Camus.GalledNetwork

/-- The trees displayed by the triangle `gall [a] [] b` are the trees `(x, y)` with `x` displayed by
`a` and `y` displayed by `b`: both switchings give the same tree. -/
theorem mem_displayed_left_triangle (a b : GalledNetwork) (t : PhyloTree) :
    t ∈ (gall [a] [] b).displayed ↔
      ∃ x ∈ a.displayed, ∃ y ∈ b.displayed, PhyloTree.fork x y = t := by
  simp [displayed, choices, gallTrees, chain, chainWithout, join, eq_comm]

/-- The trees displayed by the triangle `gall [] [a] b` are the trees `(y, x)` and `(x, y)` with `x`
displayed by `a` and `y` displayed by `b`: the two switchings differ by a swap of children. -/
theorem mem_displayed_right_triangle (a b : GalledNetwork) (t : PhyloTree) :
    t ∈ (gall [] [a] b).displayed ↔
      ∃ x ∈ a.displayed, ∃ y ∈ b.displayed,
        PhyloTree.fork y x = t ∨ PhyloTree.fork x y = t := by
  simp [displayed, choices, gallTrees, chain, chainWithout, join, eq_comm]

/-- If a valid network has slack `0` (no fork, and only triangles), all its displayed trees have the
same clusters. -/
theorem saturated_cluster_eq (n : GalledNetwork) (hn : n.Valid) (hz : n.slack = 0)
    (t u : PhyloTree) (ht : t ∈ n.displayed) (hu : u ∈ n.displayed) :
    PhyloTree.ClusterEq t u := by
  let P := fun n : GalledNetwork => n.Valid → n.slack = 0 →
    ∀ t ∈ n.displayed, ∀ u ∈ n.displayed, PhyloTree.ClusterEq t u
  have h : P n := by
    apply GalledNetwork.rec (motive_1 := P)
      (motive_2 := fun xs => ∀ x ∈ xs, P x)
    · intro a _ _ t ht u hu
      simp only [displayed, List.mem_singleton] at ht hu
      subst t
      subst u
      exact PhyloTree.ClusterEq.refl _
    · intro l r _ _ _ hz
      simp only [slack] at hz
      omega
    · intro l r b ihl ihr ihb hvalid hzero
      simp only [Valid] at hvalid
      have hlen : l.length + r.length = 1 := by
        simp only [slack] at hzero
        rcases hvalid.1 with hl | hr
        · have := List.length_pos_iff.mpr hl
          omega
        · have := List.length_pos_iff.mpr hr
          omega
      cases l with
      | nil =>
        have hrlen : r.length = 1 := by simpa using hlen
        obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hrlen
        have ha : a.slack = 0 := by
          simp [slack] at hzero
          omega
        have hb : b.slack = 0 := by
          simp [slack] at hzero
          omega
        have ia := ihr a (by simp) (hvalid.2.2.1 a (by simp)) ha
        have ib := ihb hvalid.2.2.2 hb
        intro t ht u hu
        rw [mem_displayed_right_triangle] at ht hu
        rcases ht with ⟨x, hx, y, hy, ht | ht⟩ <;>
          rcases hu with ⟨x', hx', y', hy', hu | hu⟩ <;> subst t <;> subst u
        · exact PhyloTree.ClusterEq.fork (ib _ hy _ hy') (ia _ hx _ hx')
        · exact (PhyloTree.ClusterEq.fork (ib _ hy _ hy') (ia _ hx _ hx')).trans
            (PhyloTree.ClusterEq.fork_swap _ _)
        · exact (PhyloTree.ClusterEq.fork (ia _ hx _ hx') (ib _ hy _ hy')).trans
            (PhyloTree.ClusterEq.fork_swap _ _)
        · exact PhyloTree.ClusterEq.fork (ia _ hx _ hx') (ib _ hy _ hy')
      | cons a xs =>
        have hxs : xs = [] := by
          apply List.length_eq_zero_iff.mp
          simp only [List.length_cons] at hlen
          omega
        have hr : r = [] := by
          apply List.length_eq_zero_iff.mp
          simp only [List.length_cons] at hlen
          omega
        subst xs
        subst r
        have ha : a.slack = 0 := by
          simp [slack] at hzero
          omega
        have hb : b.slack = 0 := by
          simp [slack] at hzero
          omega
        have ia := ihl a (by simp) (hvalid.2.1 a (by simp)) ha
        have ib := ihb hvalid.2.2.2 hb
        intro t ht u hu
        rw [mem_displayed_left_triangle] at ht hu
        rcases ht with ⟨x, hx, y, hy, rfl⟩
        rcases hu with ⟨x', hx', y', hy', rfl⟩
        exact PhyloTree.ClusterEq.fork (ia _ hx _ hx') (ib _ hy _ hy')
    · simp
    · intro a xs iha ihxs x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact iha
      · exact ihxs x hx
  exact h hn hz t ht u hu

/-- A valid network with `n` leaves and `n − 1` reticulations displays exactly the quartets of any
one of its displayed trees `t`: `q ∈ Q(N_r)` iff `t` induces `q`. -/
theorem saturated_contains_eq (n : GalledNetwork) (hn : n.Valid)
    (hsat : n.reticulations + 1 = n.labels.length) (t : PhyloTree)
    (ht : t ∈ n.displayed) (q : Quartet) : n.containsQuartet q = q.induced t := by
  have hz : n.slack = 0 := by
    have h := reticulations_add_slack n hn
    omega
  rw [Bool.eq_iff_iff]
  change n.displayed.any q.induced = true ↔ q.induced t = true
  rw [List.any_eq_true]
  constructor
  · rintro ⟨u, hu, hq⟩
    rw [← (saturated_cluster_eq n hn hz u t hu ht).induced_eq q]
    exact hq
  · intro hq
    exact ⟨t, ht, hq⟩

end Camus.GalledNetwork
