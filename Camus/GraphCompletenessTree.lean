module

public import Camus.GraphCompletenessAnchors
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

@[expose] public section

namespace Camus.RootedNetwork

/-- The number of strict ancestors is a topological rank for a finite DAG. -/
noncomputable def dagRank (N : RootedNetwork) (v : ℕ) : ℕ := by
  classical
  exact (N.vertices.filter (fun u =>
    Relation.TransGen (fun x y => (x,y) ∈ N.edges) u v)).card

theorem dagRank_lt {N : RootedNetwork} (hN : N.RootedBinaryLevelOne)
    {u v : ℕ} (he : (u,v) ∈ N.edges) : N.dagRank u < N.dagRank v := by
  classical
  unfold dagRank
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_exists_subset_erase.mpr
  refine ⟨u, Finset.mem_filter.mpr ⟨(hN.2.1 _ he).1,
    Relation.TransGen.single he⟩, ?_⟩
  intro w hw
  obtain ⟨hw, hwu⟩ := Finset.mem_filter.mp hw
  refine Finset.mem_erase.mpr ⟨?_, Finset.mem_filter.mpr
    ⟨hw, hwu.trans (Relation.TransGen.single he)⟩⟩
  intro hwu'
  subst w
  exact hN.2.2.1 u hwu

theorem switching_incoming_unique {N : RootedNetwork}
    (hN : N.RootedBinaryLevelOne) {S : Finset (ℕ × ℕ)} (hS : N.Switching S)
    {u v w : ℕ} (hu : (u,v) ∈ S) (hw : (w,v) ∈ S) : u = w := by
  classical
  have hv := (hN.2.1 _ (hS.1 hu)).2
  by_cases hr : v = N.root
  · have hz := hN.2.2.2.1
    have he : (u,N.root) ∈ N.edges.filter (fun e => e.2 = N.root) :=
      Finset.mem_filter.mpr ⟨by simpa [hr] using hS.1 hu, rfl⟩
    rw [Finset.card_eq_zero.mp hz] at he
    exact False.elim (Finset.notMem_empty _ he)
  · have hcard : (S.filter (fun e => e.2 = v)).card ≤ 1 := by
      rw [hS.2 v hv hr]
    have heq := Finset.card_le_one.mp hcard
      (u,v) (Finset.mem_filter.mpr ⟨hu,rfl⟩)
      (w,v) (Finset.mem_filter.mpr ⟨hw,rfl⟩)
    exact congrArg Prod.fst heq

/-- A switching has no undirected cycles. A cycle's greatest topological-rank
vertex would have two different incoming switching edges. -/
theorem switching_acyclic {N : RootedNetwork} (hN : N.RootedBinaryLevelOne)
    {S : Finset (ℕ × ℕ)} (hS : N.Switching S) :
    ({N with edges := S}).underlying.IsAcyclic := by
  classical
  intro v c hc
  have hn : c.support.toFinset.Nonempty :=
    ⟨v, List.mem_toFinset.mpr c.start_mem_support⟩
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image c.support.toFinset N.dagRank hn
  have hmc : m ∈ c.support := List.mem_toFinset.mp hm
  let d := c.rotate m hmc
  have hd : d.IsCycle := hc.rotate hmc
  have hs : N.dagRank d.snd ≤ N.dagRank m := hmax _
    (List.mem_toFinset.mpr ((c.mem_support_rotate_iff m hmc).mp
      (List.mem_of_mem_tail (d.snd_mem_tail_support hd.not_nil))))
  have hp : N.dagRank d.penultimate ≤ N.dagRank m := hmax _
    (List.mem_toFinset.mpr ((c.mem_support_rotate_iff m hmc).mp
      (List.mem_of_mem_dropLast (d.penultimate_mem_dropLast_support hd.not_nil))))
  have hsa := d.adj_snd hd.not_nil
  have hpa := d.adj_penultimate hd.not_nil
  have hin₁ : (d.snd,m) ∈ S := by
    rcases hsa.2 with hout | hin
    · exact False.elim ((not_lt_of_ge hs) (dagRank_lt hN (hS.1 hout)))
    · exact hin
  have hin₂ : (d.penultimate,m) ∈ S := by
    rcases hpa.2 with hin | hout
    · exact hin
    · exact False.elim ((not_lt_of_ge hp) (dagRank_lt hN (hS.1 hout)))
  exact hd.snd_ne_penultimate (switching_incoming_unique hN hS hin₁ hin₂)

theorem edge_ne {N : RootedNetwork} (hN : N.RootedBinaryLevelOne)
    {u v : ℕ} (he : (u,v) ∈ N.edges) : u ≠ v := by
  intro huv
  subst v
  exact hN.2.2.1 u (Relation.TransGen.single he)

theorem edge_reverse_not_mem {N : RootedNetwork} (hN : N.RootedBinaryLevelOne)
    {u v : ℕ} (he : (u,v) ∈ N.edges) : (v,u) ∉ N.edges := by
  intro hr
  exact hN.2.2.1 u ((Relation.TransGen.single he).trans
    (Relation.TransGen.single hr))

theorem switching_underlying_le {N : RootedNetwork}
    {S : Finset (ℕ × ℕ)} (hS : N.Switching S) :
    ({N with edges := S}).underlying ≤ N.underlying := by
  intro u v h
  exact ⟨h.1, h.2.imp (fun he => hS.1 he) (fun he => hS.1 he)⟩

theorem switching_connected_vertices {N : RootedNetwork}
    (hN : N.RootedBinaryLevelOne) {S : Finset (ℕ × ℕ)} (hS : N.Switching S)
    {u v : ℕ} (hu : u ∈ N.vertices) (hv : v ∈ N.vertices) :
    ({N with edges := S}).underlying.Reachable u v := by
  have rootpath : ∀ w ∈ N.vertices,
      ({N with edges := S}).underlying.Reachable N.root w := by
    intro w hw
    apply (SimpleGraph.reachable_iff_reflTransGen _ _).mpr
    apply Relation.ReflTransGen.mono ?_ N.root w (switching_reachable hN hS hw)
    intro a b hab
    exact ⟨edge_ne hN (hS.1 hab), Or.inl hab⟩
  exact (rootpath u hu).symm.trans (rootpath v hv)

theorem switching_existsUnique_path {N : RootedNetwork}
    (hN : N.RootedBinaryLevelOne) {S : Finset (ℕ × ℕ)} (hS : N.Switching S)
    {u v : ℕ} (hu : u ∈ N.vertices) (hv : v ∈ N.vertices) :
    ∃! p : ({N with edges := S}).underlying.Walk u v, p.IsPath := by
  classical
  let p := (switching_connected_vertices hN hS hu hv).some.toPath
  refine ⟨p, p.isPath, ?_⟩
  intro q hq
  exact Subtype.mk.inj ((switching_acyclic hN hS).subsingleton_path u v |>.elim ⟨q,hq⟩ p)

theorem deleted_edge_not_switching_edgeSet {N : RootedNetwork}
    (hN : N.RootedBinaryLevelOne) {S : Finset (ℕ × ℕ)} (hS : N.Switching S)
    {e : ℕ × ℕ} (he : e ∈ N.edges \ S) :
    s(e.1,e.2) ∉ ({N with edges := S}).underlying.edgeSet := by
  obtain ⟨heN, heS⟩ := Finset.mem_sdiff.mp he
  intro hs
  have hadj : ({N with edges := S}).underlying.Adj e.1 e.2 := hs
  rcases hadj.2 with hs | hr
  · exact heS hs
  · exact edge_reverse_not_mem hN heN (hS.1 hr)

/-- A simple switching path entered along a directed arc must continue forward:
a reversal would create two different incoming arcs at the turning vertex. -/
theorem switching_path_directed_of_incoming {N : RootedNetwork}
    (hN : N.RootedBinaryLevelOne) {S : Finset (ℕ × ℕ)} (hS : N.Switching S)
    {u v : ℕ} (p : ({N with edges := S}).underlying.Walk u v) (hp : p.IsPath)
    {z : ℕ} (hzu : (z,u) ∈ S) (hz : z ∉ p.support) :
    Relation.ReflTransGen (fun a b => (a,b) ∈ S) u v := by
  induction p generalizing z with
  | nil => exact Relation.ReflTransGen.refl
  | @cons u w v hadj p ih =>
    have hnodup : (u :: p.support).Nodup := hp.support_nodup
    have hup : u ∉ p.support := (List.nodup_cons.mp hnodup).1
    rcases hadj.2 with hout | hin
    · exact (Relation.ReflTransGen.single hout).trans (ih hp.of_cons hout hup)
    · have hzw := switching_incoming_unique hN hS hzu hin
      exact False.elim (hz (List.mem_cons_of_mem u (hzw ▸ p.start_mem_support)))

theorem switching_path_first_incoming {N : RootedNetwork}
    (hN : N.RootedBinaryLevelOne) {S : Finset (ℕ × ℕ)} (hS : N.Switching S)
    {u v : ℕ} (p : ({N with edges := S}).underlying.Walk v u) (hp : p.IsPath)
    (hclose : (u,v) ∈ N.edges) : (p.snd,v) ∈ S := by
  cases p with
  | nil => exact False.elim (edge_ne hN hclose rfl)
  | @cons v w u hadj p =>
    rcases hadj.2 with hout | hin
    · have hnp : v ∉ p.support := (List.nodup_cons.mp hp.support_nodup).1
      have hpath := (Relation.ReflTransGen.single hout).trans
        (switching_path_directed_of_incoming hN hS p hp.of_cons hout hnp)
      have hpathN := Relation.ReflTransGen.mono
        (fun a b hab => hS.1 hab) v u hpath
      have hloop := (Relation.TransGen.single hclose).trans_right hpathN
      exact False.elim (hN.2.2.1 v hloop)
    · simpa only [SimpleGraph.Walk.snd_cons] using hin

end Camus.RootedNetwork
