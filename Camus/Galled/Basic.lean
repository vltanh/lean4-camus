module

public import Camus.Defs

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.List.FinRange
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# A block grammar for galled networks

A recursive description of rooted binary galled (level-1) networks by their blocks, with their
displayed trees `T(N)` (Definition 1), their displayed and satisfied quartets, their reticulations
and their leaf labels. Displayed trees are computed gall by gall, so statements about a given
network can be checked by evaluation. The grammar is used for the checked examples E3 and E4 of
the report (`Camus/Galled/Counterexamples.lean`). It is separate from the directed-graph networks
`RootedNetwork` of the rest of the formalization; no theorem relates the two. The graph versions of
E3 and E4 are in `Camus/Restriction/Witness.lean` and `Camus/Pipelines/Counterexample.lean`.

## Main definitions

* `GalledNetwork`: leaves, forks and galls.
* `GalledNetwork.displayed`: the displayed trees `T(N)`.
* `GalledNetwork.containsQuartet`, `GalledNetwork.satisfies`: `q ∈ Q(N_r)` and
  `q ∈ Q(N_r) ∖ Q(T)`.
* `GalledNetwork.Extends`: `N` is built on `T`.
* `GalledNetwork.reticulations`, `GalledNetwork.Valid`, `GalledNetwork.Phylogenetic`.
-/

@[expose] public section

namespace Camus

/-- A rooted binary galled network, written by its blocks:

* `leaf a`, a leaf labelled `a`;
* `fork l r`, a tree vertex with the subnetworks `l` and `r` below it;
* `gall l r b`, a cycle: its top vertex has two directed paths to a reticulation, the successive
  internal vertices of the left path carry the subnetworks of the list `l` (from top to bottom),
  those of the right path the subnetworks of `r`, and the reticulation has the subnetwork `b`
  below it.

Subnetworks hang by cut edges, so the cycles of different galls share no vertex: the network is
level-1. `Valid` requires an internal vertex on at least one of the two paths of every gall, which
excludes parallel edges. -/
inductive GalledNetwork where
  | leaf : ℕ → GalledNetwork
  | fork : GalledNetwork → GalledNetwork → GalledNetwork
  | gall (left right : List GalledNetwork) (bottom : GalledNetwork)
      : GalledNetwork
  deriving Repr

namespace GalledNetwork

/-- The tree below a path of a gall that keeps its edge into the reticulation, with trees `ts` for
the hanging subnetworks and `bottom` below the reticulation, after suppressing unary vertices:
`(t₁, (t₂, (…, (t_k, bottom))))`. -/
def chain (ts : List PhyloTree) (bottom : PhyloTree) : PhyloTree :=
  ts.foldr PhyloTree.fork bottom

/-- The tree below a path of a gall that loses its edge into the reticulation, after suppressing
unary vertices: `(t₁, (…, (t_{k−1}, t_k)))`. An empty path leaves nothing. -/
def chainWithout : List PhyloTree → Option PhyloTree
  | [] => none
  | [t] => some t
  | t :: u :: ts => (chainWithout (u :: ts)).map (PhyloTree.fork t)

/-- The tree below the top vertex of a gall, from the trees below its two paths: their fork, or the
nonempty one alone when the top vertex has become unary and is suppressed. -/
def join (l r : Option PhyloTree) : Option PhyloTree :=
  match l, r with
  | some l, some r => some (.fork l r)
  | some t, none | none, some t => some t
  | none, none => none

/-- The two trees displayed by a gall, given trees for its hanging subnetworks and for its bottom:
the reticulation keeps its incoming edge from the left path and loses the one from the right path,
or the other way round. -/
def gallTrees (l r : List PhyloTree) (b : PhyloTree) : List PhyloTree :=
  (join (some (chain l b)) (chainWithout r)).toList ++
    (join (chainWithout l) (some (chain r b))).toList

/-- All ways to choose one tree from each list: one displayed tree for every hanging subnetwork. -/
def choices (xs : List (List PhyloTree)) : List (List PhyloTree) :=
  xs.foldr (fun s acc => s.flatMap fun t => acc.map (t :: ·)) [[]]

/-- The trees displayed by the network (`T(N)` in Definition 1): delete one incoming edge of every
reticulation, in every possible way, and suppress the unary vertices. The list may repeat a
tree. -/
def displayed : GalledNetwork → List PhyloTree
  | .leaf a => [.leaf a]
  | .fork l r => (displayed l).flatMap fun a => (displayed r).map (.fork a ·)
  | .gall l r b =>
    (choices (l.map displayed)).flatMap fun ls =>
      (choices (r.map displayed)).flatMap fun rs =>
        (displayed b).flatMap fun bs => gallTrees ls rs bs
termination_by n => sizeOf n

/-- The number of reticulations: one per gall. -/
def reticulations : GalledNetwork → ℕ
  | .leaf _ => 0
  | .fork l r => reticulations l + reticulations r
  | .gall l r b => 1 + (l.map reticulations).sum +
      (r.map reticulations).sum + reticulations b
termination_by n => sizeOf n

/-- The labels of the leaves, with repetitions. -/
def labels : GalledNetwork → List ℕ
  | .leaf a => [a]
  | .fork l r => labels l ++ labels r
  | .gall l r b => (l.flatMap labels) ++ (r.flatMap labels) ++ labels b
termination_by n => sizeOf n

/-- Every gall has an internal vertex on at least one of its two paths, so that it has no parallel
edges; recursively in all subnetworks. -/
def Valid : GalledNetwork → Prop
  | .leaf _ => True
  | .fork l r => Valid l ∧ Valid r
  | .gall l r b => (l ≠ [] ∨ r ≠ []) ∧
      (∀ x ∈ l, Valid x) ∧ (∀ x ∈ r, Valid x) ∧ Valid b
termination_by n => sizeOf n

/-- The leaf labels are distinct. -/
def WellLabelled (n : GalledNetwork) : Prop := n.labels.Nodup

/-- A phylogenetic network: valid, with distinct leaf labels. -/
def Phylogenetic (n : GalledNetwork) : Prop := n.Valid ∧ n.WellLabelled

instance (n : GalledNetwork) : Decidable n.WellLabelled :=
  inferInstanceAs (Decidable n.labels.Nodup)

/-- `q ∈ Q(N_r)` (Definition 1): some displayed tree of `n` induces `q`. -/
def containsQuartet (n : GalledNetwork) (q : Quartet) : Bool :=
  n.displayed.any q.induced

/-- `n` is built on `t` (Definition 1): `t` is one of the displayed trees of `n`, as a plane tree,
with its order of children. -/
def Extends (n : GalledNetwork) (t : PhyloTree) : Prop := t ∈ n.displayed

instance (n : GalledNetwork) (t : PhyloTree) : Decidable (n.Extends t) :=
  inferInstanceAs (Decidable (t ∈ n.displayed))

/-- `q` is satisfied by `n` relative to `t` (Section 2.1, after Definition 1):
`q ∈ Q(N_r) ∖ Q(t)`. -/
def satisfies (n : GalledNetwork) (t : PhyloTree) (q : Quartet) : Bool :=
  n.containsQuartet q && !q.induced t

end GalledNetwork

end Camus
