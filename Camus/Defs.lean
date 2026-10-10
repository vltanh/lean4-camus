module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.List.Basic
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.List.Infix
public import Mathlib.Data.Multiset.Filter
public import Mathlib.Data.Nat.Find
public import Mathlib.Logic.Relation
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Order.Lattice.Nat

/-!
# Shared definitions

The objects of the paper that the statements of the main results use: rooted binary trees and
quartet trees, rooted binary level-1 networks and the quartets they display (Definition 1),
networks built on a tree `T`, the network obtained from `T` by adding edges (Definitions 2, 3
and 5), and the dynamic program of Section 2.2 (Equations (1)–(5) and the backtracking). The
block between the two marker comments is copied verbatim into `Challenge.lean` by
`scripts/sync_challenge_defs.py`, so that the Challenge and the library state the main results
with the same definitions. Their properties are proved in the rest of the library.

## Main definitions

* `PhyloTree`, `Address`, `lca`: rooted binary trees with leaves labelled by natural numbers,
  their vertices, and least common ancestors.
* `Quartet`, `Quartet.induced`: quartet trees and the set Q(t) of Definition 1.
* `RootedNetwork`, `RootedNetwork.RootedBinaryLevelOne`: rooted binary level-1 networks as
  finite directed graphs.
* `RootedNetwork.Switching`, `RootedNetwork.DisplaysQuartet`: the displayed trees and the set
  Q(N_r) of Definition 1.
* `SupportSubdivision`, `RootedNetwork.AnchoredExtension`: the network `N` is built on `T`, with
  the root of `T` at the root of `N`.
* `DisplayedSubdivision`, `RootedNetwork.BuiltOn`: `N` is built on `T` in the sense of
  Definition 1, the root of `T` at or below the root of `N`.
* `EdgeAbove.Admissible`, `EdgeAbove.target`, `EdgeAbove.footprint`: the pairs `(u, w)` above
  which an edge can be added, their targets lca(u, w) (Definition 2), and the vertices of `T` on
  their cycles γ(u, w).
* `Realization.graph`: the network obtained from `T` by adding an edge above each pair of a
  family (Definition 3); `Realization.child`: the children of Definition 5.
* `DynamicProgramming.edgeWeight`, `DynamicProgramming.Array`, `DynamicProgramming.s`,
  `DynamicProgramming.sdpCross`, `DynamicProgramming.sdpGhost`: Equations (1)–(5);
  `DynamicProgramming.Trace`: the backtracking.
* `DynamicProgramming.repertoire`, `DynamicProgramming.novel`: the quartets of `Q` displayed,
  or satisfied, by a network; `score`: their number, counted with multiplicity in `Q`.
* `RootedNetwork.reticulationCount`: the number of reticulations.
* `BudgetDP.cases`, `BudgetDP.Array`, `BudgetDP.Knapsack`, `BudgetDP.Trace`: the dynamic program
  of Section 2.4, for exact numbers of added edges, and its backtracking.
* `ExactCountMonotone`, `UniqueOptimum`, `ExactStoppingRule`, `AtMostStoppingRule`: claims of
  Sections 2.4 and 3.2, refuted in the library; `bestExact`, `bestAtMost` and `StopsAt` state the
  stopping rule.

## Conventions

* A vertex of a tree is its `Address`, the list of steps from the root (`false` to the left
  child, `true` to the right child); the root is `[]`. The prefix order `p <+: q` says that `p`
  is an ancestor of `q` or equal to it.
* A pair `(u, w)` stands for an edge added above `(u, w)`: from a new vertex u' on the edge above
  the donor `u` to a new vertex w' on the edge above the recipient `w`; w' is a reticulation.
* The vertices of a network are natural numbers. In `Realization.graph`, a vertex `p` of `T` is
  `Address.code p`, and u', w' are `Realization.donor` and `Realization.recipient`.
-/

@[expose] public section

-- BEGIN SHARED DEFINITIONS

namespace Camus

/-- A vertex of a rooted binary tree, given by its path from the root: the list of steps,
`false` to the left child and `true` to the right child. The root is `[]`. The prefix order
`p <+: q` is the ancestor order: `p` is an ancestor of `q` or `p = q`. -/
abbrev Address := List Bool

end Camus

namespace Camus

/-- A rooted full binary tree whose leaves are labelled by natural numbers: `leaf a` is a single
leaf labelled `a`, and `fork l r` is a root with left subtree `l` and right subtree `r`. A rooted
binary phylogenetic tree is a `PhyloTree` whose leaves have distinct labels
(`PhyloTree.WellLabelled`); its taxa are its leaf labels. -/
inductive PhyloTree where
  | leaf : ℕ → PhyloTree
  | fork : PhyloTree → PhyloTree → PhyloTree
  deriving DecidableEq, Repr

namespace PhyloTree

/-- The leaf labels of `t`, from left to right, with repetitions. -/
def labels : PhyloTree → List ℕ
  | .leaf a => [a]
  | .fork l r => labels l ++ labels r

/-- The leaves of `t` have distinct labels: `t` is a phylogenetic tree on the taxa `t.taxa`. -/
def WellLabelled (t : PhyloTree) : Prop := t.labels.Nodup

instance (t : PhyloTree) : Decidable t.WellLabelled := inferInstanceAs (Decidable t.labels.Nodup)

/-- The taxa of `t`: the set of its leaf labels. -/
def taxa (t : PhyloTree) : Finset ℕ := t.labels.toFinset

/-- The clades of `t`, one for each vertex, in preorder: the set of labels of the leaves of the
subtree rooted at that vertex. Deleting the edge above a non-root vertex `x` separates the clade
of `x` from the other taxa. The list starts with the root's clade, `t.taxa`, which cuts no
quartet whose taxa are taxa of `t`. -/
def clades : PhyloTree → List (Finset ℕ)
  | .leaf a => [{a}]
  | .fork l r => (l.taxa ∪ r.taxa) :: (clades l ++ clades r)

end PhyloTree

/-- A resolved quartet tree (Definition 1) on the four taxa `a < b < c < d`, with topology given
by `split`: `0` is ab|cd, `1` is ac|bd and `2` is ad|bc. Listing the taxa in increasing order
gives each quartet tree a unique representation. -/
structure Quartet where
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ
  ab : a < b
  bc : b < c
  cd : c < d
  split : Fin 3
  deriving DecidableEq

namespace Quartet

/-- The four taxa {a, b, c, d} of `q`. -/
def taxa (q : Quartet) : Finset ℕ := {q.a, q.b, q.c, q.d}

/-- The two sides of the split of `q`: ({a, b}, {c, d}), ({a, c}, {b, d}) or ({a, d}, {b, c}). -/
def sides (q : Quartet) : Finset ℕ × Finset ℕ :=
  if q.split = 0 then ({q.a, q.b}, {q.c, q.d})
  else if q.split = 1 then ({q.a, q.c}, {q.b, q.d})
  else ({q.a, q.d}, {q.b, q.c})

/-- The set of taxa `s` cuts the quartet `q`: `s ∩ {a, b, c, d}` is one of the two sides of `q`.
Other taxa in `s` play no role. When `s` is the clade below an edge of a tree, deleting that edge
separates the two sides of `q`. -/
def cutBy (q : Quartet) (s : Finset ℕ) : Bool :=
  decide (q.sides.1 ⊆ s ∧ Disjoint q.sides.2 s ∨
    q.sides.2 ⊆ s ∧ Disjoint q.sides.1 s)

/-- The quartet `q` is in Q(t), the set of quartet trees induced by `t` in its unrooted form
(Definition 1): the taxa of `q` are taxa of `t`, and some clade of `t` cuts `q`, that is, meets
the four taxa of `q` in one side of `q`. Deleting the edge above that clade's vertex then
separates the two sides of `q`. -/
def induced (q : Quartet) (t : PhyloTree) : Bool :=
  decide (q.taxa ⊆ t.taxa) && t.clades.any q.cutBy

end Quartet

end Camus

namespace Camus

namespace PhyloTree

/-- The vertices of `t`, as the set of their addresses. -/
def nodes : PhyloTree → Finset Address
  | .leaf _ => {[]}
  | .fork l r => insert []
      ((l.nodes.image (false :: ·)) ∪ (r.nodes.image (true :: ·)))

/-- The subtree of `t` rooted at the vertex with address `p`, or `none` if `p` is not a vertex
of `t`. -/
def nodeAt : PhyloTree → Address → Option PhyloTree
  | t, [] => some t
  | .leaf _, _ :: _ => none
  | .fork l _, false :: p => nodeAt l p
  | .fork _ r, true :: p => nodeAt r p

end PhyloTree

/-- The least common ancestor lca_T(p, q) of two vertices: the longest common prefix of their
addresses. -/
def lca : Address → Address → Address
  | [], _ => []
  | _ :: _, [] => []
  | a :: p, b :: q => if a = b then a :: lca p q else []

namespace EdgeAbove

/-- An edge can be added above the pair `e = (u, w)` of vertices of `T` (Definition 3): the
donor `u` and the recipient `w` are non-root vertices of `T`, and `w` is neither an ancestor of
`u` nor `u` itself. The root has no edge above it; if `w` is an ancestor of `u`, the new edge
from above `u` to above `w` would close a directed cycle; and `u = w` does not give two edges to
subdivide. The donor may be an ancestor of the recipient: a pair `(v, w)` with `w` below `v` is
a ghost lineage (Section 2.2). `DynamicProgramming.pairsAt` restricts the paper's Pairs(v) to
these pairs. -/
def Admissible (t : PhyloTree) (e : Address × Address) : Prop :=
  e.1 ∈ t.nodes ∧ e.2 ∈ t.nodes ∧ e.1 ≠ [] ∧ e.2 ≠ [] ∧ ¬e.2 <+: e.1

instance (t : PhyloTree) (e : Address × Address) : Decidable (Admissible t e) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The admissible pairs `(u, w)` of vertices of `T` (`EdgeAbove.Admissible`): the pairs above
which an edge can be added to `T`. -/
def candidates (t : PhyloTree) : Finset (Address × Address) :=
  (t.nodes ×ˢ t.nodes).filter (Admissible t)

/-- **Definition 2** (`mthst3`). The target `v = lca_T(u, w)` of the pair `(u, w)`. Procedure
ASSIGN assigns a non-tree edge `(u', w')` of a network built on `T`, and each quartet it
satisfies, to the triplet `(u, w, v)`, where `u` and `w` are the vertices of `T` directly below
`u'` and `w'`. -/
def target (e : Address × Address) : Address := lca e.1 e.2

/-- The vertices of `T` on the cycle γ(u, w) created by adding an edge above `e = (u, w)`
(Definition 3), that is, γ(u, w) ∩ V(T): the vertices on the paths from the target lca(u, w)
down to `u` and down to `w`, with `u` and `w` excluded, since they lie below the new vertices u'
and w' of the cycle. For a ghost donor (`u = lca(u, w)`) this includes `u` itself, since u' then
lies on the edge above `u`. -/
def footprint (t : PhyloTree) (e : Address × Address) : Finset Address :=
  t.nodes.filter fun x => target e <+: x ∧
    ((x <+: e.1 ∧ x ≠ e.1) ∨ (x <+: e.2 ∧ x ≠ e.2))

end EdgeAbove
end Camus

namespace Camus

/-- The parent of a vertex: its address without the last step. The root is its own parent. -/
def parent (p : Address) : Address := p.take (p.length - 1)

/-- The vertices of `T` not in `S` whose parent is in `S`. For a region `S`, these are the roots
of the subtrees of `T` hanging off `S`. -/
def frontier (t : PhyloTree) (S : Finset Address) : Finset Address :=
  t.nodes.filter fun x => x ≠ [] ∧ parent x ∈ S ∧ x ∉ S

end Camus

namespace Camus

/-- The data of a rooted phylogenetic network as a finite directed graph: a finite set of
vertices (natural numbers), a finite set of directed edges `(x, y)` from `x` to `y`, a root, a
finite set of taxa, and the map `leaf` sending each taxon to the leaf it labels. The laws of a
rooted binary level-1 network are `RootedNetwork.RootedBinaryLevelOne`. -/
structure RootedNetwork where
  vertices : Finset ℕ
  edges : Finset (ℕ × ℕ)
  root : ℕ
  taxa : Finset ℕ
  leaf : ℕ → ℕ

namespace RootedNetwork

/-- The number of edges of `N` into `v`. -/
def indegree (N : RootedNetwork) (v : ℕ) : ℕ :=
  (N.edges.filter (fun e => e.2 = v)).card

/-- The number of edges of `N` out of `v`. -/
def outdegree (N : RootedNetwork) (v : ℕ) : ℕ :=
  (N.edges.filter (fun e => e.1 = v)).card

/-- The underlying undirected simple graph of `N`: two distinct vertices are adjacent when `N`
has an edge between them, in either direction. -/
def underlying (N : RootedNetwork) : SimpleGraph ℕ where
  Adj u v := u ≠ v ∧ ((u,v) ∈ N.edges ∨ (v,u) ∈ N.edges)
  symm := ⟨by intro u v h; exact ⟨Ne.symm h.1, h.2.symm⟩⟩
  loopless := ⟨by intro v h; exact h.1 rfl⟩

/-- `N` is a rooted binary level-1 phylogenetic network on the taxa `N.taxa`:
* the root is a vertex, every edge joins two vertices, and every vertex is reachable from the
  root by a directed path;
* `N` has no directed cycle;
* the root has indegree 0 and outdegree 0 or 2;
* every other vertex is a leaf (indegree 1, outdegree 0), a tree vertex (indegree 1,
  outdegree 2) or a reticulation (indegree 2, outdegree 1);
* the vertices of outdegree 0 are the leaves `N.leaf a`, `a ∈ N.taxa`; each has indegree 1 (0 if
  it is the root), and distinct taxa label distinct leaves;
* level-1: two cycles of the underlying undirected graph with different edge sets have no vertex
  in common. A cycle is identified by its edge set, so that traversals of one cycle from
  different starting vertices or in opposite directions count as one cycle. -/
def RootedBinaryLevelOne (N : RootedNetwork) : Prop :=
  N.root ∈ N.vertices ∧
  (∀ e ∈ N.edges, e.1 ∈ N.vertices ∧ e.2 ∈ N.vertices) ∧
  (∀ v, ¬Relation.TransGen (fun u w => (u,w) ∈ N.edges) v v) ∧
  N.indegree N.root = 0 ∧ (N.outdegree N.root = 0 ∨ N.outdegree N.root = 2) ∧
  (∀ v ∈ N.vertices, Relation.ReflTransGen (fun u w => (u,w) ∈ N.edges) N.root v) ∧
  Set.InjOn N.leaf N.taxa ∧
  (∀ a ∈ N.taxa, N.leaf a ∈ N.vertices ∧
    N.indegree (N.leaf a) = (if N.leaf a = N.root then 0 else 1) ∧
    N.outdegree (N.leaf a) = 0) ∧
  (∀ v ∈ N.vertices, N.outdegree v = 0 ↔ ∃ a ∈ N.taxa, N.leaf a = v) ∧
  (∀ v ∈ N.vertices, v ≠ N.root →
    (N.indegree v = 1 ∧ N.outdegree v = 0) ∨
    (N.indegree v = 1 ∧ N.outdegree v = 2) ∨
    (N.indegree v = 2 ∧ N.outdegree v = 1)) ∧
  (∀ v w (c : N.underlying.Walk v v) (d : N.underlying.Walk w w),
    c.IsCycle → d.IsCycle → c.edges.toFinset ≠ d.edges.toFinset →
      Disjoint c.support.toFinset d.support.toFinset)

/-- `S` is a switching of `N`: a set of edges of `N` with exactly one edge into each non-root
vertex. In a rooted binary network, these are the edge sets of the trees of Definition 1,
obtained by deleting one of the two edges into each reticulation, taken before the clean-up
(suppressing the vertices with one parent and one child, deleting unlabelled leaves, and passing
to the unrooted tree). The clean-up does not change which splits of the taxa are cut by deleting
one edge, so `DisplaysQuartet` tests quartets on `S` itself. -/
def Switching (N : RootedNetwork) (S : Finset (ℕ × ℕ)) : Prop :=
  S ⊆ N.edges ∧ ∀ v ∈ N.vertices, v ≠ N.root →
    (S.filter (fun e => e.2 = v)).card = 1

/-- In the graph `G` on the vertices of `N`, the two sides of the quartet `q` are separated: the
two leaves of each side are connected in `G`, and no leaf of one side is connected to a leaf of
the other side. -/
def Separates (N : RootedNetwork) (G : SimpleGraph ℕ) (q : Quartet) : Prop :=
  (∀ a ∈ q.sides.1, ∀ b ∈ q.sides.1, G.Reachable (N.leaf a) (N.leaf b)) ∧
  (∀ a ∈ q.sides.2, ∀ b ∈ q.sides.2, G.Reachable (N.leaf a) (N.leaf b)) ∧
  (∀ a ∈ q.sides.1, ∀ b ∈ q.sides.2, ¬G.Reachable (N.leaf a) (N.leaf b))

/-- **Definition 1** (`mthst1`). `N` displays the quartet `q`: `q ∈ Q(N_r)`, the union of the
sets Q(t) over the trees t displayed by `N`. That is, the taxa of `q` are taxa of `N`, and some
switching `S` of `N` has an edge whose deletion from the underlying undirected graph of `S`
separates the two sides of `q`. -/
def DisplaysQuartet (N : RootedNetwork) (q : Quartet) : Prop :=
  q.taxa ⊆ N.taxa ∧ ∃ S, N.Switching S ∧
    ∃ e ∈ ({N with edges := S}).underlying.edgeSet,
      N.Separates (({N with edges := S}).underlying.deleteEdges {e}) q

end RootedNetwork

end Camus

namespace Camus

/-- The interior vertices of a path, given as the list of its vertices: all but the first and
the last. -/
def wireInterior (p : List ℕ) : Finset ℕ := p.tail.dropLast.toFinset

/-- The directed edges of a path, given as the list of its vertices: the pairs of consecutive
vertices. -/
def wireEdges (p : List ℕ) : Finset (ℕ × ℕ) := (p.zip p.tail).toFinset

/-- The switching `S` of `N` is a subdivision of `T` that keeps the root and the labelled leaves:
`N` is built on `T` (Definition 1), and the edges of `N` outside `S` are the edges added to `T`.
The map `original` sends the vertices of `T` injectively to vertices of `N`, and for each
non-root vertex `p` of `T`, `wire p` is the directed path of `N` that replaces the edge of `T`
from `parent p` to `p`. The laws:
* `original` sends the root of `T` to the root of `N` and the leaf of `T` labelled `a` to
  `N.leaf a`, and `N` has the taxa of `T`;
* each wire runs from `original (parent p)` to `original p` without repeating a vertex, and its
  interior vertices are not images of vertices of `T`;
* the interiors of distinct wires are disjoint;
* the vertices of `N` are the images of the vertices of `T` and the interior vertices of the
  wires, and `S` is the set of the edges of the wires;
* `S` is a switching of `N`. -/
structure SupportSubdivision (t : PhyloTree) (N : RootedNetwork)
    (S : Finset (ℕ × ℕ)) where
  original : Address → ℕ
  wire : Address → List ℕ
  original_injective : Set.InjOn original t.nodes
  root_preserved : original [] = N.root
  taxa_preserved : N.taxa = t.taxa
  leaves_preserved : ∀ p ∈ t.nodes, ∀ a, t.nodeAt p = some (.leaf a) →
    original p = N.leaf a
  wire_laws : ∀ p ∈ t.nodes, p ≠ [] →
    2 ≤ (wire p).length ∧ (wire p).Nodup ∧
    (wire p).head? = some (original (parent p)) ∧
    (wire p).getLast? = some (original p) ∧
    Disjoint (wireInterior (wire p)) (t.nodes.image original)
  interiors_disjoint :
    ((t.nodes.erase []) : Set Address).Pairwise
      (fun p q => Disjoint (wireInterior (wire p)) (wireInterior (wire q)))
  vertices_covered : N.vertices = t.nodes.image original ∪
    (t.nodes.erase []).biUnion (fun p => wireInterior (wire p))
  edges_covered : S = (t.nodes.erase []).biUnion (fun p => wireEdges (wire p))
  switching : N.Switching S

/-- `N` is built on `T` (Definition 1), with the root of `T` at the root of `N`: `N` is a rooted
binary level-1 network, and some switching of `N` is a subdivision of `T` that keeps the root and
the labelled leaves (`SupportSubdivision`). The root is kept as in Section 2.2, where no edge
begins above the root of `T`; asking only that `T` be a displayed tree of `N` would also allow
networks whose root lies above the root of `T`. -/
def RootedNetwork.AnchoredExtension (N : RootedNetwork) (t : PhyloTree) : Prop :=
  N.RootedBinaryLevelOne ∧ ∃ S, Nonempty (SupportSubdivision t N S)

/-- The switching `S` of `N` gives the tree `T` of Definition 1, with the root of `N` at or above
the root of `T`: `S` is `T` with each edge replaced by a directed path, below a directed path
`rootWire` of `S` from `N.root` to `original []` (`[N.root]` when the two roots coincide, the case
of `SupportSubdivision`). Deleting the edges outside `S` and cleaning up (suppressing the vertices
with one child, a root with one child included; a switching of a rooted binary level-1 network
leaves no unlabelled leaf) gives `T`. The laws are those of `SupportSubdivision`, with the root
wire: it runs from `N.root` to `original []` without repeating a vertex, its other vertices are not
images of vertices of `T` and avoid the interiors of the wires, and its vertices and edges are
vertices and edges of `N` and of `S`. -/
structure DisplayedSubdivision (t : PhyloTree) (N : RootedNetwork)
    (S : Finset (ℕ × ℕ)) where
  original : Address → ℕ
  wire : Address → List ℕ
  rootWire : List ℕ
  original_injective : Set.InjOn original t.nodes
  taxa_preserved : N.taxa = t.taxa
  leaves_preserved : ∀ p ∈ t.nodes, ∀ a, t.nodeAt p = some (.leaf a) →
    original p = N.leaf a
  rootWire_laws : rootWire.Nodup ∧ rootWire.head? = some N.root ∧
    rootWire.getLast? = some (original []) ∧
    Disjoint rootWire.dropLast.toFinset (t.nodes.image original)
  wire_laws : ∀ p ∈ t.nodes, p ≠ [] →
    2 ≤ (wire p).length ∧ (wire p).Nodup ∧
    (wire p).head? = some (original (parent p)) ∧
    (wire p).getLast? = some (original p) ∧
    Disjoint (wireInterior (wire p)) (t.nodes.image original)
  interiors_disjoint :
    ((t.nodes.erase []) : Set Address).Pairwise
      (fun p q => Disjoint (wireInterior (wire p)) (wireInterior (wire q)))
  rootWire_disjoint : ∀ p ∈ t.nodes, p ≠ [] →
    Disjoint rootWire.dropLast.toFinset (wireInterior (wire p))
  vertices_covered : N.vertices = t.nodes.image original ∪
    (t.nodes.erase []).biUnion (fun p => wireInterior (wire p)) ∪ rootWire.dropLast.toFinset
  edges_covered : S = (t.nodes.erase []).biUnion (fun p => wireEdges (wire p)) ∪
    wireEdges rootWire
  switching : N.Switching S

/-- **Definition 1** (`mthst1`). `N` is built on `T`: `N` is a rooted binary level-1 network and
`T` is one of its trees, the trees obtained by deleting one of the two edges into each reticulation
and cleaning up (`DisplayedSubdivision`). The root of `T` need not be the root of `N`; with the
root of `T` at the root of `N`, this is `RootedNetwork.AnchoredExtension`. -/
def RootedNetwork.BuiltOn (N : RootedNetwork) (t : PhyloTree) : Prop :=
  N.RootedBinaryLevelOne ∧ ∃ S, Nonempty (DisplayedSubdivision t N S)

/-- An isomorphism of rooted networks from `N` to `P`: a bijection between their vertex sets
that preserves and reflects the directed edges and preserves the root and the leaf of each
taxon; the two networks have the same taxa. -/
structure RootedNetwork.Iso (N P : RootedNetwork) where
  vertices : N.vertices ≃ P.vertices
  edges : ∀ u v : N.vertices,
    ((u.val,v.val) ∈ N.edges ↔ ((vertices u).val,(vertices v).val) ∈ P.edges)
  root_left : N.root ∈ N.vertices
  root_right : P.root ∈ P.vertices
  root_preserved : vertices ⟨N.root, root_left⟩ = ⟨P.root, root_right⟩
  taxa_preserved : N.taxa = P.taxa
  leaves_left : ∀ a ∈ N.taxa, N.leaf a ∈ N.vertices
  leaves_right : ∀ a ∈ N.taxa, P.leaf a ∈ P.vertices
  leaves_preserved : ∀ a (ha : a ∈ N.taxa),
    vertices ⟨N.leaf a, leaves_left a ha⟩ = ⟨P.leaf a, leaves_right a ha⟩

end Camus

namespace Camus

namespace Address

/-- The vertex identifier of the vertex `p` of `T` in the networks `Realization.graph`:
`code [] = 1`, and putting a step `b` in front of `p` gives `2 * code p`, plus 1 if `b = true`.
So the binary digits of `code p` are 1 followed by the steps of `p` from last to first. Codes are
positive and injective, and the new vertices u', w' get identifiers larger than all codes of
vertices of `T`. -/
def code : Address → ℕ
  | [] => 1
  | false :: p => 2 * code p
  | true :: p => 2 * code p + 1

end Address

namespace Realization

/-- A pair `(u, w)` of addresses, standing for the edge added above `(u, w)`. -/
abbrev Pair := Address × Address

/-- The largest code of a vertex of `T`. The new vertices of `Realization.graph` get identifiers
above it. -/
def bound (t : PhyloTree) : ℕ := t.nodes.sup Address.code

/-- The position of the pair `e` in a fixed enumeration of the admissible pairs of `T`. Distinct
admissible pairs get distinct positions. -/
noncomputable def index (t : PhyloTree) (e : Pair) : ℕ :=
  (EdgeAbove.candidates t).toList.idxOf e

/-- The identifier `bound t + 2 * index t e + 1` of the new vertex u' that subdivides the edge
above the donor `u` of the pair `e = (u, w)`. -/
noncomputable def donor (t : PhyloTree) (e : Pair) : ℕ :=
  bound t + 2 * index t e + 1

/-- The identifier `bound t + 2 * index t e + 2` of the new vertex w' that subdivides the edge
above the recipient `w` of the pair `e = (u, w)`; w' is the reticulation of the cycle γ(u, w). -/
noncomputable def recipient (t : PhyloTree) (e : Pair) : ℕ :=
  bound t + 2 * index t e + 2

/-- The new vertices on the edge of `T` above `p` whose cycles leave that edge upward, through
`parent p`: the donor u' of each pair `(p, w)` of `E` with target other than `p`, and the
recipient w' of each pair `(u, p)` of `E`. -/
noncomputable def outerEndpoints (t : PhyloTree) (E : Finset Pair) (p : Address) : List ℕ :=
  E.toList.flatMap fun e =>
    (if e.1 = p ∧ EdgeAbove.target e ≠ p then [donor t e] else []) ++
    (if e.2 = p then [recipient t e] else [])

/-- The new vertices on the edge of `T` above `p` whose cycles leave that edge downward, through
`p`: the donor u' of each pair `(p, w)` of `E` with target `p` (a ghost lineage). -/
noncomputable def ghostEndpoints (t : PhyloTree) (E : Finset Pair) (p : Address) : List ℕ :=
  E.toList.flatMap fun e =>
    if e.1 = p ∧ EdgeAbove.target e = p then [donor t e] else []

/-- The directed path of `Realization.graph t E` that replaces the edge of `T` from `parent p` to
`p`: the code of `parent p`, the vertices of `outerEndpoints`, the vertices of
`ghostEndpoints`, and the code of `p`. Two pairs with vertex-disjoint cycles can both put a new
vertex on this edge: one whose cycle leaves it upward, and a ghost donor whose cycle leaves it
downward. The cycles stay disjoint only if the ghost donor is the lower of the two. -/
noncomputable def wire (t : PhyloTree) (E : Finset Pair) (p : Address) : List ℕ :=
  [Address.code (parent p)] ++ outerEndpoints t E p ++
    ghostEndpoints t E p ++ [Address.code p]

/-- The edges of the subdivided tree `T` in `Realization.graph t E`: the edges of all the
wires. -/
noncomputable def supportEdges (t : PhyloTree) (E : Finset Pair) : Finset (ℕ × ℕ) :=
  (t.nodes.erase []).biUnion (fun p => wireEdges (wire t E p))

/-- The address of a leaf of `T` labelled `a` (the first one found, and the root `[]` if there
is none). For a well-labelled `T` and a taxon `a` of `T`, it is the leaf labelled `a`. -/
noncomputable def leafAddress (t : PhyloTree) (a : ℕ) : Address :=
  ((t.nodes.toList).find? (fun p => t.nodeAt p = some (.leaf a))).getD []

/-- **Definition 3** (`mthst6`). The network obtained from `T` by adding an edge above each pair
`e = (u, w)` of `E`: subdivide the edge above `u` by a new vertex u' (`donor t e`) and the edge
above `w` by a new vertex w' (`recipient t e`), and add the edge from u' to w'. Each such edge
creates the cycle γ(u, w), whose bottom vertex, the only one of indegree 2, is w'. A vertex `p`
of `T` is the vertex `Address.code p`, the new vertices get fresh identifiers above these codes,
and the root, the taxa and the labelled leaves are those of `T`. For one pair `e`, `graph t {e}`
is the network T + e, and `graph t ∅` is `T` itself. -/
noncomputable def graph (t : PhyloTree) (E : Finset Pair) : RootedNetwork :=
  { vertices := t.nodes.image Address.code ∪ E.biUnion (fun e => {donor t e, recipient t e})
    edges := supportEdges t E ∪ E.image (fun e => (donor t e, recipient t e))
    root := Address.code []
    taxa := t.taxa
    leaf := fun a => Address.code (leafAddress t a) }

/-- The vertices of the cycle γ(u, w) in T + e = `graph t {e}`, for `e = (u, w)`: the codes of
the vertices γ(u, w) ∩ V(T) (`EdgeAbove.footprint`) and the new vertices u' and w'. -/
noncomputable def cycleVertices (t : PhyloTree) (e : Pair) : Finset ℕ :=
  (EdgeAbove.footprint t e).image Address.code ∪ {donor t e, recipient t e}

/-- **Definition 5** (`mthst8`). The children l(p) (`b = false`) and r(p) (`b = true`) of a
vertex `p` of `T` in the network T + e = `graph t {e}`, for `e = (u, w)`: the new vertex u' if
the child of `p` in `T` is `u`, the new vertex w' if it is `w`, and the child of `p` in `T`
otherwise. Equations (4) and (5) test l(x) ∉ γ(u, w) with these children: at the parent of `w`,
the child `w` of `T` is off the cycle, but the child w' of T + e is on it. -/
noncomputable def child (t : PhyloTree) (e : Pair) (p : Address) (b : Bool) : ℕ :=
  let q := p ++ [b]
  if q = e.1 then donor t e else if q = e.2 then recipient t e else Address.code q

/-- The child off the cycle γ(u, w) of a vertex `p` of γ(u, w) ∩ V(T), as chosen in
Equations (4) and (5) for x = p: l(p) if l(p) ∉ γ(u, w), and r(p) otherwise, for the children of
`p` in T + e (`Realization.child`). The result is an address of `T`, `p ++ [false]` or
`p ++ [true]`. -/
noncomputable def offChild (t : PhyloTree) (e : Pair) (p : Address) : Address :=
  if child t e p false ∉ cycleVertices t e then p ++ [false] else p ++ [true]

end Realization
end Camus

namespace Camus

variable {α : Type*} [DecidableEq α]

/-- The number of elements of the multiset `Q`, counted with multiplicity, that lie in the finite
set `D`. For `D` the quartets displayed by a network `N` (`DynamicProgramming.repertoire Q N`),
this is the score of `N` (Section 2.2): the number of quartet trees in `Q` that also appear in
Q(N_r). -/
def score (Q : Multiset α) (D : Finset α) : ℕ :=
  (Q.filter (· ∈ D)).card

end Camus

namespace Camus

namespace DynamicProgramming

/-- A pair `(u, w)` of addresses, standing for the edge added above `(u, w)`. -/
abbrev Pair := Address × Address

/-- Pairs(v) (Section 2.2): the admissible pairs `(u, w)` with target lca(u, w) = `v`. The paper
takes all pairs of vertices of `T` with lca_T(u, w) = v (and u, w ≠ r when `v` is the root r),
and describes them as the pairs for which "the triplet (u, w, v) would be assigned to a non-tree
edge we would add to T". Admissibility (`EdgeAbove.Admissible`) keeps the pairs that give a
network: it removes the pairs with `w = v`, for which `w` is an ancestor of `u` or `u` itself
(the report's E4). The pairs `(v, w)` with `w` below `v` (ghost lineages) are kept. -/
def pairsAt (t : PhyloTree) (v : Address) : Finset Pair :=
  (EdgeAbove.candidates t).filter (fun e => EdgeAbove.target e = v)

/-- The roots of the subtrees of `T` hanging off the cycle γ(u, w), for `e = (u, w)`: the
vertices of `T` off the cycle whose parent is on it (the `frontier` of `EdgeAbove.footprint`).
For an admissible pair with target `v`: if `u ≠ v`, they are `u`, `w` and the off-cycle children
(`Realization.offChild`) of the vertices of γ(u, w) ∩ V(T) other than `v`; if `u = v`, they are
`w` and the off-cycle children of all the vertices of γ(u, w) ∩ V(T). These are the vertices
whose values Equations (4) and (5) add up. -/
def hanging (t : PhyloTree) (e : Pair) : Finset Address :=
  frontier t (EdgeAbove.footprint t e)

/-- **Equation (4)** (`E4`). For a pair `e = (u, w)` with target `v ≠ u`,
s_dp(v, u, w) = M[w] + M[u] + ∑_{x ∈ γ(u, w) ∩ V(T) ∖ {v}} M[c(x)], where c(x) = l(x) if
l(x) ∉ γ(u, w) and c(x) = r(x) otherwise (`Realization.offChild`, with the children of
Definition 5 in T + e). It adds the values of the subtrees of `T` hanging off γ(u, w). -/
noncomputable def sdpCross (t : PhyloTree) (M : Address → ℕ) (e : Pair) : ℕ :=
  M e.2 + M e.1 + ∑ x ∈ (EdgeAbove.footprint t e).erase (EdgeAbove.target e),
    M (Realization.offChild t e x)

/-- **Equation (5)** (`E5`). For a pair `e = (u, w)` with target `v = u` (a ghost lineage),
s_dp(v, u, w) = M[w] + ∑_{x ∈ γ(u, w) ∩ V(T)} M[c(x)], with c(x) as in Equation (4). It adds the
values of the subtrees of `T` hanging off γ(u, w). Here the sum includes `x = v`, which has one
child off the cycle, and there is no term M[u], since the cycle runs through `u`. -/
noncomputable def sdpGhost (t : PhyloTree) (M : Address → ℕ) (e : Pair) : ℕ :=
  M e.2 + ∑ x ∈ EdgeAbove.footprint t e, M (Realization.offChild t e x)

/-- s_dp(v, u, w) for the pair `e = (u, w)` with target `v`: Equation (5) if `v = u`, and
Equation (4) otherwise. -/
noncomputable def sdp (t : PhyloTree) (M : Address → ℕ) (e : Pair) : ℕ :=
  if EdgeAbove.target e = e.1 then sdpGhost t M e else sdpCross t M e

/-- **Equation (3)** (`E3`). s(v) = max over `(u, w) ∈ Pairs(v)` of s_e(u, w) + s_dp(v, u, w),
with s_e given by `weight`: the best value when an edge with target `v` is added. If Pairs(v) is
empty, as for a leaf `v`, then s(v) = 0. -/
noncomputable def s (t : PhyloTree) (weight : Pair → ℕ) (M : Address → ℕ) (v : Address) : ℕ :=
  (pairsAt t v).sup (fun e => weight e + sdp t M e)

/-- **Equation (2)** (`E2`). `M` is the DP array of Section 2.2 for the edge weights `weight`
(the s_e): for every vertex `v` of `T`, M[v] = 0 if `v` is a leaf, and
M[v] = max(M[l(v)] + M[r(v)], s(v)) otherwise, where l(v) and r(v) are the children of `v` in
`T`. Since s(v) only uses values of `M` strictly below `v`, these equations determine `M` on the
vertices of `T` from the leaves up. -/
def Array (t : PhyloTree) (weight : Pair → ℕ) (M : Address → ℕ) : Prop :=
  ∀ v ∈ t.nodes,
    match t.nodeAt v with
    | some (.leaf _) => M v = 0
    | some (.fork _ _) => M v = max (M (v ++ [false]) + M (v ++ [true])) (s t weight M v)
    | none => False

/-- The backtracking through the DP array `M` (Section 2.2): `Trace t weight M v E` says that the
family `E` of pairs is a result of backtracking from the vertex `v`. At a leaf, `E` is empty
(`leaf`). At a vertex `v` with M[v] = M[l(v)] + M[r(v)], `E` is the union of results at the two
children (`fork`). At a vertex `v` with M[v] = s_e(u, w) + s_dp(v, u, w) for a pair
`e = (u, w) ∈ Pairs(v)`, `E` consists of `e` and results at the roots of the subtrees hanging off
γ(u, w) (`gall`). -/
inductive Trace (t : PhyloTree) (weight : Pair → ℕ) (M : Address → ℕ) :
    Address → Finset Pair → Prop
  | leaf (v : Address) (a : ℕ) (node : t.nodeAt v = some (.leaf a)) :
      Trace t weight M v ∅
  | fork (v : Address) (l r : PhyloTree) (L R : Finset Pair)
      (node : t.nodeAt v = some (.fork l r))
      (left : Trace t weight M (v ++ [false]) L)
      (right : Trace t weight M (v ++ [true]) R)
      (chosen : M (v ++ [false]) + M (v ++ [true]) = M v) :
      Trace t weight M v (L ∪ R)
  | gall (v : Address) (e : Pair) (F : Address → Finset Pair)
      (edge : e ∈ pairsAt t v)
      (branches : ∀ r ∈ hanging t e, Trace t weight M r (F r))
      (chosen : weight e + sdp t M e = M v) :
      Trace t weight M v (insert e ((hanging t e).biUnion F))

/-- The quartets of `Q` displayed by `N`: the finite set of the distinct quartets `q` of `Q` with
`q ∈ Q(N_r)` (`RootedNetwork.DisplaysQuartet`). -/
noncomputable def repertoire (Q : Multiset Quartet) (N : RootedNetwork) : Finset Quartet := by
  classical
  exact Q.toFinset.filter N.DisplaysQuartet

/-- The quartets of `Q` satisfied by `N` (Section 2.1): those displayed by `N` and not by `T`,
where `T` is the network `Realization.graph t ∅`. For a well-labelled `T`, the quartets displayed
by that network are those of Q(T). -/
noncomputable def novel (t : PhyloTree) (Q : Multiset Quartet) (N : RootedNetwork) :
    Finset Quartet := repertoire Q N \ repertoire Q (Realization.graph t ∅)

/-- **Equation (1)** (`E1`). s_e(u, w) = ∑_{q ∈ Q} δ_T(q, (u, w)) for `e = (u, w)`: the number of
quartets of `Q`, counted with multiplicity, satisfied by the edge added above `(u, w)`, that is,
by T + e = `Realization.graph t {e}`. Here δ_T(q, (u, w)) (Definition 4) is the number of times
`q` appears in `Q` if `q` is satisfied by that edge, and 0 otherwise. The sum runs over the
distinct quartets of `Q`, reading `Q` as a weighted set as Section 2.3 allows: summing over all
`m` copies of a quartet of multiplicity `m` would count it m² times (the report's E3). -/
noncomputable def edgeWeight (t : PhyloTree) (Q : Multiset Quartet) (e : Pair) : ℕ :=
  ∑ q ∈ Q.toFinset, if q ∈ novel t Q (Realization.graph t {e}) then Q.count q else 0

end DynamicProgramming
end Camus

namespace Camus

namespace RootedNetwork

/-- The number of reticulations of `N`: its vertices of indegree 2. -/
noncomputable def reticulationCount (N : RootedNetwork) : ℕ := by
  classical
  exact (N.vertices.filter (fun v => N.indegree v = 2)).card

end RootedNetwork

end Camus

namespace Camus.BudgetDP

open DynamicProgramming

/-- The row kept from a finite set `S` of candidate values: empty if `S` is empty, and otherwise the
singleton of the maximum of `S`. -/
def best (S : Finset ℕ) : Finset ℕ := S.filter (fun z => z = S.sup id)

/-- The ways to split the budget `k` between two rows `A` and `B`: the sums `a + b` with `a ∈ A i`,
`b ∈ B j` and `i + j = k`. Followed by `best`, this is the max-plus convolution of the rows. -/
def convolution (A B : ℕ → Finset ℕ) (k : ℕ) : Finset ℕ :=
  (Finset.range (k+1)).biUnion fun i =>
    (A i ×ˢ B (k-i)).image (fun xy => xy.1 + xy.2)

/-- The knapsack over the subtrees `rs` hanging off a cycle: their rows are combined one at a time
by `convolution`, keeping only the maximum after each step, so every intermediate row is empty or a
singleton. -/
def forest (M : Address → ℕ → Finset ℕ) : List Address → ℕ → Finset ℕ
  | [], k => if k=0 then {0} else ∅
  | r::rs, k => best (convolution (M r) (forest M rs) k)

/-- Section 2.4, the formalization's recurrence: the candidate values of row `k` at the vertex `v`,
for edge weights `w` (in applications, `s_e` of Equation (1)). At a leaf, `0` for `k = 0` and none
otherwise. At an internal vertex, the values of `convolution` of the children's rows (no added edge
has target `v`, the first case of Equation (2)), together with, for `k ≥ 1`, the values `w e + z`
where `e ∈ Pairs(v)` and `z` is in row `k − 1` of the knapsack over the subtrees hanging off the
cycle of `e` (Equations (3)–(5)). -/
noncomputable def cases (t : PhyloTree) (w : Pair → ℕ) (M : Address → ℕ → Finset ℕ)
    (v : Address) (k : ℕ) : Finset ℕ :=
  match t.nodeAt v with
  | some (.leaf _) => if k=0 then {0} else ∅
  | some (.fork _ _) => convolution (M (v++[false])) (M (v++[true])) k ∪
      if k=0 then ∅ else (pairsAt t v).biUnion fun e =>
        (forest M (hanging t e).toList (k-1)).image (fun z => w e + z)
  | none => ∅

/-- Section 2.4: `M` satisfies the recurrence. At every vertex `v` of `T` and every budget `k`, the
row `M v k` is `best (cases t w M v k)`. Such an `M` exists (`exists_array`). -/
def Array (t : PhyloTree) (w : Pair → ℕ) (M : Address → ℕ → Finset ℕ) : Prop :=
  ∀ v ∈ t.nodes, ∀ k, M v k = best (cases t w M v k)

/-- Backtracking through the knapsack `forest M rs` (Section 2.4). `Knapsack M b s rs k z` says
that the budgets `b r` and the row values `s r ∈ M[r][b r]` of the subtrees `r ∈ rs` distribute the
budget `k` with total value `z`, and that the knapsack keeps each partial total: for
`rs = r :: rs'`, if the budgets of `rs'` add up to `k'` with total value `z'`, then `s r + z'` is
the value kept in row `b r + k'` of `forest M rs`. -/
inductive Knapsack (M : Address → ℕ → Finset ℕ) (b s : Address → ℕ) :
    List Address → ℕ → ℕ → Prop
  | nil : Knapsack M b s [] 0 0
  | cons (r : Address) (rs : List Address) (k z : ℕ)
      (row : s r ∈ M r (b r))
      (tail : Knapsack M b s rs k z)
      (chosen : s r + z ∈ forest M (r :: rs) (b r + k)) :
      Knapsack M b s (r :: rs) (b r + k) (s r + z)

/-- Section 2.4: the backtracking through the array `M` of the recurrence `BudgetDP.Array`, for
edge weights `w`. `Trace t w M v k E` says that the family `E` of pairs is a result of backtracking
from the vertex `v` with budget `k`.
* `leaf`: at a leaf, the budget is `0` and `E` is empty.
* `fork`: at an internal vertex, no added edge has target `v`. The budget is split as `i + j`
  between the two children, and `E` is the union of results there, whose row values `x` and `y`
  add up to the value kept in `M[v][i + j]`.
* `gall`: an edge `e ∈ Pairs(v)` is added, using one unit of budget. The remaining `k` units are
  distributed over the subtrees `r` hanging off the cycle of `e`, with budgets `b r` and values
  `s r` chosen by backtracking through the knapsack (`Knapsack`), and `E` consists of `e` and
  results at the hanging subtrees with these budgets; `w e` plus the knapsack value `z` is the value
  kept in `M[v][k + 1]`. -/
inductive Trace (t : PhyloTree) (w : Pair → ℕ) (M : Address → ℕ → Finset ℕ) :
    Address → ℕ → Finset Pair → Prop
  | leaf (v : Address) (a : ℕ) (node : t.nodeAt v = some (.leaf a)) :
      Trace t w M v 0 ∅
  | fork (v : Address) (l r : PhyloTree) (i j x y : ℕ) (L R : Finset Pair)
      (node : t.nodeAt v = some (.fork l r))
      (left : Trace t w M (v ++ [false]) i L)
      (right : Trace t w M (v ++ [true]) j R)
      (leftRow : x ∈ M (v ++ [false]) i)
      (rightRow : y ∈ M (v ++ [true]) j)
      (chosen : x + y ∈ M v (i + j)) :
      Trace t w M v (i + j) (L ∪ R)
  | gall (v : Address) (e : Pair) (k z : ℕ) (b s : Address → ℕ) (F : Address → Finset Pair)
      (edge : e ∈ pairsAt t v)
      (knapsack : Knapsack M b s (hanging t e).toList k z)
      (branches : ∀ r ∈ hanging t e, Trace t w M r (b r) (F r))
      (chosen : w e + z ∈ M v (k + 1)) :
      Trace t w M v (k + 1) (insert e ((hanging t e).biUnion F))

end Camus.BudgetDP

namespace Camus

open DynamicProgramming

/-- Section 2.4's claim that the best score never decreases as the number of reticulations
increases, read for exact numbers of reticulations, as the section computes them: for every
well-labelled tree `T`, multiset `Q` and `j ≤ k` such that some network built on `T` has exactly
`k` reticulations, every network built on `T` with exactly `j` reticulations displays at most as
many quartets of `Q` (with multiplicity) as some network built on `T` with exactly `k`
reticulations. For a fixed `T` the number of quartets of `Q` displayed and the number satisfied
differ by the number of quartets of `Q` that `T` induces, so the claim reads the same for
either. -/
def ExactCountMonotone : Prop :=
  ∀ t : PhyloTree, t.WellLabelled → ∀ (Q : Multiset Quartet) (j k : ℕ), j ≤ k →
    (∃ P : RootedNetwork, P.AnchoredExtension t ∧ P.reticulationCount = k) →
      ∀ N : RootedNetwork, N.AnchoredExtension t → N.reticulationCount = j →
        ∃ P : RootedNetwork, P.AnchoredExtension t ∧ P.reticulationCount = k ∧
          score Q (repertoire Q N) ≤ score Q (repertoire Q P)

/-- Section 3.2's claim: if the network `N` is built on the well-labelled tree `t` and the
quartets of the multiset `Q` are exactly those that `N` displays (`Q` is a multiset version of
`Q(N_r)`), then every network built on `t` that displays at least as many quartets of `Q` (with
multiplicity) as every network built on `t` is isomorphic to `N`. -/
def UniqueOptimum : Prop :=
  ∀ t : PhyloTree, t.WellLabelled → ∀ N : RootedNetwork, N.AnchoredExtension t →
    ∀ Q : Multiset Quartet, (∀ q, q ∈ Q ↔ N.DisplaysQuartet q) →
      ∀ P : RootedNetwork, P.AnchoredExtension t →
        (∀ R : RootedNetwork, R.AnchoredExtension t →
          score Q (repertoire Q R) ≤ score Q (repertoire Q P)) →
        Nonempty (P.Iso N)

/-- The best number of quartets of `Q`, counted with multiplicity, displayed by a network built on
`T` with exactly `k` reticulations, and `0` if there is no such network. -/
noncomputable def bestExact (t : PhyloTree) (Q : Multiset Quartet) (k : ℕ) : ℕ :=
  sSup {s | ∃ N : RootedNetwork, N.AnchoredExtension t ∧ N.reticulationCount = k ∧
    score Q (repertoire Q N) = s}

/-- The best number of quartets of `Q`, counted with multiplicity, displayed by a network built on
`T` with at most `k` reticulations. -/
noncomputable def bestAtMost (t : PhyloTree) (Q : Multiset Quartet) (k : ℕ) : ℕ :=
  sSup {s | ∃ N : RootedNetwork, N.AnchoredExtension t ∧ N.reticulationCount ≤ k ∧
    score Q (repertoire Q N) = s}

/-- Section 2.4's stopping rule on the scores `s 0, s 1, …` of the columns: columns are added "until
we no longer get an improvement in score", and `m` is "the number of reticulations after which the
score does not improve". The rule stops at `m` if the score improves at each column before `m`, and
does not improve from `m` to `m + 1`. -/
def StopsAt (s : ℕ → ℕ) (m : ℕ) : Prop :=
  (∀ j < m, s j < s (j + 1)) ∧ s (m + 1) ≤ s m

/-- Section 2.4's stopping rule, for exact numbers of reticulations, as the array of Section 2.4
computes them: for every well-labelled tree `T` and multiset `Q`, if the rule stops at `m` on the
best scores with exactly `k` reticulations, then the score does not improve after `m`: no network
built on `T` with `j ≥ m` reticulations displays more quartets of `Q` than the best network with
exactly `m`. For a fixed `T` the number of quartets of `Q` displayed and the number satisfied
differ by the number of quartets of `Q` that `T` induces, so the claim reads the same for
either. -/
def ExactStoppingRule : Prop :=
  ∀ t : PhyloTree, t.WellLabelled → ∀ (Q : Multiset Quartet) (m : ℕ),
    StopsAt (bestExact t Q) m → ∀ j, m ≤ j → bestExact t Q j ≤ bestExact t Q m

/-- Section 2.4's stopping rule, for "at most k" reticulations: for every well-labelled tree `T`
and multiset `Q`, if the rule stops at `m` on the best scores with at most `k` reticulations, then
no network built on `T` displays more quartets of `Q` than the best network with at most `m`
reticulations. -/
def AtMostStoppingRule : Prop :=
  ∀ t : PhyloTree, t.WellLabelled → ∀ (Q : Multiset Quartet) (m : ℕ),
    StopsAt (bestAtMost t Q) m → ∀ j, bestAtMost t Q j ≤ bestAtMost t Q m

end Camus

-- END SHARED DEFINITIONS

-- The definitions below are used by the proofs, not by the statements of `Challenge.lean`.

namespace Camus

namespace EdgeAbove

/-- The family `E` of pairs is cycle-separated: its pairs are admissible, and the cycles
γ(u, w) of distinct pairs of `E` have no vertex of `T` in common. As distinct pairs get distinct
new vertices, the cycles of `Realization.graph t E` are then vertex-disjoint: the network
obtained by adding an edge above each pair of `E` is level-1. -/
def CycleSeparated (t : PhyloTree) (E : Finset (Address × Address)) : Prop :=
  E ⊆ candidates t ∧
    (E : Set (Address × Address)).Pairwise
      (fun e f => Disjoint (footprint t e) (footprint t f))

end EdgeAbove

/-- `S` is a connected region of `T` with top vertex `p`: a set of vertices of `T` that contains
`p`, whose members are `p` and descendants of `p`, and that contains every vertex on the path
from `p` to each of its members. The vertices γ(u, w) ∩ V(T) of a cycle form such a region, with
top lca(u, w). -/
def TreeRegion (t : PhyloTree) (p : Address) (S : Finset Address) : Prop :=
  p ∈ S ∧ S ⊆ t.nodes ∧ ∀ x ∈ S,
    p <+: x ∧ ∀ y, p <+: y → y <+: x → y ∈ S

namespace RootedNetwork

/-- The first alternative of Observation 2 of Warnow, Tabatabaee and Evans: deleting one cut
edge of the underlying undirected graph of `N` separates the two sides of `q`. -/
def CutEdgeSeparates (N : RootedNetwork) (q : Quartet) : Prop :=
  ∃ e ∈ N.underlying.edgeSet, N.underlying.IsBridge e ∧
    N.Separates (N.underlying.deleteEdges {e}) q

/-- The second alternative of Observation 2 of Warnow, Tabatabaee and Evans: for some cycle `C`
of the underlying undirected graph of `N`, with a vertex `r` of indegree 2 on `C` (the
reticulation at the bottom of `C`), deleting two distinct edges of `C`, at least one of them
incident to `r`, separates the two sides of `q`. -/
def CycleSeparates (N : RootedNetwork) (q : Quartet) : Prop :=
  ∃ v, ∃ c : N.underlying.Walk v v, c.IsCycle ∧
    ∃ r ∈ c.support, N.indegree r = 2 ∧
      ∃ e ∈ c.edges, ∃ f ∈ c.edges, e ≠ f ∧ (r ∈ e ∨ r ∈ f) ∧
        N.Separates (N.underlying.deleteEdges {e,f}) q

end RootedNetwork

/-- The network `N` is a subdivision of the network `P`: `P` is obtained from `N` by suppressing
the interior vertices of the directed paths `wire (x, y)` that replace the edges `(x, y)` of `P`.
This makes precise the network T + e of Section 2.1, obtained from a network by deleting all
non-tree edges but `e` and suppressing the vertices of indegree and outdegree 1. The laws:
* `original` sends the vertices of `P` injectively to vertices of `N`, the root of `P` to the
  root of `N` and the leaf of each taxon to the leaf of that taxon, and `N` and `P` have the same
  taxa;
* each edge `(x, y)` of `P` joins two vertices of `P`, and its wire runs from `original x` to
  `original y` without repeating a vertex; the interior vertices of the wire are not images of
  vertices of `P`;
* the interiors of distinct wires are disjoint;
* the vertices of `N` are the images of the vertices of `P` and the interior vertices of the
  wires, and the edges of `N` are the edges of the wires. -/
structure GraphSubdivision (P N : RootedNetwork) where
  original : ℕ → ℕ
  wire : (ℕ × ℕ) → List ℕ
  original_injective : Set.InjOn original P.vertices
  root_left : P.root ∈ P.vertices
  root_preserved : original P.root = N.root
  taxa_preserved : N.taxa = P.taxa
  leaves_left : ∀ a ∈ P.taxa, P.leaf a ∈ P.vertices
  leaves_preserved : ∀ a ∈ P.taxa, original (P.leaf a) = N.leaf a
  edge_endpoints : ∀ e ∈ P.edges, e.1 ∈ P.vertices ∧ e.2 ∈ P.vertices
  wire_laws : ∀ e ∈ P.edges,
    2 ≤ (wire e).length ∧ (wire e).Nodup ∧
    (wire e).head? = some (original e.1) ∧
    (wire e).getLast? = some (original e.2) ∧
    Disjoint (wireInterior (wire e)) (P.vertices.image original)
  interiors_disjoint : (P.edges : Set (ℕ × ℕ)).Pairwise
    (fun e f => Disjoint (wireInterior (wire e)) (wireInterior (wire f)))
  vertices_covered : N.vertices = P.vertices.image original ∪
    P.edges.biUnion (fun e => wireInterior (wire e))
  edges_covered : N.edges = P.edges.biUnion (fun e => wireEdges (wire e))

namespace SupportSubdivision

/-- For a vertex `v` of `N` inside the wire of the edge of `T` above `p`, the address `p` of the
vertex of `T` directly below `v` (the wire is unique, since the interiors of distinct wires are
disjoint). For any other vertex the value is the root `[]`. -/
noncomputable def anchor {t : PhyloTree} {N : RootedNetwork}
    {S : Finset (ℕ × ℕ)} (H : SupportSubdivision t N S) (v : ℕ) : Address :=
  if h : ∃ p ∈ t.nodes, p ≠ [] ∧ v ∈ wireInterior (H.wire p) then
    Classical.choose h else []

/-- For an edge `e = (u', w')` of `N`, the pair `(u, w)` of vertices of `T` directly below `u'`
and `w'`, as in Procedure ASSIGN (Definition 2). For a non-tree edge of a rooted binary level-1
network built on `T`, both ends lie inside wires, and `e` is the edge added above `(u, w)`. -/
noncomputable def pairOf {t : PhyloTree} {N : RootedNetwork}
    {S : Finset (ℕ × ℕ)} (H : SupportSubdivision t N S) (e : ℕ × ℕ) :
    Address × Address := (H.anchor e.1, H.anchor e.2)

/-- The pairs `(u, w)` of the non-tree edges of `N` (the edges outside `S`). For a rooted binary
level-1 network `N`, this family is cycle-separated, and `N` is isomorphic to the network
obtained from `T` by adding an edge above each of these pairs (`Realization.graph`). -/
noncomputable def extracted {t : PhyloTree} {N : RootedNetwork}
    {S : Finset (ℕ × ℕ)} (H : SupportSubdivision t N S) :
    Finset (Address × Address) := by
  classical
  exact (N.edges \ S).image H.pairOf

end SupportSubdivision

namespace DynamicProgramming

/-- `E` is a feasible family below `v`: `E` is cycle-separated, and the target of each of its
pairs lies in the subtree `T_v` of `T` rooted at `v`. The paper's M[v] is the best value over
these families: the largest number of quartets of `Q` satisfied by a level-1 network obtained by
adding edges with targets in `T_v`. -/
def FeasibleBelow (t : PhyloTree) (v : Address) (E : Finset Pair) : Prop :=
  EdgeAbove.CycleSeparated t E ∧ ∀ e ∈ E, v <+: EdgeAbove.target e

/-- The total weight of the family `E`: the sum of `weight e` over the pairs `e` of `E`. -/
def value (weight : Pair → ℕ) (E : Finset Pair) : ℕ := ∑ e ∈ E, weight e

end DynamicProgramming

end Camus
