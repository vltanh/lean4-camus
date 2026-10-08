module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.List.FinRange
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace Camus

/-- A rooted full binary tree. Labels need not be distinct in storage; `WellLabelled`
expresses the defining leaf-labelling condition of a phylogenetic tree. -/
inductive PhyloTree where
  | leaf : ℕ → PhyloTree
  | fork : PhyloTree → PhyloTree → PhyloTree
  deriving DecidableEq, Repr

namespace PhyloTree

def labels : PhyloTree → List ℕ
  | .leaf a => [a]
  | .fork l r => labels l ++ labels r

def WellLabelled (t : PhyloTree) : Prop := t.labels.Nodup

instance (t : PhyloTree) : Decidable t.WellLabelled := inferInstanceAs (Decidable t.labels.Nodup)

def taxa (t : PhyloTree) : Finset ℕ := t.labels.toFinset

/-- Every rooted edge cuts off the clade at its lower endpoint. The whole-tree
clade is harmless and is included to simplify recursion. -/
def clades : PhyloTree → List (Finset ℕ)
  | .leaf a => [{a}]
  | .fork l r => (l.taxa ∪ r.taxa) :: (clades l ++ clades r)

end PhyloTree

/-- A resolved quartet, represented by four increasing taxon labels and one of
three splits. Sorted labels eliminate permutation duplicates. The ordering fields
are defining laws, not assumed mathematical results. -/
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

def taxa (q : Quartet) : Finset ℕ := {q.a, q.b, q.c, q.d}

def sides (q : Quartet) : Finset ℕ × Finset ℕ :=
  if q.split = 0 then ({q.a, q.b}, {q.c, q.d})
  else if q.split = 1 then ({q.a, q.c}, {q.b, q.d})
  else ({q.a, q.d}, {q.b, q.c})

/-- A clade induces the split if it contains precisely one side among the quartet's
four taxa. Other taxa in the clade do not affect restriction to the quartet. -/
def cutBy (q : Quartet) (s : Finset ℕ) : Bool :=
  decide (q.sides.1 ⊆ s ∧ Disjoint q.sides.2 s ∨
    q.sides.2 ⊆ s ∧ Disjoint q.sides.1 s)

/-- Definition 1 (`mthst1`): suppressing the root and restricting to four leaves
is equivalent to an edge cut separating the two pairs. -/
def induced (q : Quartet) (t : PhyloTree) : Bool :=
  decide (q.taxa ⊆ t.taxa) && t.clades.any q.cutBy

end Quartet

/-- Cycle-separated galled networks, written by their recursive blocks.
`gall l r b` is one directed cycle with top node, two directed paths to the
bottom reticulation, hanging subnetworks `l` and `r` along those paths, and
subnetwork `b` below the bottom. A nonempty path list supplies an intermediate
branch node, excluding a two-edge parallel cycle. Subnetworks attach by cut edges,
so different gall blocks are vertex-disjoint by construction.

This concrete grammar is used for checked examples. A completeness bridge from
arbitrary directed-graph networks is separate from the grammar's definitions. -/
inductive GalledNetwork where
  | leaf : ℕ → GalledNetwork
  | fork : GalledNetwork → GalledNetwork → GalledNetwork
  | gall (left right : List GalledNetwork) (bottom : GalledNetwork)
      : GalledNetwork
  deriving Repr

namespace GalledNetwork

/-- A path with hanging trees and a surviving bottom subtree. -/
def chain (ts : List PhyloTree) (bottom : PhyloTree) : PhyloTree :=
  ts.foldr PhyloTree.fork bottom

/-- A path after its bottom reticulation edge is deleted. Unary nodes are
suppressed; an empty path disappears. -/
def chainWithout : List PhyloTree → Option PhyloTree
  | [] => none
  | [t] => some t
  | t :: u :: ts => (chainWithout (u :: ts)).map (PhyloTree.fork t)

/-- Suppress a root of outdegree one after an incoming reticulation edge is
removed. A quartet set is insensitive to the remaining plane orientation. -/
def join (l r : Option PhyloTree) : Option PhyloTree :=
  match l, r with
  | some l, some r => some (.fork l r)
  | some t, none | none, some t => some t
  | none, none => none

/-- The two choices at one gall, after choices in its attached subnetworks.
One path retains its bottom edge and the other loses it. -/
def gallTrees (l r : List PhyloTree) (b : PhyloTree) : List PhyloTree :=
  (join (some (chain l b)) (chainWithout r)).toList ++
    (join (chainWithout l) (some (chain r b))).toList

/-- Choose a displayed tree for every hanging subnetwork. -/
def choices (xs : List (List PhyloTree)) : List (List PhyloTree) :=
  xs.foldr (fun s acc => s.flatMap fun t => acc.map (t :: ·)) [[]]

/-- Definition 1: delete one incoming edge per reticulation in every possible
way. Duplicates are allowed in this list and disappear in the displayed-quartet
predicate. -/
def displayed : GalledNetwork → List PhyloTree
  | .leaf a => [.leaf a]
  | .fork l r => (displayed l).flatMap fun a => (displayed r).map (.fork a ·)
  | .gall l r b =>
    (choices (l.map displayed)).flatMap fun ls =>
      (choices (r.map displayed)).flatMap fun rs =>
        (displayed b).flatMap fun bs => gallTrees ls rs bs
termination_by n => sizeOf n

def reticulations : GalledNetwork → ℕ
  | .leaf _ => 0
  | .fork l r => reticulations l + reticulations r
  | .gall l r b => 1 + (l.map reticulations).sum +
      (r.map reticulations).sum + reticulations b
termination_by n => sizeOf n

def labels : GalledNetwork → List ℕ
  | .leaf a => [a]
  | .fork l r => labels l ++ labels r
  | .gall l r b => (l.flatMap labels) ++ (r.flatMap labels) ++ labels b
termination_by n => sizeOf n

/-- Every gall has at least one intermediate branch node; all hanging networks
are themselves valid. Together with distinct labels this is the defining law of
our cycle-separated binary-network representation. -/
def Valid : GalledNetwork → Prop
  | .leaf _ => True
  | .fork l r => Valid l ∧ Valid r
  | .gall l r b => (l ≠ [] ∨ r ≠ []) ∧
      (∀ x ∈ l, Valid x) ∧ (∀ x ∈ r, Valid x) ∧ Valid b
termination_by n => sizeOf n

def WellLabelled (n : GalledNetwork) : Prop := n.labels.Nodup

def Phylogenetic (n : GalledNetwork) : Prop := n.Valid ∧ n.WellLabelled

instance (n : GalledNetwork) : Decidable n.WellLabelled :=
  inferInstanceAs (Decidable n.labels.Nodup)

def containsQuartet (n : GalledNetwork) (q : Quartet) : Bool :=
  n.displayed.any q.induced

/-- The extension relation keeps the actual displayed constraint tree, rather
than only its leaf labels. -/
def Extends (n : GalledNetwork) (t : PhyloTree) : Prop := t ∈ n.displayed

instance (n : GalledNetwork) (t : PhyloTree) : Decidable (n.Extends t) :=
  inferInstanceAs (Decidable (t ∈ n.displayed))

/-- Definition 1's novel satisfaction excludes quartets in the constraint tree. -/
def satisfies (n : GalledNetwork) (t : PhyloTree) (q : Quartet) : Bool :=
  n.containsQuartet q && !q.induced t

end GalledNetwork

end Camus
