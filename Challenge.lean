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

/-!
Statements of record for CAMUS: scalable phylogenetic network estimation.

The main theorem is CONDITIONAL on Observation 2 of Warnow, Tabatabaee and
Evans (2025), DOI 10.1089/cmb.2024.0710. That hypothesis describes quartet
separation by a bridge or by two cycle edges, one incident to its bottom.
It does not assume quartet uniqueness, network decomposition, or optimality.

Rooted binary level-1 networks are finite directed acyclic leaf-labelled graphs
whose undirected cycles are vertex-disjoint. An anchored extension retains the
constraint tree as a root-preserving support subdivision. CAMUS uses the
paper's bottom-up recurrence and its backtracking trace. Its result maximizes
novel quartet satisfaction over every such graph extension; the equivalent
total-support maximization and equality to the root array value are explicit.

Equation (1) sums multiplicities once over distinct quartet support. The
at-most-budget theorem replaces the false exact-budget claim of §2.4. Corrected
§3.2 recovery is a user-authorized new result with explicit identifiability under
repertoire inclusion and minimum-reticulation tie-breaking. It does not assert
these additional hypotheses for a biological model.

The shared definitions are copied verbatim from Camus/Definitions.lean and
contain data and defining laws only. Their graph and forest bridges belong to
the Solution; no decomposition or optimality assumption is stored in data.
-/

@[expose] public section

-- BEGIN SHARED DEFINITIONS

namespace Camus

abbrev Address := List Bool

end Camus

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

end Camus

namespace Camus

namespace PhyloTree

def nodes : PhyloTree → Finset Address
  | .leaf _ => {[]}
  | .fork l r => insert []
      ((l.nodes.image (false :: ·)) ∪ (r.nodes.image (true :: ·)))

def nodeAt : PhyloTree → Address → Option PhyloTree
  | t, [] => some t
  | .leaf _, _ :: _ => none
  | .fork l _, false :: p => nodeAt l p
  | .fork _ r, true :: p => nodeAt r p

end PhyloTree

/-- The actual least common ancestor address, computed as the longest common
prefix. It is not an unspecified target function supplied with assumed laws. -/
def lca : Address → Address → Address
  | [], _ => []
  | _ :: _, [] => []
  | a :: p, b :: q => if a = b then a :: lca p q else []

namespace EdgeAbove

/-- Definition 3's permitted endpoints. Incoming root edges do not exist, and
a recipient that is an ancestor of the donor would create a directed cycle.
The distinctness condition follows from the latter prohibition. -/
def Admissible (t : PhyloTree) (e : Address × Address) : Prop :=
  e.1 ∈ t.nodes ∧ e.2 ∈ t.nodes ∧ e.1 ≠ [] ∧ e.2 ≠ [] ∧ ¬e.2 <+: e.1

instance (t : PhyloTree) (e : Address × Address) : Decidable (Admissible t e) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

def candidates (t : PhyloTree) : Finset (Address × Address) :=
  (t.nodes ×ˢ t.nodes).filter (Admissible t)

def target (e : Address × Address) : Address := lca e.1 e.2

/-- Original tree vertices on the created undirected cycle: from the LCA to
each subdivided incoming edge, excluding the endpoint subtrees themselves.
The ghost case includes the donor vertex through the recipient's path. -/
def footprint (t : PhyloTree) (e : Address × Address) : Finset Address :=
  t.nodes.filter fun x => target e <+: x ∧
    ((x <+: e.1 ∧ x ≠ e.1) ∨ (x <+: e.2 ∧ x ≠ e.2))

/-- Cycle-separated endpoint families in the original tree. A bridge to the
directed graph realization is proved separately; it is not assumed here. -/
def CycleSeparated (t : PhyloTree) (E : Finset (Address × Address)) : Prop :=
  E ⊆ candidates t ∧
    (E : Set (Address × Address)).Pairwise
      (fun e f => Disjoint (footprint t e) (footprint t f))

end EdgeAbove
end Camus

namespace Camus

def parent (p : Address) : Address := p.take (p.length - 1)

/-- A connected set of original tree vertices below p: every intermediate
ancestor from p to a member is a member. This elementary geometric property is
proved for every cycle footprint and supplies the hanging-subtree partition. -/
def TreeRegion (t : PhyloTree) (p : Address) (S : Finset Address) : Prop :=
  p ∈ S ∧ S ⊆ t.nodes ∧ ∀ x ∈ S,
    p <+: x ∧ ∀ y, p <+: y → y <+: x → y ∈ S

def frontier (t : PhyloTree) (S : Finset Address) : Finset Address :=
  t.nodes.filter fun x => x ≠ [] ∧ parent x ∈ S ∧ x ∉ S

end Camus

namespace Camus

/-- Finite directed network data. Defining laws are stated separately in
`RootedBinaryLevelOne`; this structure contains no assumed theorem. Labels
identify leaves and are not used as internal vertex identifiers. -/
structure RootedNetwork where
  vertices : Finset ℕ
  edges : Finset (ℕ × ℕ)
  root : ℕ
  taxa : Finset ℕ
  leaf : ℕ → ℕ

namespace RootedNetwork

def indegree (N : RootedNetwork) (v : ℕ) : ℕ :=
  (N.edges.filter (fun e => e.2 = v)).card

def outdegree (N : RootedNetwork) (v : ℕ) : ℕ :=
  (N.edges.filter (fun e => e.1 = v)).card

def underlying (N : RootedNetwork) : SimpleGraph ℕ where
  Adj u v := u ≠ v ∧ ((u,v) ∈ N.edges ∨ (v,u) ∈ N.edges)
  symm := ⟨by intro u v h; exact ⟨Ne.symm h.1, h.2.symm⟩⟩
  loopless := ⟨by intro v h; exact h.1 rfl⟩

/-- Standard rooted binary, directed acyclic, leaf-labelled network laws and
vertex-disjoint undirected cycles. Two traversals of the same cycle are
identified by their edge sets. This is a definition of the source's object,
not a decomposition or optimality assumption. -/
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

/-- Deleting one incoming reticulation edge keeps precisely one incoming edge
at each non-root vertex. Suppression of unary vertices is unnecessary for the
edge-separation test for unrooted quartets. The suppression/restriction bridge
is proved separately and is not part of this definition. -/
def Switching (N : RootedNetwork) (S : Finset (ℕ × ℕ)) : Prop :=
  S ⊆ N.edges ∧ ∀ v ∈ N.vertices, v ≠ N.root →
    (S.filter (fun e => e.2 = v)).card = 1

/-- The two pairs lie in two different connected components, each pair remaining
connected. This uses the quartet's unordered split, independent of its spelling. -/
def Separates (N : RootedNetwork) (G : SimpleGraph ℕ) (q : Quartet) : Prop :=
  (∀ a ∈ q.sides.1, ∀ b ∈ q.sides.1, G.Reachable (N.leaf a) (N.leaf b)) ∧
  (∀ a ∈ q.sides.2, ∀ b ∈ q.sides.2, G.Reachable (N.leaf a) (N.leaf b)) ∧
  (∀ a ∈ q.sides.1, ∀ b ∈ q.sides.2, ¬G.Reachable (N.leaf a) (N.leaf b))

def DisplaysQuartet (N : RootedNetwork) (q : Quartet) : Prop :=
  q.taxa ⊆ N.taxa ∧ ∃ S, N.Switching S ∧
    ∃ e ∈ ({N with edges := S}).underlying.edgeSet,
      N.Separates (({N with edges := S}).underlying.deleteEdges {e}) q

def CutEdgeSeparates (N : RootedNetwork) (q : Quartet) : Prop :=
  ∃ e ∈ N.underlying.edgeSet, N.underlying.IsBridge e ∧
    N.Separates (N.underlying.deleteEdges {e}) q

def CycleSeparates (N : RootedNetwork) (q : Quartet) : Prop :=
  ∃ v, ∃ c : N.underlying.Walk v v, c.IsCycle ∧
    ∃ r ∈ c.support, N.indegree r = 2 ∧
      ∃ e ∈ c.edges, ∃ f ∈ c.edges, e ≠ f ∧ (r ∈ e ∨ r ∈ f) ∧
        N.Separates (N.underlying.deleteEdges {e,f}) q

end RootedNetwork

end Camus

namespace Camus

def wireInterior (p : List ℕ) : Finset ℕ := p.tail.dropLast.toFinset

def wireEdges (p : List ℕ) : Finset (ℕ × ℕ) := (p.zip p.tail).toFinset

/-- The defining data and laws of a root-preserving subdivision of T forming
a switching of N. Each original edge has an ordered directed wire; wire
interiors are disjoint and consist precisely of added vertices. No cycle
decomposition, quartet attribution, or optimization claim is a field. -/
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

/-- Root-preserving 'built upon T': the graph is a rooted binary level-1 network
with T as an explicitly subdivided support switching. This retains the root,
which bare membership among suppressed displayed trees does not guarantee. -/
def RootedNetwork.AnchoredExtension (N : RootedNetwork) (t : PhyloTree) : Prop :=
  N.RootedBinaryLevelOne ∧ ∃ S, Nonempty (SupportSubdivision t N S)

/-- A root- and taxon-preserving directed graph isomorphism on the finite vertex
sets. Its propositional fields are precisely the defining isomorphism laws. -/
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

/-- A directed graph subdivision. Suppressing the wire interiors of N recovers
P, retaining its root and labelled leaves. This gives an explicit meaning to
suppression when reducing a full extension to T plus one retained edge. -/
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

/-- The lower original vertex of the wire containing an added endpoint. Outside
wire interiors the fallback is the root; endpoint classification proves that
fallback is never used for a deleted reticulation edge. -/
noncomputable def anchor {t : PhyloTree} {N : RootedNetwork}
    {S : Finset (ℕ × ℕ)} (H : SupportSubdivision t N S) (v : ℕ) : Address :=
  if h : ∃ p ∈ t.nodes, p ≠ [] ∧ v ∈ wireInterior (H.wire p) then
    Classical.choose h else []

/-- Definition 2 (`mthst3`): the endpoints below the selected non-tree edge.
Lemma 1 proves the unique quartet attribution used by Procedure ASSIGN. -/
noncomputable def pairOf {t : PhyloTree} {N : RootedNetwork}
    {S : Finset (ℕ × ℕ)} (H : SupportSubdivision t N S) (e : ℕ × ℕ) :
    Address × Address := (H.anchor e.1, H.anchor e.2)

noncomputable def extracted {t : PhyloTree} {N : RootedNetwork}
    {S : Finset (ℕ × ℕ)} (H : SupportSubdivision t N S) :
    Finset (Address × Address) := by
  classical
  exact (N.edges \ S).image H.pairOf

end SupportSubdivision
end Camus

namespace Camus

namespace Address

/-- Positive binary encoding of vertex addresses; fresh subdivision identifiers
will be above the largest original identifier. -/
def code : Address → ℕ
  | [] => 1
  | false :: p => 2 * code p
  | true :: p => 2 * code p + 1

end Address

namespace Realization

abbrev Pair := Address × Address

def bound (t : PhyloTree) : ℕ := t.nodes.sup Address.code

noncomputable def index (t : PhyloTree) (e : Pair) : ℕ :=
  (EdgeAbove.candidates t).toList.idxOf e

noncomputable def donor (t : PhyloTree) (e : Pair) : ℕ :=
  bound t + 2 * index t e + 1

noncomputable def recipient (t : PhyloTree) (e : Pair) : ℕ :=
  bound t + 2 * index t e + 2

/-- On a shared original wire, the endpoint of the outer cycle comes before an
inner ghost donor. Distinct disjoint cycles may share an original wire, so a
one-subdivision-per-wire implementation would lose legitimate networks. -/
noncomputable def outerEndpoints (t : PhyloTree) (E : Finset Pair) (p : Address) : List ℕ :=
  E.toList.flatMap fun e =>
    (if e.1 = p ∧ EdgeAbove.target e ≠ p then [donor t e] else []) ++
    (if e.2 = p then [recipient t e] else [])

noncomputable def ghostEndpoints (t : PhyloTree) (E : Finset Pair) (p : Address) : List ℕ :=
  E.toList.flatMap fun e =>
    if e.1 = p ∧ EdgeAbove.target e = p then [donor t e] else []

noncomputable def wire (t : PhyloTree) (E : Finset Pair) (p : Address) : List ℕ :=
  [Address.code (parent p)] ++ outerEndpoints t E p ++
    ghostEndpoints t E p ++ [Address.code p]

noncomputable def supportEdges (t : PhyloTree) (E : Finset Pair) : Finset (ℕ × ℕ) :=
  (t.nodes.erase []).biUnion (fun p => wireEdges (wire t E p))

noncomputable def leafAddress (t : PhyloTree) (a : ℕ) : Address :=
  ((t.nodes.toList).find? (fun p => t.nodeAt p = some (.leaf a))).getD []

/-- Definition 3 (`mthst6`): insert the directed donor→recipient edges into the canonically subdivided
constraint tree. No theorem is assumed by this construction. -/
noncomputable def graph (t : PhyloTree) (E : Finset Pair) : RootedNetwork :=
  { vertices := t.nodes.image Address.code ∪ E.biUnion (fun e => {donor t e, recipient t e})
    edges := supportEdges t E ∪ E.image (fun e => (donor t e, recipient t e))
    root := Address.code []
    taxa := t.taxa
    leaf := fun a => Address.code (leafAddress t a) }

/-- The full vertex set of the single-edge cycle includes the two new
subdivision vertices as well as the original path footprint. -/
noncomputable def cycleVertices (t : PhyloTree) (e : Pair) : Finset ℕ :=
  (EdgeAbove.footprint t e).image Address.code ∪ {donor t e, recipient t e}

/-- Left/right children in the SUBDIVIDED single-edge network. This realizes
Definition 5 (`mthst8`); testing only original children against the original footprint
would choose the wrong branch at a subdivision endpoint. -/
noncomputable def child (t : PhyloTree) (e : Pair) (p : Address) (b : Bool) : ℕ :=
  let q := p ++ [b]
  if q = e.1 then donor t e else if q = e.2 then recipient t e else Address.code q

noncomputable def offChild (t : PhyloTree) (e : Pair) (p : Address) : Address :=
  if child t e p false ∉ cycleVertices t e then p ++ [false] else p ++ [true]

end Realization
end Camus

namespace Camus

variable {α : Type*} [DecidableEq α]

/-- Count occurrences, including multiplicity, of the input quartets in a repertoire. -/
def score (Q : Multiset α) (D : Finset α) : ℕ :=
  (Q.filter (· ∈ D)).card

end Camus

namespace Camus

namespace DynamicProgramming

abbrev Pair := Address × Address

def pairsAt (t : PhyloTree) (v : Address) : Finset Pair :=
  (EdgeAbove.candidates t).filter (fun e => EdgeAbove.target e = v)

def hanging (t : PhyloTree) (e : Pair) : Finset Address :=
  frontier t (EdgeAbove.footprint t e)

/-- Equation (4) (`E4`), including the two endpoint subtrees. -/
noncomputable def sdpCross (t : PhyloTree) (M : Address → ℕ) (e : Pair) : ℕ :=
  M e.2 + M e.1 + ∑ x ∈ (EdgeAbove.footprint t e).erase (EdgeAbove.target e),
    M (Realization.offChild t e x)

/-- Equation (5) (`E5`), including the target's off-cycle child for a ghost donor. -/
noncomputable def sdpGhost (t : PhyloTree) (M : Address → ℕ) (e : Pair) : ℕ :=
  M e.2 + ∑ x ∈ EdgeAbove.footprint t e, M (Realization.offChild t e x)

/-- The paper's actual two-case formula. Its equality with the hanging-forest
sum is a proved representation bridge, not an assumed decomposition law. -/
noncomputable def sdp (t : PhyloTree) (M : Address → ℕ) (e : Pair) : ℕ :=
  if EdgeAbove.target e = e.1 then sdpGhost t M e else sdpCross t M e

/-- Equation (3) (`E3`). Empty candidate families have value zero for the nonnegative
novel-quartet objective, so no phantom edge is selected. -/
noncomputable def s (t : PhyloTree) (weight : Pair → ℕ) (M : Address → ℕ) (v : Address) : ℕ :=
  (pairsAt t v).sup (fun e => weight e + sdp t M e)

/-- Equation (2) (`E2`): the defining bottom-up array equations, including the leaf base case.
This proposition assumes only that M is the array computed by the recurrence;
it contains no feasibility decomposition or optimality conclusion. -/
def Array (t : PhyloTree) (weight : Pair → ℕ) (M : Address → ℕ) : Prop :=
  ∀ v ∈ t.nodes,
    match t.nodeAt v with
    | some (.leaf _) => M v = 0
    | some (.fork _ _) => M v = max (M (v ++ [false]) + M (v ++ [true])) (s t weight M v)
    | none => False

/-- A backtracking trace records the paper's two cases. Its fields specify
which maximizing branch was taken and traces on the hanging subproblems.
Feasibility and equality with the global optimum are proved from these rules;
neither is a constructor assumption. -/
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

def FeasibleBelow (t : PhyloTree) (v : Address) (E : Finset Pair) : Prop :=
  EdgeAbove.CycleSeparated t E ∧ ∀ e ∈ E, v <+: EdgeAbove.target e

def value (weight : Pair → ℕ) (E : Finset Pair) : ℕ := ∑ e ∈ E, weight e

/-- Distinct-quartet weighted support in a directed graph, restricted to the
finite observed repertoire. Noncomputability is logical decidability of graph
reachability, not an added correctness hypothesis. -/
noncomputable def repertoire (Q : Multiset Quartet) (N : RootedNetwork) : Finset Quartet := by
  classical
  exact Q.toFinset.filter N.DisplaysQuartet

noncomputable def novel (t : PhyloTree) (Q : Multiset Quartet) (N : RootedNetwork) :
    Finset Quartet := repertoire Q N \ repertoire Q (Realization.graph t ∅)

/-- Equation (1) (`E1`) with the single-edge graph built above the actual endpoints. -/
noncomputable def edgeWeight (t : PhyloTree) (Q : Multiset Quartet) (e : Pair) : ℕ :=
  ∑ q ∈ Q.toFinset, if q ∈ novel t Q (Realization.graph t {e}) then Q.count q else 0

end DynamicProgramming
end Camus

-- END SHARED DEFINITIONS

namespace CamusResults

/-- Equation (1), with the weighted-support reading of §2.3. -/
theorem equation1 {α : Type*} [DecidableEq α] (Q : Multiset α) (D : Finset α) :
    (Q.filter (· ∈ D)).card =
      ∑ q ∈ Q.toFinset, if q ∈ D then Q.count q else 0 := by
  sorry

/-- Authorized corrected §2.4: nesting holds for at-most budgets. -/
theorem atMostBudgetMonotone {α N : Type*} [DecidableEq α] [DecidableEq N]
    (C : Finset N) (displayed : N → Finset α) (reticulations : N → ℕ)
    (Q : Multiset α) {j k : ℕ} (hjk : j ≤ k) :
    (C.filter (fun n => reticulations n ≤ j)).sup
        (fun n => (Q.filter (· ∈ displayed n)).card) ≤
      (C.filter (fun n => reticulations n ≤ k)).sup
        (fun n => (Q.filter (· ∈ displayed n)).card) := by
  sorry

/-- Authorized corrected §3.2: explicit identifiability and a tie-break give
deterministic recovery up to the application's stated equivalence. -/
theorem correctedRecovery {α N : Type*} [DecidableEq α]
    (C : Finset N) (displayed : N → Finset α) (reticulations : N → ℕ)
    (equivalent : N → N → Prop) (truth selected : N)
    (truth_feasible : truth ∈ C) (Q : Multiset α)
    (exact_support : Q.toFinset = displayed truth)
    (identifiable : ∀ n ∈ C, displayed truth ⊆ displayed n →
      reticulations n ≤ reticulations truth → equivalent n truth)
    (optimal : selected ∈ C ∧ ∀ m ∈ C,
      (Q.filter (· ∈ displayed m)).card ≤ (Q.filter (· ∈ displayed selected)).card)
    (tie_break : ∀ m ∈ C,
      (m ∈ C ∧ ∀ n ∈ C,
        (Q.filter (· ∈ displayed n)).card ≤ (Q.filter (· ∈ displayed m)).card) →
      reticulations selected ≤ reticulations m) :
    equivalent selected truth := by
  sorry


/-- Theorem 1: the full conditional optimality statement, with novel and total
support related explicitly. The root and all support-tree laws are retained. -/
theorem optimalNetwork
    (WarnowTabatabaeeEvansObservation2 :
      ∀ N : Camus.RootedNetwork, N.RootedBinaryLevelOne →
        ∀ q : Camus.Quartet, q.taxa ⊆ N.taxa →
          (N.DisplaysQuartet q ↔ N.CutEdgeSeparates q ∨ N.CycleSeparates q))
    (t : Camus.PhyloTree) (ht : t.WellLabelled) (Q : Multiset Camus.Quartet)
    (M : Camus.Address → ℕ)
    (hM : Camus.DynamicProgramming.Array t (Camus.DynamicProgramming.edgeWeight t Q) M)
    (E : Finset Camus.DynamicProgramming.Pair)
    (trace : Camus.DynamicProgramming.Trace t (Camus.DynamicProgramming.edgeWeight t Q) M [] E) :
    (Camus.Realization.graph t E).AnchoredExtension t ∧
      Camus.score Q (Camus.DynamicProgramming.novel t Q (Camus.Realization.graph t E)) = M [] ∧
      (∀ N : Camus.RootedNetwork, N.AnchoredExtension t →
        Camus.score Q (Camus.DynamicProgramming.novel t Q N) ≤
          Camus.score Q (Camus.DynamicProgramming.novel t Q (Camus.Realization.graph t E))) ∧
      (∀ N : Camus.RootedNetwork, N.AnchoredExtension t →
        Camus.score Q (Camus.DynamicProgramming.repertoire Q N) ≤
          Camus.score Q (Camus.DynamicProgramming.repertoire Q (Camus.Realization.graph t E))) := by
  sorry

end CamusResults
