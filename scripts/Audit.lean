module

public meta import Lean.Elab.Command
public meta import Lean.DocString
-- One `import all` line per module of the library, so that proofs are visible to the dependency
-- traversal (the module system hides them from a plain `import`). Generate the lines with
--   find Camus -name '*.lean' | sort | sed 's/\.lean$//; s#/#.#g; s/^/import all /'
import all Camus.Complexity.Operations
import all Camus.Complexity.Oracle
import all Camus.DP.Correctness
import all Camus.DP.Frontier
import all Camus.DP.Packing
import all Camus.DP.Theorem1
import all Camus.Defs
import all Camus.External.WarnowTabatabaeeEvans.Observation2
import all Camus.Galled.Basic
import all Camus.Galled.Bounds
import all Camus.Galled.Counterexamples
import all Camus.Galled.TreeIsomorphism
import all Camus.Galled.Triangles
import all Camus.Network.Baseline.Clades
import all Camus.Network.Baseline.Cuts
import all Camus.Network.Baseline.Main
import all Camus.Network.Code
import all Camus.Network.Completeness.AddEdge
import all Camus.Network.Completeness.Admissible
import all Camus.Network.Completeness.Anchors
import all Camus.Network.Completeness.Baseline
import all Camus.Network.Completeness.CanonicalWires
import all Camus.Network.Completeness.Cycles
import all Camus.Network.Completeness.Decode
import all Camus.Network.Completeness.Degrees
import all Camus.Network.Completeness.Encoding
import all Camus.Network.Completeness.Footprints
import all Camus.Network.Completeness.Iso
import all Camus.Network.Completeness.Main
import all Camus.Network.Completeness.Order
import all Camus.Network.Completeness.Reachability
import all Camus.Network.Completeness.Reduction
import all Camus.Network.Completeness.Splitting
import all Camus.Network.Completeness.Transport
import all Camus.Network.Completeness.Tree
import all Camus.Network.Completeness.Wires
import all Camus.Network.Cuts
import all Camus.Network.Isomorphism.Invariance
import all Camus.Network.Isomorphism.Rename
import all Camus.Network.Realization.Basic
import all Camus.Network.Realization.Binary
import all Camus.Network.Realization.Cactus
import all Camus.Network.Realization.Cones
import all Camus.Network.Realization.Construction
import all Camus.Network.Realization.CycleFootprint
import all Camus.Network.Realization.CycleWires
import all Camus.Network.Realization.Cycles
import all Camus.Network.Realization.DAG
import all Camus.Network.Realization.Degrees
import all Camus.Network.Realization.Refinement
import all Camus.Network.Realization.Subdivision
import all Camus.Network.Realization.Support
import all Camus.Network.Realization.Wires
import all Camus.Network.Reticulations
import all Camus.Network.Subdivision.Colors
import all Camus.Network.Subdivision.Counterexample
import all Camus.Network.Subdivision.Cuts
import all Camus.Network.Subdivision.Incoming
import all Camus.Network.Subdivision.Invariance
import all Camus.Network.Subdivision.Switching
import all Camus.Network.Subdivision.Wires
import all Camus.Pipelines.Algorithm1
import all Camus.Pipelines.Counterexample
import all Camus.Pipelines.Filtering
import all Camus.Pipelines.Recovery
import all Camus.Pipelines.Statistical
import all Camus.Pipelines.Uniqueness
import all Camus.Preliminaries.Lemma1.Cuts
import all Camus.Preliminaries.Lemma1.Switches
import all Camus.Preliminaries.Lemma1.Tree
import all Camus.Preliminaries.Lemma1.Unique
import all Camus.Preliminaries.Lemmas
import all Camus.Restriction.Construction
import all Camus.Restriction.Correctness
import all Camus.Restriction.Counterexample
import all Camus.Restriction.Defs
import all Camus.Restriction.Forest
import all Camus.Restriction.Main
import all Camus.Restriction.Monotonicity
import all Camus.Restriction.Optimality
import all Camus.Restriction.Saturation
import all Camus.Restriction.Witness
import all Camus.Score
import all Camus.Tree.Forest
import all Camus.Tree.Geometry
import all Solution

/-!
# Axiom and dependency audit

Run with `lake env lean scripts/Audit.lean` after `lake build`.

For every numbered result of the paper, this prints the axioms it depends on and the results from
prior work (`Camus/External/`) that it uses, whether proved there or, in a conditional
formalization, assumed as hypotheses of its statement. It then checks every declaration
of the library and the theorems that Palomar's comparator checks. The run fails if any of them
depends on an axiom other than Lean's standard `propext`, `Classical.choice` and `Quot.sound` (a
`sorry` shows up as the axiom `sorryAx`). Its table of results is the source of the report's
dependency table.

It also writes the *route* of every numbered result to `.lake/route_deps.tsv`: the other
numbered results that its proof uses, found by following the proof through the library's helper
lemmas and stopping at numbered results, together with the TeX label that the result's docstring
names in backticks. `route_check.py` (in the skill's `scripts/`) compares these routes with the
results that the paper's proofs cite.

The library's modules are imported with `import all`, which makes the proofs of their theorems
available: the module system does not export them otherwise. The traversal tests membership in a
precomputed set of the library's constants; looking up each constant's module instead
(`Environment.getModuleIdxFor?`) makes the interpreted script take minutes.

To adapt: generate the `import all` lines, fill in the three lists, and set the library's root
name in `isLibraryModule`. Keep one `import all` line per module of the library, each on its own
line: a module that is missing is still imported through the others, but without its proofs, and
the audit then misses the axioms and the routes inside them. The CI template checks the list.
-/

open Lean Elab Command

namespace Audit

/-- The results from prior work in `Camus/External/`, with a short label: the theorems proved
there. The traversal stops at them. -/
meta def externalResults : List (String × Name) :=
  [("Observation 2 (Warnow, Tabatabaee, Evans 2025)", ``Camus.External.observation2)]

/-- The numbered results of the paper, and its unnumbered claims, in the order of the paper. -/
meta def paperResults : List (String × Name) :=
  [("Lemma 1", ``Camus.lemma1),
   ("Lemma 1, second sentence", ``Camus.lemma1_union),
   ("Lemma 1, second sentence, edge families", ``Camus.DynamicProgramming.novel_disjoint_union),
   ("Lemma 2", ``Camus.lemma2),
   ("Lemma 2, edge families", ``Camus.EdgeAbove.target_unique),
   ("Eq (1)", ``Camus.equation1),
   ("Eq (2)", ``Camus.DynamicProgramming.Array),
   ("Eq (3)", ``Camus.DynamicProgramming.s),
   ("Eq (4)", ``Camus.DynamicProgramming.equation4),
   ("Eq (5)", ``Camus.DynamicProgramming.equation5),
   ("Theorem 1", ``Camus.theorem1),
   ("Sec 2.3, operations", ``Camus.Complexity.scalarOperations_bound),
   ("Sec 2.3, memory", ``Camus.Complexity.scalarSpace_bound),
   ("Sec 2.4, operations", ``Camus.Complexity.budgetOperations_bound),
   ("Sec 2.4, n - 1 reticulations", ``Camus.RootedNetwork.anchored_reticulation_bound),
   ("Sec 2.4, the restricted DP", ``Camus.BudgetDP.reticulation_restriction),
   ("Sec 2.4, monotonicity fails (E5)", ``Camus.not_exactCountMonotone),
   ("Sec 2.4, at most k", ``Camus.atMostScore_mono),
   ("Sec 3.2, uniqueness fails (E6)", ``Camus.not_uniqueOptimum),
   ("Sec 3.2, CAMUS may add an edge (E6)", ``Camus.camus_may_add_edge),
   ("Sec 3.2, corrected", ``Camus.recovery),
   ("Sec 3.2, corrected, trees are identifiable", ``Camus.tree_identifiable),
   ("Sec 3.2, corrected, in probability", ``Camus.correctedStatisticalConsistency),
   ("Sec 3.4, Algorithm 1", ``Camus.Algorithm1.filterQuartets_mono),
   ("Sec 3.4, threshold as a ratio", ``Camus.retainSecond_iff_ratio)]

/-- The theorems that Palomar's comparator checks (`theorem_names` of `comparator.json`). -/
meta def solutionResults : List Name :=
  [``Camus.Challenge.theorem1, ``Camus.Challenge.exists_array_trace,
   ``Camus.Challenge.tree_displays_iff, ``Camus.Challenge.edgeWeight_eq,
   ``Camus.Challenge.reticulation_restriction, ``Camus.Challenge.exists_budgetArray,
   ``Camus.Challenge.not_exactCountMonotone, ``Camus.Challenge.not_uniqueOptimum,
   ``Camus.Challenge.recovery, ``Camus.Challenge.tree_identifiable]

/-- Lean's standard axioms. -/
meta def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Whether `m` is a module of the library. -/
meta def isLibraryModule (m : Name) : Bool := (`Camus).isPrefixOf m

/-- The constants declared in the library. -/
meta def libraryConstants (env : Environment) : NameSet := Id.run do
  let mut s : NameSet := {}
  for m in env.header.moduleNames, d in env.header.moduleData do
    if isLibraryModule m then
      for c in d.constNames do
        s := s.insert c
  return s

/-- The constants used by the type and the value of `c`. -/
meta def usedConstants (env : Environment) (c : Name) : Array Name :=
  match env.find? c with
  | some (.thmInfo t) => t.type.getUsedConstants ++ t.value.getUsedConstants
  | some (.defnInfo d) => d.type.getUsedConstants ++ d.value.getUsedConstants
  | some (.opaqueInfo o) => o.type.getUsedConstants ++ o.value.getUsedConstants
  | some (.inductInfo i) => i.type.getUsedConstants ++ i.ctors.toArray
  | some ci => ci.type.getUsedConstants
  | none => #[]

/-- The external results reached from `root` through constants of the library, without looking
inside the proofs of the external results themselves. `deps` caches the constants of the library
that each constant uses, across calls. -/
meta def externalUses (env : Environment) (library : NameSet) (deps : NameMap (Array Name))
    (root : Name) :
    List Name × NameMap (Array Name) := Id.run do
  let externals := externalResults.map (·.2)
  let mut deps := deps
  let mut visited : NameSet := {}
  let mut stack : List Name := [root]
  let mut found : NameSet := {}
  while true do
    match stack with
    | [] => break
    | c :: rest =>
      stack := rest
      if visited.contains c then continue
      visited := visited.insert c
      if c != root && externals.contains c then
        found := found.insert c
        continue
      let ds := match deps.find? c with
        | some ds => ds
        | none => (usedConstants env c).filter library.contains
      deps := deps.insert c ds
      for d in ds do
        if !visited.contains d then stack := d :: stack
  return (externalResults.filterMap fun (_, n) => if found.contains n then some n else none, deps)

/-- Where `#audit` writes the routes, relative to the project root (`.lake/` is not committed). -/
meta def routeFile : System.FilePath := ".lake/route_deps.tsv"

/-- The numbered results that the proof of `root` uses: those reached from it through constants
of the library, without looking inside the proofs of numbered results themselves. -/
meta def resultUses (env : Environment) (library results : NameSet) (root : Name) :
    Array Name := Id.run do
  let mut visited : NameSet := {}
  let mut stack : List Name := (usedConstants env root).toList
  let mut found : Array Name := #[]
  while true do
    match stack with
    | [] => break
    | c :: rest =>
      stack := rest
      if visited.contains c || c == root then continue
      visited := visited.insert c
      if results.contains c then
        found := found.push c
        continue
      if !library.contains c then continue
      for d in usedConstants env c do
        if !visited.contains d then stack := d :: stack
  return found

/-- The code spans of the docstring of `c` that contain no space or comma: the candidates for its
TeX label. -/
meta def docLabels (env : Environment) (c : Name) : IO (Array String) := do
  let some doc ← findDocString? env c | return #[]
  let mut out : Array String := #[]
  let mut inside := false
  for part in doc.splitOn "`" do
    if inside && !part.isEmpty && !part.any (fun ch => ch.isWhitespace || ch == ',') then
      out := out.push part
    inside := !inside
  return out

elab "#audit" : command => do
  let env ← getEnv
  let mut bad : Array Name := #[]
  let library := libraryConstants env
  let mut deps : NameMap (Array Name) := {}
  let mut rows : Array String := #["| Result | Lean | Results from prior work used | Axioms |",
    "| --- | --- | --- | --- |"]
  for (label, n) in paperResults do
    let axs ← liftCoreM <| collectAxioms n
    if axs.any (!standardAxioms.contains ·) then bad := bad.push n
    let (uses, deps') := externalUses env library deps n
    deps := deps'
    let usesStr := if uses.isEmpty then "–" else ", ".intercalate (uses.map fun u => s!"`{u}`")
    let axStr := ", ".intercalate (axs.toList.map toString)
    rows := rows.push s!"| {label} | `{n}` | {usesStr} | {axStr} |"
  for n in solutionResults ++ externalResults.map (·.2) do
    let axs ← liftCoreM <| collectAxioms n
    if axs.any (!standardAxioms.contains ·) then bad := bad.push n
  -- Every declaration of the library, including private and auxiliary ones.
  for c in library do
    let axs ← liftCoreM <| collectAxioms c
    if axs.any (!standardAxioms.contains ·) then bad := bad.push c
  -- The routes: for each numbered result, its docstring's labels and the results it uses.
  let results : NameSet := paperResults.foldl (fun s p => s.insert p.2) {}
  let mut routes : Array String := #[]
  for (label, n) in paperResults do
    let labels ← docLabels env n
    let uses := resultUses env library results n
    routes := routes.push (s!"{label}\t{n}\t{",".intercalate labels.toList}\t" ++
      ",".intercalate (uses.map toString).toList)
  IO.FS.createDirAll ".lake"
  IO.FS.writeFile routeFile ("\n".intercalate routes.toList ++ "\n")
  logInfo ("\n".intercalate rows.toList ++
    s!"\n\nChecked {library.size} declarations of the library: " ++
    (if bad.isEmpty then "all use only the standard axioms." else "see the error."))
  unless bad.isEmpty do
    throwError m!"non-standard axioms used by: {bad}"

end Audit

#audit
