module

public import Camus.PackingTheorem

@[expose] public section

namespace Camus.BudgetDP

open DynamicProgramming

/-- An exact-budget row is empty when infeasible and contains only its maximum
when feasible. This is the finite-set encoding of an optional score. -/
def best (S : Finset ℕ) : Finset ℕ := S.filter (fun z => z = S.sup id)

 theorem mem_best {S : Finset ℕ} {z : ℕ} : z ∈ best S ↔ z ∈ S ∧ ∀ x ∈ S, x ≤ z := by
  constructor
  · intro hz
    obtain ⟨hz, heq⟩ := Finset.mem_filter.mp hz
    exact ⟨hz, fun x hx => heq ▸ Finset.le_sup (f := id) hx⟩
  · rintro ⟨hz,hmax⟩
    apply Finset.mem_filter.mpr
    exact ⟨hz, Nat.le_antisymm (Finset.le_sup (f := id) hz) (Finset.sup_le hmax)⟩

 theorem exists_best_ge {S : Finset ℕ} {z : ℕ} (hz : z ∈ S) :
    ∃ m ∈ best S, z ≤ m := by
  have hn : S.Nonempty := ⟨z,hz⟩
  refine ⟨S.sup id, ?_, Finset.le_sup (f := id) hz⟩
  apply (mem_best).mpr
  exact ⟨by simpa using (Finset.sup_mem_of_nonempty (f := id) hn), fun x hx => Finset.le_sup (f := id) hx⟩

 theorem best_card_le_one (S : Finset ℕ) : (best S).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  exact (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm

/-- Max-plus convolution, distributing the exact budget between two rows. -/
def convolution (A B : ℕ → Finset ℕ) (k : ℕ) : Finset ℕ :=
  (Finset.range (k+1)).biUnion fun i =>
    (A i ×ˢ B (k-i)).image (fun xy => xy.1 + xy.2)

 theorem mem_convolution {A B : ℕ → Finset ℕ} {k z : ℕ} :
    z ∈ convolution A B k ↔
      ∃ i j a b, i+j=k ∧ a ∈ A i ∧ b ∈ B j ∧ a+b=z := by
  classical
  constructor
  · intro hz
    obtain ⟨i,hi,hz⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨⟨a,b⟩,hab,heq⟩ := Finset.mem_image.mp hz
    have hi' : i ≤ k := by have := Finset.mem_range.mp hi; omega
    exact ⟨i,k-i,a,b,by omega,(Finset.mem_product.mp hab).1,(Finset.mem_product.mp hab).2,heq⟩
  · rintro ⟨i,j,a,b,hij,ha,hb,rfl⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨i,Finset.mem_range.mpr (by omega),Finset.mem_image.mpr ?_⟩
    exact ⟨(a,b),Finset.mem_product.mpr ⟨ha,by simpa [show k-i=j by omega] using hb⟩,rfl⟩

/-- Specification helper containing all budget-allocation scores. This is not
the algorithm: `forest` prunes intermediate maxima while preserving attainment
and domination, as proved in `BudgetDPForest`. No network is enumerated. -/
def allocations (M : Address → ℕ → Finset ℕ) : List Address → ℕ → Finset ℕ
  | [], k => if k=0 then {0} else ∅
  | r::rs, k => convolution (M r) (allocations M rs) k

/-- Hanging-forest knapsack: retain only the maximum after each
convolution, so every intermediate exact-budget row is empty or singleton. -/
def forest (M : Address → ℕ → Finset ℕ) : List Address → ℕ → Finset ℕ
  | [], k => if k=0 then {0} else ∅
  | r::rs, k => best (convolution (M r) (forest M rs) k)

/-- The source §2.4 recurrence: either no edge at v, or one edge at v using
one budget unit followed by allocation across the Eq. 4/5 hanging forest. -/
noncomputable def cases (t : PhyloTree) (w : Pair → ℕ) (M : Address → ℕ → Finset ℕ)
    (v : Address) (k : ℕ) : Finset ℕ :=
  match t.nodeAt v with
  | some (.leaf _) => if k=0 then {0} else ∅
  | some (.fork _ _) => convolution (M (v++[false])) (M (v++[true])) k ∪
      if k=0 then ∅ else (pairsAt t v).biUnion fun e =>
        (forest M (hanging t e).toList (k-1)).image (fun z => w e + z)
  | none => ∅

/-- Only the exact-budget recurrence is assumed of an array. Its existence,
attainment, feasibility and optimality are separate theorem obligations. -/
def Array (t : PhyloTree) (w : Pair → ℕ) (M : Address → ℕ → Finset ℕ) : Prop :=
  ∀ v ∈ t.nodes, ∀ k, M v k = best (cases t w M v k)

end Camus.BudgetDP
