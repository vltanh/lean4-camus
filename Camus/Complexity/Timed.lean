module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Tactic.Ring

/-!
# A cost monad for Section 2.3

Section 2.3 of the paper bounds the running time of CAMUS in the unit-cost model, where an integer
takes `O(1)` memory and an operation on integers takes `O(1)` time. This file sets up the cost
semantics in which `Camus/Complexity/Program.lean` and `Camus/Complexity/BudgetProgram.lean` write
the algorithm. A program is a value of `Timed α`: a result `val : α` together with the number
`time` of elementary operations performed to obtain it. `pure` costs nothing, `bind` adds the
costs, and `step a` is one elementary operation with result `a`.

## The cost model

One unit of time is charged for each of the following elementary operations:

* a read or a write of one entry of a table (the preprocessing tables of
  `Camus/Complexity/Tables.lean`, the array `M`, the table of weights `s_e`, the buckets of pairs);
* an arithmetic operation or a comparison on natural numbers, and a Boolean connective;
* a comparison of two vertices, and the creation of the name of a vertex;
* one iteration of a loop (`forList`, `mapList`, `sumList`, `maxList`, `sumOver`).

Vertices are named by their addresses (`Address`). A program uses an address only as a name, as an
implementation would use an index or a pointer: it compares two names, uses them as keys of tables,
and creates the names of the two children of a vertex once, during the traversal of `T`. It never
inspects the list structure of an address: parents, children, depths and lowest common ancestors
are read from tables. A table is a function updated one entry at a time (`Function.update`), and
every read and write is charged. Everything a program computes between two charged operations is a
constant amount of work in this model.

## Main results

* `Complexity.Timed`, `Complexity.Timed.step`: programs with their running time.
* `Complexity.Timed.forList`, `Complexity.Timed.mapList`, `Complexity.Timed.sumList`,
  `Complexity.Timed.maxList`: loops over a list, with their results (`val_forList`, ...) and
  running times (`time_forList_le`, ...).
* `Complexity.Timed.sumOver`: the sum over a finite set, the same as the loop over any
  enumeration of the set (`sumList_eq_sumOver`).
* `Complexity.foldl_invariant`: induction along a loop.
-/

@[expose] public section

namespace Camus.Complexity

/-- A program with result type `α`, run: its result `val` and the number `time` of elementary
operations it performed. -/
structure Timed (α : Type) where
  val : α
  time : ℕ

namespace Timed

/-- `pure a` returns `a` at no cost; `x >>= f` runs `x`, then `f` on its result, and adds the
costs. -/
instance : Monad Timed where
  pure a := ⟨a, 0⟩
  bind x f := ⟨(f x.val).val, x.time + (f x.val).time⟩

/-- One elementary operation with result `a`. -/
def step {α : Type} (a : α) : Timed α := ⟨a, 1⟩

/-- `n` elementary operations with result `a`. -/
def steps {α : Type} (n : ℕ) (a : α) : Timed α := ⟨a, n⟩

/-- One elementary operation with no result. -/
def tick : Timed Unit := step ()

variable {α β σ : Type}

@[simp] theorem val_pure (a : α) : (pure a : Timed α).val = a := rfl
@[simp] theorem time_pure (a : α) : (pure a : Timed α).time = 0 := rfl
@[simp] theorem val_bind (x : Timed α) (f : α → Timed β) : (x >>= f).val = (f x.val).val := rfl
@[simp] theorem time_bind (x : Timed α) (f : α → Timed β) :
    (x >>= f).time = x.time + (f x.val).time := rfl
@[simp] theorem val_step (a : α) : (step a).val = a := rfl
@[simp] theorem time_step (a : α) : (step a).time = 1 := rfl
@[simp] theorem val_steps (n : ℕ) (a : α) : (steps n a).val = a := rfl
@[simp] theorem time_steps (n : ℕ) (a : α) : (steps n a).time = n := rfl
@[simp] theorem val_tick : tick.val = () := rfl
@[simp] theorem time_tick : tick.time = 1 := rfl

@[simp] theorem val_ite (c : Prop) [Decidable c] (x y : Timed α) :
    (if c then x else y).val = if c then x.val else y.val := by
  split_ifs <;> rfl

@[simp] theorem time_ite (c : Prop) [Decidable c] (x y : Timed α) :
    (if c then x else y).time = if c then x.time else y.time := by
  split_ifs <;> rfl

/-- The loop `for a in l` over a state: `forList f l s` runs `f s a` for the elements `a` of `l` in
order, passing the state along, with one operation per iteration. -/
def forList (f : σ → α → Timed σ) : List α → σ → Timed σ
  | [], s => pure s
  | a :: l, s => do
      tick
      let s' ← f s a
      forList f l s'

@[simp] theorem forList_nil (f : σ → α → Timed σ) (s : σ) : forList f [] s = pure s := rfl

theorem forList_cons (f : σ → α → Timed σ) (a : α) (l : List α) (s : σ) :
    forList f (a :: l) s = (do tick; let s' ← f s a; forList f l s') := rfl

/-- The result of a loop is the left fold of the results of its iterations. -/
@[simp] theorem val_forList (f : σ → α → Timed σ) (l : List α) (s : σ) :
    (forList f l s).val = l.foldl (fun s a => (f s a).val) s := by
  induction l generalizing s with
  | nil => rfl
  | cons a l ih => simp [forList_cons, ih]

/-- If each iteration on `a` costs at most `c a`, whatever the state, the loop costs at most
`Σ_{a ∈ l} (c a + 1)`. -/
theorem time_forList_le (f : σ → α → Timed σ) (l : List α) (s : σ) (c : α → ℕ)
    (h : ∀ s, ∀ a ∈ l, (f s a).time ≤ c a) :
    (forList f l s).time ≤ (l.map fun a => c a + 1).sum := by
  induction l generalizing s with
  | nil => simp
  | cons a l ih =>
    simp only [forList_cons, time_bind, time_tick, List.map_cons, List.sum_cons]
    have ha := h s a (by simp)
    have hl := ih (f s a).val (fun s b hb => h s b (by simp [hb]))
    omega

/-- If each iteration on `a` costs exactly `c a`, whatever the state, the loop costs
`Σ_{a ∈ l} (c a + 1)`. -/
theorem time_forList_eq (f : σ → α → Timed σ) (l : List α) (s : σ) (c : α → ℕ)
    (h : ∀ s, ∀ a ∈ l, (f s a).time = c a) :
    (forList f l s).time = (l.map fun a => c a + 1).sum := by
  induction l generalizing s with
  | nil => simp
  | cons a l ih =>
    simp only [forList_cons, time_bind, time_tick, List.map_cons, List.sum_cons]
    have ha := h s a (by simp)
    have hl := ih (f s a).val (fun s b hb => h s b (by simp [hb]))
    omega

@[simp] theorem sum_map_const_nat (l : List α) (c : ℕ) : (l.map fun _ => c).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; ring

/-- `mapList f l` applies `f` to the elements of `l` in order and lists the results, with one
operation per element. -/
def mapList (f : α → Timed β) : List α → Timed (List β)
  | [] => pure []
  | a :: l => do
      tick
      let b ← f a
      let bs ← mapList f l
      pure (b :: bs)

@[simp] theorem val_mapList (f : α → Timed β) (l : List α) :
    (mapList f l).val = l.map fun a => (f a).val := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [mapList, ih]

@[simp] theorem time_mapList (f : α → Timed β) (l : List α) :
    (mapList f l).time = (l.map fun a => (f a).time + 1).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [mapList, time_bind, time_tick, time_pure, List.map_cons, List.sum_cons, ih]
    omega

/-- `sumList f l = Σ_{a ∈ l} f a`, one addition per element. -/
def sumList (f : α → Timed ℕ) (l : List α) : Timed ℕ :=
  forList (fun acc a => do let x ← f a; step (acc + x)) l 0

theorem foldl_add_eq (g : α → ℕ) (l : List α) (s : ℕ) :
    l.foldl (fun acc a => acc + g a) s = s + (l.map g).sum := by
  induction l generalizing s with
  | nil => simp
  | cons a l ih => simp only [List.foldl_cons, ih, List.map_cons, List.sum_cons]; omega

@[simp] theorem val_sumList (f : α → Timed ℕ) (l : List α) :
    (sumList f l).val = (l.map fun a => (f a).val).sum := by
  simp [sumList, foldl_add_eq]

@[simp] theorem time_sumList (f : α → Timed ℕ) (l : List α) :
    (sumList f l).time = (l.map fun a => (f a).time + 2).sum := by
  unfold sumList
  rw [time_forList_eq _ l 0 (fun a => (f a).time + 1) (fun s a _ => by simp)]

/-- `maxList f l` is the maximum of `f a` over the elements `a` of `l` (`0` for the empty list),
one comparison per element. -/
def maxList (f : α → Timed ℕ) (l : List α) : Timed ℕ :=
  forList (fun acc a => do let x ← f a; step (max acc x)) l 0

theorem foldl_max_eq [DecidableEq α] (g : α → ℕ) (l : List α) (s : ℕ) :
    l.foldl (fun acc a => max acc (g a)) s = max s (l.toFinset.sup g) := by
  induction l generalizing s with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldl_cons, ih, List.toFinset_cons, Finset.sup_insert]
    simp only [max_assoc]

/-- The result of `maxList` is the supremum over the set of the elements of the list. -/
@[simp] theorem val_maxList [DecidableEq α] (f : α → Timed ℕ) (l : List α) :
    (maxList f l).val = l.toFinset.sup fun a => (f a).val := by
  simp [maxList, foldl_max_eq]

@[simp] theorem time_maxList (f : α → Timed ℕ) (l : List α) :
    (maxList f l).time = (l.map fun a => (f a).time + 2).sum := by
  unfold maxList
  rw [time_forList_eq _ l 0 (fun a => (f a).time + 1) (fun s a _ => by simp)]

/-- The sum `Σ_{a ∈ s} f a` over a finite set, as a loop over the elements of `s` in some order,
with one iteration and one addition per element. Its result and its cost do not depend on the
order (`sumList_eq_sumOver`). -/
def sumOver (s : Finset α) (f : α → Timed ℕ) : Timed ℕ :=
  ⟨∑ a ∈ s, (f a).val, ∑ a ∈ s, ((f a).time + 2)⟩

@[simp] theorem val_sumOver (s : Finset α) (f : α → Timed ℕ) :
    (sumOver s f).val = ∑ a ∈ s, (f a).val := rfl

@[simp] theorem time_sumOver (s : Finset α) (f : α → Timed ℕ) :
    (sumOver s f).time = ∑ a ∈ s, ((f a).time + 2) := rfl

/-- `sumOver` is the loop `sumList` over any enumeration of the set without repetition. -/
theorem sumList_eq_sumOver [DecidableEq α] (f : α → Timed ℕ) {l : List α} (hl : l.Nodup)
    {s : Finset α} (hs : l.toFinset = s) : sumList f l = sumOver s f := by
  subst hs
  have hv := val_sumList f l
  have ht := time_sumList f l
  rw [← List.sum_toFinset _ hl] at hv ht
  cases h : sumList f l
  rw [h] at hv ht
  simp only [sumOver, Timed.mk.injEq]
  exact ⟨hv, ht⟩

/-- If each term costs at most `c`, the sum over `s` costs at most `|s| (c + 2)`. -/
theorem time_sumOver_le (s : Finset α) (f : α → Timed ℕ) (c : ℕ)
    (h : ∀ a ∈ s, (f a).time ≤ c) : (sumOver s f).time ≤ s.card * (c + 2) := by
  rw [time_sumOver]
  calc
    _ ≤ ∑ _a ∈ s, (c + 2) := Finset.sum_le_sum fun a ha => by have := h a ha; omega
    _ = _ := by simp

end Timed

/-- Induction along a loop: if `P` holds before the loop, and each iteration on an element `a` of
`l = A ++ a :: B` takes a state satisfying `P A` to one satisfying `P (A ++ [a])`, then the state
after the loop satisfies `P l`. -/
theorem foldl_invariant {α σ : Type*} (l : List α) (step : σ → α → σ) (P : List α → σ → Prop)
    {s : σ} (h0 : P [] s)
    (hstep : ∀ A a B s, l = A ++ a :: B → P A s → P (A ++ [a]) (step s a)) :
    P l (l.foldl step s) := by
  have key : ∀ (B A : List α) (s : σ), l = A ++ B → P A s → P l (B.foldl step s) := by
    intro B
    induction B with
    | nil => intro A s hl hs; simpa [hl] using hs
    | cons a B ih =>
      intro A s hl hs
      exact ih (A ++ [a]) (step s a) (by simp [hl]) (hstep A a B s hl hs)
  exact key l [] s (by simp) h0

end Camus.Complexity
