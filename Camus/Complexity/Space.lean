module

public import Camus.Complexity.Timed

/-!
# Memory: a space component for the cost monad

Section 2.3 of the paper bounds the memory of CAMUS: "We can represent Q in O(n⁴) space, since we
consider integers to require O(1) memory. All other data structures needed for the algorithm, such
as the precomputed LCAs, etc., can be stored in O(n²); hence the total memory usage is O(n⁴)." The
cost monad `Complexity.Timed` of `Camus/Complexity/Timed.lean` counts time only. This file adds
memory: a value of `Spaced α` is a program `run : Timed α`, with its result and its running time,
together with the memory it uses, in cells. `Camus/Complexity/PeakMemory.lean` and
`Camus/Complexity/PeakMemoryBudget.lean` write the programs of Sections 2.2 to 2.4 with their
memory and bound it.

## The memory model

A cell holds a constant number of integers and vertex names: one entry of a table, one element of
a list (a vertex, or a pair of vertices, with its link), or the frame of a call of a recursive
function. The integers, Booleans and vertex names held in the variables of a program are not
charged: outside recursive calls a program has a constant number of variables, and the variables
of a recursive call are in its frame. Memory is counted in cells above the memory in use when the
program starts, so the input `T` and `Q` are not part of it. A program reports two numbers:

* `kept`: the cells it allocated and still holds at its end (its result, and what it built before
  it);
* `peak`: the largest number of cells it holds at a step of its run.

In a sequential composition, the cells kept by the first program are held while the second one
runs: `peak (x >>= f) = max (peak x) (kept x + peak (f a))` and
`kept (x >>= f) = kept x + kept (f a)`, where `a` is the result of `x`. A loop composes its
iterations in the same way (`Complexity.Spaced.forList`). The primitives declare what a program
stores, and each declaration is to be checked against the program it wraps:

* `Spaced.op p`: `p` stores nothing. It reads tables; computes integers, Booleans and vertex names;
  iterates over ranges (`List.range n`, `pairList l`), which are counters and are not stored; and
  writes entries of existing tables in place.
* `Spaced.build sz p`: `p` builds its result `a`, a structure of `sz a` cells, one cell at a time,
  and stores nothing else.
* `Spaced.withAlloc c x`: `x` runs after `c` cells are allocated (a table, as an array over its
  keys, or some rows of one), and keeps them.
* `Spaced.scope sz x`: at the end of `x`, the cells that `x` allocated are released, except the
  `sz a` cells of its result `a`.
* `Spaced.frame x`: `x` is a call of a recursive function that is not tail-recursive; its frame,
  one cell, is held during the call. A tail-recursive function is a loop and has no frames.

Tables are written in place. Every table of the programs is threaded through them and no older
version of a table is read after it was written, except in the knapsack of Section 2.4, which reads
the previous row while it writes the next one and is charged for two rows. So, up to the constant
number of variables, the model charges at least what an implementation stores that keeps the tables
as arrays of the declared sizes and the lists as linked cells, and releases every structure at the
end of the scope that built it, or earlier.

## Main results

* `Complexity.Spaced`: programs with their memory, `kept` and `peak`.
* `Complexity.Spaced.op`, `Complexity.Spaced.build`, `Complexity.Spaced.withAlloc`,
  `Complexity.Spaced.scope`, `Complexity.Spaced.frame`: what a program stores.
* `Complexity.Spaced.forList`, `Complexity.Spaced.maxList`: loops, whose `run` is the loop of
  `Complexity.Timed` (`Complexity.Spaced.run_forList`, `Complexity.Spaced.run_maxList`).
* `Complexity.Spaced.loopKept_le`, `Complexity.Spaced.loopPeak_le_kept_add`,
  `Complexity.Spaced.loopPeak_le_sum`: the memory of a loop.
-/

@[expose] public section

namespace Camus.Complexity

/-- A program with result type `α`, with its memory: the program `run`, with its result and its
running time, and two numbers of cells, counted above the memory in use when it starts: `kept`,
the cells it allocated and still holds at its end, and `peak`, the largest number of cells it
holds at a step of its run. -/
structure Spaced (α : Type) where
  run : Timed α
  kept : ℕ
  peak : ℕ

namespace Spaced

variable {α β σ : Type}

/-- `pure a` stores nothing; `x >>= f` runs `x`, then `f` on its result, holding the cells kept by
`x` while `f` runs. -/
instance : Monad Spaced where
  pure a := ⟨pure a, 0, 0⟩
  bind x f := ⟨x.run >>= fun a => (f a).run, x.kept + (f x.run.val).kept,
    max x.peak (x.kept + (f x.run.val).peak)⟩

@[simp] theorem run_pure (a : α) : (pure a : Spaced α).run = pure a := rfl
@[simp] theorem kept_pure (a : α) : (pure a : Spaced α).kept = 0 := rfl
@[simp] theorem peak_pure (a : α) : (pure a : Spaced α).peak = 0 := rfl

@[simp] theorem run_bind (x : Spaced α) (f : α → Spaced β) :
    (x >>= f).run = x.run >>= fun a => (f a).run := rfl

@[simp] theorem kept_bind (x : Spaced α) (f : α → Spaced β) :
    (x >>= f).kept = x.kept + (f x.run.val).kept := rfl

@[simp] theorem peak_bind (x : Spaced α) (f : α → Spaced β) :
    (x >>= f).peak = max x.peak (x.kept + (f x.run.val).peak) := rfl

@[simp] theorem run_ite (c : Prop) [Decidable c] (x y : Spaced α) :
    (if c then x else y).run = if c then x.run else y.run := by
  split_ifs <;> rfl

@[simp] theorem kept_ite (c : Prop) [Decidable c] (x y : Spaced α) :
    (if c then x else y).kept = if c then x.kept else y.kept := by
  split_ifs <;> rfl

@[simp] theorem peak_ite (c : Prop) [Decidable c] (x y : Spaced α) :
    (if c then x else y).peak = if c then x.peak else y.peak := by
  split_ifs <;> rfl

/-- The program `p`, which stores nothing: it reads tables, computes integers, Booleans and vertex
names, iterates over ranges, and writes entries of existing tables in place. -/
def op (p : Timed α) : Spaced α := ⟨p, 0, 0⟩

/-- The program `p`, which builds its result `a`, a structure of `sz a` cells, one cell at a time,
and stores nothing else. -/
def build (sz : α → ℕ) (p : Timed α) : Spaced α := ⟨p, sz p.val, sz p.val⟩

/-- `x`, run after `c` cells are allocated, which it keeps. -/
def withAlloc (c : ℕ) (x : Spaced α) : Spaced α := ⟨x.run, c + x.kept, c + x.peak⟩

/-- `x` in a scope: at its end, the cells that `x` allocated are released, except the `sz a` cells
of its result `a`. -/
def scope (sz : α → ℕ) (x : Spaced α) : Spaced α :=
  ⟨x.run, sz x.run.val, max x.peak (sz x.run.val)⟩

/-- A call of a recursive function that is not tail-recursive: its frame, one cell, is held during
the call. -/
def frame (x : Spaced α) : Spaced α := ⟨x.run, x.kept, x.peak + 1⟩

@[simp] theorem run_op (p : Timed α) : (op p).run = p := rfl
@[simp] theorem kept_op (p : Timed α) : (op p).kept = 0 := rfl
@[simp] theorem peak_op (p : Timed α) : (op p).peak = 0 := rfl
@[simp] theorem run_build (sz : α → ℕ) (p : Timed α) : (build sz p).run = p := rfl
@[simp] theorem kept_build (sz : α → ℕ) (p : Timed α) : (build sz p).kept = sz p.val := rfl
@[simp] theorem peak_build (sz : α → ℕ) (p : Timed α) : (build sz p).peak = sz p.val := rfl
@[simp] theorem run_withAlloc (c : ℕ) (x : Spaced α) : (withAlloc c x).run = x.run := rfl
@[simp] theorem kept_withAlloc (c : ℕ) (x : Spaced α) : (withAlloc c x).kept = c + x.kept := rfl
@[simp] theorem peak_withAlloc (c : ℕ) (x : Spaced α) : (withAlloc c x).peak = c + x.peak := rfl
@[simp] theorem run_scope (sz : α → ℕ) (x : Spaced α) : (scope sz x).run = x.run := rfl
@[simp] theorem kept_scope (sz : α → ℕ) (x : Spaced α) :
    (scope sz x).kept = sz x.run.val := rfl
@[simp] theorem peak_scope (sz : α → ℕ) (x : Spaced α) :
    (scope sz x).peak = max x.peak (sz x.run.val) := rfl
@[simp] theorem run_frame (x : Spaced α) : (frame x).run = x.run := rfl
@[simp] theorem kept_frame (x : Spaced α) : (frame x).kept = x.kept := rfl
@[simp] theorem peak_frame (x : Spaced α) : (frame x).peak = x.peak + 1 := rfl

/-! ### Loops -/

/-- The cells kept by the iterations of the loop `for a in l` from the state `s`. -/
def loopKept (f : σ → α → Spaced σ) : List α → σ → ℕ
  | [], _ => 0
  | a :: l, s => (f s a).kept + loopKept f l (f s a).run.val

/-- The peak of the loop `for a in l` from the state `s`: the largest, over the iterations, of the
cells kept by the earlier iterations and the peak of the iteration. -/
def loopPeak (f : σ → α → Spaced σ) : List α → σ → ℕ
  | [], _ => 0
  | a :: l, s => max (f s a).peak ((f s a).kept + loopPeak f l (f s a).run.val)

/-- The loop `for a in l` over a state (`Timed.forList`), with its memory: the iterations are
composed in sequence, each holding the cells kept by the earlier ones. -/
def forList (f : σ → α → Spaced σ) (l : List α) (s : σ) : Spaced σ :=
  ⟨Timed.forList (fun s a => (f s a).run) l s, loopKept f l s, loopPeak f l s⟩

@[simp] theorem run_forList (f : σ → α → Spaced σ) (l : List α) (s : σ) :
    (forList f l s).run = Timed.forList (fun s a => (f s a).run) l s := rfl

@[simp] theorem kept_forList (f : σ → α → Spaced σ) (l : List α) (s : σ) :
    (forList f l s).kept = loopKept f l s := rfl

@[simp] theorem peak_forList (f : σ → α → Spaced σ) (l : List α) (s : σ) :
    (forList f l s).peak = loopPeak f l s := rfl

/-- If each iteration keeps at most `c` cells, whatever the state, the loop keeps at most
`|l| c`. -/
theorem loopKept_le (f : σ → α → Spaced σ) (c : ℕ) :
    ∀ (l : List α) (s : σ), (∀ s, ∀ a ∈ l, (f s a).kept ≤ c) → loopKept f l s ≤ l.length * c := by
  intro l
  induction l with
  | nil => intro s _; simp [loopKept]
  | cons a l ih =>
    intro s h
    have ha := h s a (by simp)
    have hl := ih (f s a).run.val (fun s b hb => h s b (by simp [hb]))
    simp only [loopKept, List.length_cons, Nat.succ_mul]
    omega

/-- If each iteration holds at most `p` cells beyond those it keeps, whatever the state, the loop
holds at most `p` cells beyond those it keeps. -/
theorem loopPeak_le_kept_add (f : σ → α → Spaced σ) (p : ℕ) :
    ∀ (l : List α) (s : σ), (∀ s, ∀ a ∈ l, (f s a).peak ≤ (f s a).kept + p) →
      loopPeak f l s ≤ loopKept f l s + p := by
  intro l
  induction l with
  | nil => intro s _; simp [loopPeak, loopKept]
  | cons a l ih =>
    intro s h
    have ha := h s a (by simp)
    have hl := ih (f s a).run.val (fun s b hb => h s b (by simp [hb]))
    simp only [loopPeak, loopKept]
    omega

/-- A loop whose iterations keep nothing holds at most the largest peak of an iteration. -/
theorem loopPeak_le (f : σ → α → Spaced σ) (p : ℕ) (l : List α) (s : σ)
    (hk : ∀ s, ∀ a ∈ l, (f s a).kept = 0) (hp : ∀ s, ∀ a ∈ l, (f s a).peak ≤ p) :
    loopPeak f l s ≤ p := by
  have h1 := loopPeak_le_kept_add f p l s (fun s a ha => by have := hp s a ha; omega)
  have h2 := loopKept_le f 0 l s (fun s a ha => by rw [hk s a ha])
  simp only [Nat.mul_zero, Nat.le_zero] at h2
  omega

/-- If each iteration on `a` keeps at most `c a` cells, whatever the state, the loop keeps at most
`Σ_{a ∈ l} c a`. -/
theorem loopKept_le_sum (f : σ → α → Spaced σ) (c : α → ℕ) :
    ∀ (l : List α) (s : σ), (∀ s, ∀ a ∈ l, (f s a).kept ≤ c a) →
      loopKept f l s ≤ (l.map c).sum := by
  intro l
  induction l with
  | nil => intro s _; simp [loopKept]
  | cons a l ih =>
    intro s h
    have ha := h s a (by simp)
    have hl := ih (f s a).run.val (fun s b hb => h s b (by simp [hb]))
    simp only [loopKept, List.map_cons, List.sum_cons]
    omega

/-- If each iteration on `a` keeps at most `c a` cells and holds at most `c a + p`, whatever the
state, the loop holds at most `Σ_{a ∈ l} c a + p`. -/
theorem loopPeak_le_sum (f : σ → α → Spaced σ) (c : α → ℕ) (p : ℕ) :
    ∀ (l : List α) (s : σ), (∀ s, ∀ a ∈ l, (f s a).kept ≤ c a ∧ (f s a).peak ≤ c a + p) →
      loopPeak f l s ≤ (l.map c).sum + p := by
  intro l
  induction l with
  | nil => intro s _; simp [loopPeak]
  | cons a l ih =>
    intro s h
    obtain ⟨hk, hp⟩ := h s a (by simp)
    have hl := ih (f s a).run.val (fun s b hb => h s b (by simp [hb]))
    simp only [loopPeak, List.map_cons, List.sum_cons]
    omega

/-- `maxList f l` (`Timed.maxList`), with its memory. -/
def maxList (f : α → Spaced ℕ) (l : List α) : Spaced ℕ :=
  forList (fun acc a => do let x ← f a; op (Timed.step (max acc x))) l 0

/-- The program of `maxList f l` is the loop `Timed.maxList`. -/
theorem run_maxList (f : α → Spaced ℕ) (l : List α) :
    (maxList f l).run = Timed.maxList (fun a => (f a).run) l := rfl

end Spaced

end Camus.Complexity
