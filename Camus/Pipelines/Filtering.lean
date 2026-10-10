module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp

/-!
# Section 3.4: the threshold test of Algorithm 1

Algorithm 1 (quartet filtering) keeps, for each set of four taxa whose three topologies have
frequencies `f₁ ≥ f₂ ≥ f₃`, the most frequent topology `q₁`, and keeps the second `q₂` iff
`f₂ − f₃ > t · (f₂ + f₃)` (`retainSecond`). This file proves the paper's reformulation of the test
and its behaviour in `t`. The algorithm itself is in `Camus/Pipelines/Algorithm1.lean`.

## Main results

* `retainSecond_iff_ratio`: for `f₂ + f₃ > 0`, the test holds iff `t < (f₂ − f₃)/(f₂ + f₃)`.
* `retainSecond_mono`: a smaller threshold keeps `q₂` more often.
* `not_retainSecond_one`, `not_retainSecond_equal`, `retainSecond_zero`: the threshold `t = 1`
  never keeps `q₂`; for `t ≥ 0`, equal frequencies `f₂ = f₃` never keep `q₂`; the threshold `t = 0`
  keeps `q₂` iff `f₂ > f₃`.
-/

@[expose] public section

namespace Camus

/-- The test of Algorithm 1 (Section 3.4): the second most frequent topology `q₂` is kept iff
`f₂ − f₃ > t · (f₂ + f₃)`. The paper takes `t ∈ [0, 1]`. -/
def retainSecond (t f₂ f₃ : ℝ) : Prop := f₂ - f₃ > t * (f₂ + f₃)

/-- Section 3.4: "for t small enough (specifically, t < (f₂−f₃)/(f₂+f₃)), then we will include q₂".
For `f₂ + f₃ > 0`, the test holds iff `t < (f₂ − f₃)/(f₂ + f₃)`. -/
theorem retainSecond_iff_ratio (t f₂ f₃ : ℝ) (h : 0 < f₂ + f₃) :
    retainSecond t f₂ f₃ ↔ t < (f₂ - f₃) / (f₂ + f₃) := by
  exact (lt_div_iff₀ h).symm

/-- A smaller threshold keeps `q₂` more often: if `f₂ + f₃ ≥ 0`, `s ≤ t` and the test holds at `t`,
it holds at `s`. -/
theorem retainSecond_mono {s t f₂ f₃ : ℝ} (hfreq : 0 ≤ f₂ + f₃)
    (hst : s ≤ t) (h : retainSecond t f₂ f₃) : retainSecond s f₂ f₃ := by
  unfold retainSecond at *
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hst hfreq) h

/-- The threshold `t = 1` never keeps `q₂` when `f₃ ≥ 0`. -/
theorem not_retainSecond_one (f₂ f₃ : ℝ) (h₃ : 0 ≤ f₃) :
    ¬retainSecond 1 f₂ f₃ := by
  unfold retainSecond
  simp only [one_mul]
  linarith

/-- Equal frequencies `f₂ = f₃ ≥ 0`, which Section 3.4 expects under the multispecies coalescent,
never keep `q₂` when `t ≥ 0`. -/
theorem not_retainSecond_equal (t f : ℝ) (ht : 0 ≤ t) (hf : 0 ≤ f) :
    ¬retainSecond t f f := by
  unfold retainSecond
  have h := mul_nonneg ht (add_nonneg hf hf)
  linarith

/-- The threshold `t = 0` keeps `q₂` iff `f₃ < f₂`. -/
theorem retainSecond_zero (f₂ f₃ : ℝ) :
    retainSecond 0 f₂ f₃ ↔ f₃ < f₂ := by
  simp only [retainSecond, zero_mul]
  exact sub_pos

end Camus
