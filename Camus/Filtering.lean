module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp

@[expose] public section

namespace Camus

/-- Algorithm 1 (`btag245-BOX1`): retain the runner-up precisely when this strict
inequality holds. Zero denominator is handled by the original inequality. -/
def retainSecond (t f₂ f₃ : ℝ) : Prop := f₂ - f₃ > t * (f₂ + f₃)

/-- §3.4's ratio reformulation, with its required positive denominator explicit.
The case f₂=f₃=0 uses the original inequality and never divides by zero. -/
theorem retainSecond_iff_ratio (t f₂ f₃ : ℝ) (h : 0 < f₂ + f₃) :
    retainSecond t f₂ f₃ ↔ t < (f₂ - f₃) / (f₂ + f₃) := by
  exact (lt_div_iff₀ h).symm

theorem retainSecond_mono {s t f₂ f₃ : ℝ} (hfreq : 0 ≤ f₂ + f₃)
    (hst : s ≤ t) (h : retainSecond t f₂ f₃) : retainSecond s f₂ f₃ := by
  unfold retainSecond at *
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hst hfreq) h

/-- The filtering threshold 1 never retains the runner-up for nonnegative f₃. -/
theorem not_retainSecond_one (f₂ f₃ : ℝ) (h₃ : 0 ≤ f₃) :
    ¬retainSecond 1 f₂ f₃ := by
  unfold retainSecond
  simp only [one_mul]
  linarith

/-- Exactly equal minor frequencies never trigger the filter at nonnegative t. -/
theorem not_retainSecond_equal (t f : ℝ) (ht : 0 ≤ t) (hf : 0 ≤ f) :
    ¬retainSecond t f f := by
  unfold retainSecond
  have h := mul_nonneg ht (add_nonneg hf hf)
  linarith

/-- Threshold zero retains the runner-up exactly at a strict frequency gap. -/
theorem retainSecond_zero (f₂ f₃ : ℝ) :
    retainSecond 0 f₂ f₃ ↔ f₃ < f₂ := by
  simp only [retainSecond, zero_mul]
  exact sub_pos

end Camus
