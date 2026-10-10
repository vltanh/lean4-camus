module

public import Camus.Defs

public import Camus.Tree.Forest

/-!
# Codes of addresses

The networks `Realization.graph t E` built from `T` use natural numbers as vertex identifiers: a
vertex `p` of `T` is the number `Address.code p`, and the new vertices u', w' get fresh numbers
above all of these. This file proves that the codes are positive and injective, so distinct
vertices of `T` get distinct identifiers.

## Main results

* `Address.code_pos`: codes are positive.
* `Address.code_injective`: distinct addresses have distinct codes.
-/

@[expose] public section

namespace Camus

namespace Address

/-- The code of an address is positive. -/
theorem code_pos (p : Address) : 0 < code p := by
  induction p with
  | nil => simp [code]
  | cons b p ih => cases b <;> simp only [code] <;> omega

/-- Distinct addresses have distinct codes: `Address.code` is injective. -/
theorem code_injective : Function.Injective code := by
  intro p
  induction p with
  | nil =>
    intro q h
    cases q with
    | nil => rfl
    | cons b q =>
      have hpos := code_pos q
      cases b <;> simp only [code] at h <;> omega
  | cons a p ih =>
    intro q h
    cases q with
    | nil =>
      have hpos := code_pos p
      cases a <;> simp only [code] at h <;> omega
    | cons b q =>
      cases a <;> cases b <;> simp only [code] at h
      · exact congrArg (false :: ·) (ih (by omega))
      · omega
      · omega
      · exact congrArg (true :: ·) (ih (by omega))

end Address

namespace Realization

end Realization
end Camus
