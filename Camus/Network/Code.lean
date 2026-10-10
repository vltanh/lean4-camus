module

public import Camus.Defs

public import Camus.Tree.Forest

@[expose] public section

namespace Camus

namespace Address

theorem code_pos (p : Address) : 0 < code p := by
  induction p with
  | nil => simp [code]
  | cons b p ih => cases b <;> simp only [code] <;> omega

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
