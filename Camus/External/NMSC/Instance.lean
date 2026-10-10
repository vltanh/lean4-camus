module

public import Camus.External.NMSC.Model

/-!
# The formulas of Fig. S1 satisfy the property

The property `Brooqs.NMSCQuartetCF Ω ord CF` fixes the CFs of distinct components to the formulas
of Fig. S1 (`Brooqs.cycleCF`); the formulas themselves have it. The algebraic version of Remark 1's
example (`Brooqs.remark1_sharp_cycleCF`) uses this instance; the component CFs of a cycle of a
network have the property by `Brooqs.nmsc_quartetCF`.
-/

@[expose] public section

namespace Brooqs

variable {d : ℕ}

/-- The component CFs given by the formulas of Fig. S1 have the property `NMSCQuartetCF`. -/
theorem nmscQuartetCF_cycleCF (Ω : MetricCycle d) (ord : Equiv.Perm (Fin d)) :
    NMSCQuartetCF Ω ord
      (fun a b c e => cycleCF Ω (ord.symm a) (ord.symm b) (ord.symm c) (ord.symm e)) :=
  fun _ _ _ _ _ _ _ _ _ _ => rfl

end Brooqs
