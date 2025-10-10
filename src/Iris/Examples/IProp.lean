/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
import Iris.BI
import Iris.ProofMode
import Iris.Algebra.IProp
import Iris.Instances.IProp
import Iris.Algebra.Agree

namespace Iris.Examples
open Iris.BI COFE

section Example1

abbrev F0 : OFunctorPre := COFE.constOF (Agree (LeibnizO String))

variable {GF} [E0 : ElemG GF F0]

private theorem autoverse : ⊢
    (|==> ∃ (γ : GName), iOwn (F := F0) γ (toAgree ⟨"Paul Durham"⟩) : IProp GF) := by
  apply iOwn_alloc
  exact fun _ => trivial

example : ⊢ |==> ∃ (γ1 γ2 : GName),
    iOwn (E := E0) γ1 (toAgree ⟨"hi"⟩) ∗
    iOwn (E := E0) γ2 (toAgree ⟨"hello"⟩) := by
  sorry

end Example1


end Iris.Examples
