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

abbrev F0 : OFunctorPre := constOF (Agree (LeibnizO String))

variable {GF} [E0 : ElemG GF F0]

private theorem autoverse : ⊢
    (|==> ∃ (γ : GName), iOwn (F := F0) γ (toAgree ⟨"Paul Durham"⟩) : IProp GF) := by
  apply iOwn_alloc
  exact fun _ => trivial

example : ⊢ |==> ∃ (γ0 γ1 : GName) (s0 s1 : String),
    iOwn (E := E0) γ0 (toAgree ⟨s0⟩) ∗
    iOwn (E := E0) γ1 (toAgree ⟨s1⟩) := by
  let v0 : F0.ap (IProp GF) := toAgree ⟨"string0"⟩
  let v1 : F0.ap (IProp GF) := toAgree ⟨"string1"⟩

  -- Allocate the resources
  refine emp_sep.mpr.trans <| (sep_mono (iOwn_alloc v1 (fun _ => trivial)) .rfl).trans ?_
  refine emp_sep.mpr.trans <| (sep_mono (iOwn_alloc v0 (fun _ => trivial)) .rfl).trans ?_

  -- Eliminate the bupds (by hand, until iMod is implemented)
  refine BIUpdate.frame_r.trans ?_
  refine BIUpdate.mono (sep_mono .rfl BIUpdate.frame_r) |>.trans ?_
  refine BIUpdate.mono bupd_frame_l |>.trans ?_
  refine BIUpdate.trans.trans ?_
  refine BIUpdate.mono ?_

  -- Complete the Iris proof
  istart
  iintro ⟨⟨γ0, Hγ0⟩, ⟨γ1, Hγ1⟩, -⟩
  iexists γ0
  iexists γ1
  iexists "string0"
  iexists "string1"
  isplitl [Hγ0]
  · iexact Hγ0
  · iexact Hγ1


end Example1


end Iris.Examples
