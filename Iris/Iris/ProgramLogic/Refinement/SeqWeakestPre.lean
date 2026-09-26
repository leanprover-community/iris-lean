/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iris-Lean Contributors
-/
module

public import Iris.ProgramLogic.Refinement.RefWeakestPre
public import Iris.Instances.Lib.NaInvariantsTransfinite

/-! # Sequential reasoning (Transfinite Iris)

This file ports `theories/program_logic/refinement/seq_weakestpre.v` of Transfinite Iris: the
sequential weakest precondition `seq E e Φ` (Rocq: `SEQ e @ E ⟨⟨ v, Φ v ⟩⟩`), a refinement weakest
precondition that owns the non-atomic invariant tokens `E` before and after, so that non-atomic
invariants (`seInv`) can be opened around arbitrary (non-atomic) code.
-/

@[expose] public noncomputable section

variable {SI : Type _} [instSI : Iris.SIdx SI]
local stepindex SI

namespace Iris.Transfinite

open Iris ProgramLogic Language Iris.Std Iris.BI OFE

/-- The ghost state of sequential reasoning (Rocq: `seqG`). -/
class SeqG (GF : BundledGFunctors) extends NaInvG GF where
  name : NaInvPoolName

attribute [instance] SeqG.toNaInvG

variable {Expr State Obs Val : Type _} [Λ : Language Expr State Obs Val]
variable {GF : BundledGFunctors} {A : Type _} [src : Source GF A] [ι : RefIrisGS Expr GF]
variable [G : SeqG GF]

/-- The sequential weakest precondition (Rocq: `seq`). -/
def seq (E : CoPset) (e : Expr) (Φ : Val → IProp GF) : IProp GF :=
  iprop(NonAtomicInvariant.own G.name E -∗
    rwp (src := src) (ι := ι) .NotStuck ⊤ e fun v => iprop(NonAtomicInvariant.own G.name E ∗ Φ v))

/-- Non-atomic invariants for sequential reasoning (Rocq: `se_inv`). -/
def seInv (N : Namespace) (P : IProp GF) : IProp GF := NonAtomicInvariant.inv G.name N P

/-- Rocq: `seq_value`. -/
theorem seq_value {Φ : Val → IProp GF} {E : CoPset} (v : Val) :
    Φ v ⊢ seq (src := src) (ι := ι) E (v : Expr) Φ := by
  unfold seq
  iintro HΦ Hna
  iapply rwp_value'
  iframe

end Iris.Transfinite
