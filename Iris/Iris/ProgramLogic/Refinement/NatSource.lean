/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iris-Lean Contributors
-/
module

public import Iris.ProgramLogic.Refinement.RefAuthSource
public import Iris.Algebra.Numbers

/-! # The natural-number authoritative source (Transfinite Iris)

This file ports `nat_auth_source` of `theories/program_logic/refinement/ref_source.v`: natural
numbers under addition, where a source step decreases the number (Rocq: `natA`). Fragments `$ n`
are (finite) credits.

The natural numbers are wrapped in `NatC SI`, whose type determines the step-index type, so that
the camera instances can be found by instance resolution for any `SI`.
-/

@[expose] public noncomputable section

universe u v

variable {SI : Type v} [instSI : Iris.SIdx SI]
local stepindex SI

namespace Iris.Transfinite

open _root_.Std (Associative Commutative LeftIdentity LawfulLeftIdentity)
open Iris Iris.Std Iris.BI OFE CMRA

/-- Natural numbers, as a camera over the step-index type `SI`. -/
@[ext] structure NatC (SI : Type v) : Type v where
  n : Nat

namespace NatC

instance : Add (NatC SI) := ⟨fun a b => ⟨a.n + b.n⟩⟩
instance : Zero (NatC SI) := ⟨⟨0⟩⟩

@[simp] theorem add_n (a b : NatC SI) : (a + b).n = a.n + b.n := rfl
@[simp] theorem zero_n : (0 : NatC SI).n = 0 := rfl

instance : Associative (α := NatC SI) (· + ·) := ⟨fun _ _ _ => NatC.ext (Nat.add_assoc _ _ _)⟩
instance : Commutative (α := NatC SI) (· + ·) := ⟨fun _ _ => NatC.ext (Nat.add_comm _ _)⟩
instance : LeftIdentity (α := NatC SI) (· + ·) (0 : NatC SI) where
instance : LawfulLeftIdentity (α := NatC SI) (· + ·) (0 : NatC SI) :=
  ⟨fun _ => NatC.ext (Nat.zero_add _)⟩

instance : COFE (NatC SI) := COFE.ofDiscrete _
instance : OFE.Discrete (NatC SI) := ⟨fun h => h⟩
instance : UCMRA (NatC SI) := CommMonoidLike.instUCMRA
instance : CMRA.Discrete (NatC SI) := CommMonoidLike.instDiscrete

theorem op_n (a b : NatC SI) : (a • b).n = a.n + b.n := rfl

end NatC

/-- The ghost state of natural-number credits (Rocq: `auth_sourceG Σ natA`). -/
class NatSourceG (GF : BundledGFunctors.{u}) where
  elem : ElemG GF (constOFU.{max u v} (Auth (NatC SI)))
  name : GName

/-- The natural-number authoritative source (Rocq: `natA`, `nat_credit`). -/
instance natA {GF : BundledGFunctors} [G : NatSourceG GF] : AuthSourceG GF (NatC SI) where
  elem := G.elem
  name := G.name
  trans a a' := a'.n < a.n
  step_frame {a a' f} h _ := ⟨trivial, by simp only [NatC.op_n]; omega⟩
  op_cancel {a f f'} _ h := by
    have := congrArg NatC.n h
    simp only [NatC.op_n] at this
    exact NatC.ext (by omega)

variable {GF : BundledGFunctors} [NatSourceG GF]

/-- Rocq: `nat_srcF_split`. -/
theorem nat_srcF_split (n m : Nat) :
    srcF (GF := GF) (⟨n + m⟩ : NatC SI) ⊣⊢ srcF (GF := GF) (⟨n⟩ : NatC SI) ∗ srcF (GF := GF) (⟨m⟩ : NatC SI) :=
  srcF_split (s := (⟨n⟩ : NatC SI)) (t := ⟨m⟩)

/-- Rocq: `nat_srcF_succ`. -/
theorem nat_srcF_succ (n : Nat) :
    srcF (GF := GF) (⟨n + 1⟩ : NatC SI) ⊣⊢ srcF (GF := GF) (⟨1⟩ : NatC SI) ∗ srcF (GF := GF) (⟨n⟩ : NatC SI) := by
  rw [Nat.add_comm]
  exact nat_srcF_split 1 n

end Iris.Transfinite
