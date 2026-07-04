/-
Copyright (c) 2026 Sebastian Graf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

public import Iris.Algebra.OFE

@[expose] public section

/-! Tests for the packed Banach fixpoint `fastFixpoint`. -/

namespace Iris.Tests.FastFixpoint
open Iris OFE

instance : Inhabited (LeibnizO Nat) := ⟨⟨0⟩⟩

/-- The simplest contraction on a discrete COFE: a constant map. -/
def K : LeibnizO Nat -c> LeibnizO Nat := Function.toContractiveHom fun _ => ⟨42⟩

example : K.fastFixpoint ≡ K K.fastFixpoint := fastFixpoint_unfold K

example : K.fastFixpoint ≡ K.fixpoint := fastFixpoint_eqv K

example : (⟨42⟩ : LeibnizO Nat) ≡ K.fastFixpoint := fastFixpoint_unique (f := K) .rfl

example {n} {f g : LeibnizO Nat -c> LeibnizO Nat} (h : f ≡{n}≡ g) :
    f.fastFixpoint ≡{n}≡ g.fastFixpoint :=
  OFE.ContractiveHom.fastFixpoint_ne.ne h

/-- The unbundled form, with the `Contractive` instance found by instance search. -/
example : fastFixpoint (fun _ => (⟨42⟩ : LeibnizO Nat)) ≡ ⟨42⟩ :=
  (fastFixpoint_unique (f := K) .rfl).symm

end Iris.Tests.FastFixpoint
