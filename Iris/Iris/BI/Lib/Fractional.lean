/-
Copyright (c) 2026 Сухарик. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Сухарик (@suhr)
-/

module

public import Iris.BI
public import Iris.ProofMode

@[expose] public section

namespace Iris
open Iris.Std BI OFE

@[rocq_alias Fractional]
class Fractional [BI PROP] (Φ : Qp → PROP) where
  fractional p q : Φ (p + q) ⊣⊢ Φ p ∗ Φ q

@[rocq_alias AsFractional]
class AsFractional {PROP: Type u} [bi: BI PROP] (P : PROP) (Φ : Qp → PROP) (q : Qp) where
  as_fractional : P ⊣⊢ Φ q
  as_fractional_fractional : Fractional Φ
