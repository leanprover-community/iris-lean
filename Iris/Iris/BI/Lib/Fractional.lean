module

public import Iris.BI
public import Iris.ProofMode

@[expose] public section

namespace Iris
open Iris.Std BI OFE

#check BI

class Fractional [BI PROP] [UFraction F] (Φ : F → PROP) where
  fractional p q : Φ (p + q) ⊣⊢ Φ p ∗ Φ q

class AsFractional {PROP: Type u} [bi: BI PROP] [UFraction F] (P : PROP) (Φ : F → PROP) (q : F)
  -- Invalid resulting type: Expected a sort
  -- as_fractional : ?m.2
  -- as_fractional : @BiEntails PROP (bi.toBIBase) P (Φ q)
