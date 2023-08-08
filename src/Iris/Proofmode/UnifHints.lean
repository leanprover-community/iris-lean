/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König
-/
import Iris.BI

namespace Iris.Proofmode
open Iris.BI

/- Importing these unification hints makes some proofs more convenient for the user of the
proof interface. -/

unif_hint [BIBase PROP] (P Q : PROP) where
  |- iprop(P ↔ Q) ≟ iprop((P → Q) ∧ (Q → P))
unif_hint [BIBase PROP] (P Q : PROP) where
  |- iprop(P ∗-∗ Q) ≟ iprop((P -∗ Q) ∧ (Q -∗ P))
unif_hint [BIBase PROP] (P : PROP) where
  |- iprop(<affine> P) ≟ iprop(emp ∧ P)
unif_hint [BIBase PROP] (P : PROP) where
  |- iprop(<absorb> P) ≟ iprop(True ∗ P)
unif_hint [BIBase PROP] (P : PROP) where
  |- iprop(□ P) ≟ iprop(<affine> <pers> P)
unif_hint [BIBase PROP] (P : PROP) where
  |- iprop(<pers>?false P) ≟ iprop(P)
unif_hint [BIBase PROP] (P : PROP) where
  |- iprop(<pers>?true P) ≟ iprop(<pers> P)
unif_hint [BIBase PROP] (P : PROP) where
  |- iprop(<affine>?false P) ≟ iprop(P)
unif_hint [BIBase PROP] (P : PROP) where
  |- iprop(<affine>?true P) ≟ iprop(<affine> P)
unif_hint [BIBase PROP] (P : PROP) where
  |- iprop(<absorb>?false P) ≟ iprop(P)
unif_hint [BIBase PROP] (P : PROP) where
  |- iprop(<absorb>?true P) ≟ iprop(<absorb> P)
unif_hint [BIBase PROP] (P : PROP) where
  |- iprop(□?false P) ≟ iprop(P)
unif_hint [BIBase PROP] (P : PROP) where
  |- iprop(□?true P) ≟ iprop(□ P)

end Iris.Proofmode
