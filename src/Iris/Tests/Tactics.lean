import Iris.BI
import Iris.Proofmode

namespace Iris.Tests
open Iris.BI

-- start stop
theorem startStop [BI PROP] (Q : PROP) (H : Q ⊢ Q) : Q ⊢ Q := by
  istart_proof
  iintro HQ
  istop_proof
  exact H

-- rename
namespace rename

theorem rename [BI PROP] (Q : PROP) : Q ⊢ Q := by
  iintro HQ
  irename HQ into H
  iexact H

theorem renameTwice [BI PROP] (Q : PROP) : Q ⊢ Q := by
  iintro HQ
  irename HQ into H
  irename H into HQ
  iexact HQ

theorem renameId [BI PROP] (Q : PROP) : Q ⊢ Q := by
  iintro HQ
  irename HQ into HQ
  iexact HQ

end rename

-- clear
namespace clear

theorem intuitionistic [BI PROP] (Q : PROP) : □ P ⊢ Q -∗ Q := by
  iintro #HP
  iintro HQ
  iclear HP
  iexact HQ

theorem ispatial [BI PROP] (Q : PROP) : <affine> P ⊢ Q -∗ Q := by
  iintro HP
  iintro HQ
  iclear HP
  iexact HQ

end clear

-- exact
namespace exact

theorem exact [BI PROP] (Q : PROP) : Q ⊢ Q := by
  iintro HQ
  iexact HQ

theorem defEq [BI PROP] (Q : PROP) : <affine> <pers> Q ⊢ □ Q := by
  iintro HQ
  iexact HQ

theorem intuitionistic [BI PROP] (Q : PROP) : □ Q ⊢ Q := by
  iintro HQ
  iexact HQ

end exact

-- assumption
namespace assumption

theorem exact [BI PROP] (Q : PROP) : Q ⊢ Q := by
  iintro HQ
  iassumption

theorem fromAssumption [BI PROP] (Q : PROP) : <affine> <pers> Q ⊢ □ Q := by
  iintro HQ
  iassumption

theorem intuitionistic [BI PROP] (Q : PROP) : □ Q ⊢ Q := by
  iintro #HQ
  iassumption

theorem lean [BI PROP] (Q : PROP) (H : ⊢ Q) : <affine> P ⊢ Q := by
  iintro HP
  iassumption

theorem false [BI PROP] (Q : PROP) : False ⊢ Q := by
  iintro H
  iassumption

end assumption

-- split
namespace split

theorem and [BI PROP] (Q : PROP) : Q ⊢ Q ∧ Q := by
  iintro HQ
  isplit
  <;> iexact HQ

theorem sepLeft [BIAffine PROP] (Q : PROP) : ⊢ P -∗ Q -∗ R -∗ P ∗ Q := by
  iintro HP
  iintro HQ
  iintro HR
  isplit l [HP]
  · iexact HP
  · iexact HQ

theorem sepRight [BIAffine PROP] (Q : PROP) : ⊢ P -∗ Q -∗ R -∗ P ∗ Q := by
  iintro HP
  iintro HQ
  iintro HR
  isplit r [HQ]
  · iexact HP
  · iexact HQ

theorem sepLeftAll [BIAffine PROP] (Q : PROP) : ⊢ P -∗ □ Q -∗ R -∗ P ∗ Q := by
  iintro HP
  iintro #HQ
  iintro HR
  isplit l
  · iexact HP
  · iexact HQ

theorem sepRightAll [BIAffine PROP] (Q : PROP) : ⊢ □ P -∗ Q -∗ R -∗ P ∗ Q := by
  iintro #HP
  iintro HQ
  iintro HR
  isplit r
  · iexact HP
  · iexact HQ

end split

end Iris.Tests
