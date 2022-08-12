import Iris.BI
import Iris.Proofmode

namespace Iris.Tests
open Iris.BI

-- start stop
theorem startStop [BI PROP] (Q : PROP) (H : Q ⊢ Q) : Q ⊢ Q := by
  istart
  iintro HQ
  istop
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

-- intro
namespace intro

theorem spatial [BI PROP] (Q : PROP) : Q ⊢ Q := by
  iintro HQ
  iexact HQ

theorem intuitionistic [BI PROP] (Q : PROP) : □ Q ⊢ Q := by
  iintro #HQ
  iexact HQ

theorem drop [BI PROP] (Q : PROP) : ⊢ P → Q -∗ Q := by
  iintro _ HQ
  iexact HQ

theorem dropAfter [BI PROP] (Q : PROP) : ⊢ Q -∗ P → Q := by
  iintro HQ _
  iexact HQ

theorem «forall» [BI PROP] : ⊢ ∀ x, ⌜x = 0⌝ → (⌜x = 0⌝ : PROP) := by
  iintro %x
  iintro H
  iexact H

theorem pure [BIAffine PROP] (Q : PROP) : ⊢ ⌜φ⌝ -∗ Q -∗ Q := by
  iintro %Hφ HQ
  iexact HQ

theorem pattern [BI PROP] (Q : PROP) : □ (P1 ∨ P2) ∗ Q ⊢ Q := by
  iintro ⟨#(HP1 | HP2), HQ⟩
  <;> iexact HQ

theorem multipleSpatial [BI PROP] (Q : PROP) : ⊢ <affine> P -∗ Q -∗ Q := by
  iintro HP HQ
  iexact HQ

theorem multipleIntuitionistic [BI PROP] (Q : PROP) : ⊢ □ P -∗ □ Q -∗ Q := by
  iintro #HP #HQ
  iexact HQ

theorem multiplePatterns [BI PROP] (Q : PROP) : ⊢ □ (P1 ∧ P2) -∗ Q ∨ Q -∗ Q := by
  iintro #⟨HP1, -#HP2⟩ (HQ | HQ)
  <;> iexact HQ

end intro

-- exist
namespace exist

theorem id [BI PROP] : ⊢ (∃ x, x : PROP) := by
  iexists `[iprop| True]
  ipure_intro
  exact True.intro

theorem f [BI PROP] : ⊢ (∃ (_x : Nat), True ∨ False : PROP) := by
  iexists 42
  ileft
  ipure_intro
  exact True.intro

theorem pure [BI PROP] : ⊢ (⌜∃ x, x ∨ False⌝ : PROP) := by
  iexists True
  ipure_intro
  exact Or.inl True.intro

end exist

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

theorem leanPure [BI PROP] (Q : PROP) : <affine> ⌜⊢ Q⌝ ⊢ Q := by
  iintro %H
  iassumption

theorem false [BI PROP] (Q : PROP) : False ⊢ Q := by
  iintro H
  iassumption

end assumption

-- ex falso
namespace exfalso

theorem false [BI PROP] (P : PROP) : □ P ⊢ False -∗ Q := by
  iintro HP HF
  iex_falso
  iexact HF

theorem pure [BI PROP] (P : PROP) (HF : False) : ⊢ P := by
  istart
  iex_falso
  ipure_intro
  exact HF

end exfalso

-- pure
namespace pure

theorem move [BI PROP] (Q : PROP) : <affine> ⌜φ⌝ ⊢ Q -∗ Q := by
  iintro Hφ
  iintro HQ
  ipure Hφ
  iexact HQ

theorem moveMultiple [BI PROP] (Q : PROP) : <affine> ⌜φ1⌝ ⊢ <affine> ⌜φ2⌝ -∗ Q -∗ Q := by
  iintro Hφ1
  iintro Hφ2
  iintro HQ
  ipure Hφ1
  ipure Hφ2
  iexact HQ

theorem moveConjunction [BI PROP] (Q : PROP) : (⌜φ1⌝ ∧ <affine> ⌜φ2⌝) ⊢ Q -∗ Q := by
  iintro Hφ
  iintro HQ
  ipure Hφ
  iexact HQ

end pure

-- intuitionistic
namespace intuitionistic

theorem move [BI PROP] (P : PROP) : □ P ⊢ Q -∗ Q := by
  iintro HP
  iintro HQ
  iintuitionistic HP
  iexact HQ

theorem moveMultiple [BI PROP] (P : PROP) : □ P ⊢ □ Q -∗ Q := by
  iintro HP
  iintro HQ
  iintuitionistic HP
  iintuitionistic HQ
  iexact HQ

theorem moveTwice [BI PROP] (P : PROP) : □ P ⊢ Q -∗ Q := by
  iintro HP
  iintro HQ
  iintuitionistic HP
  iintuitionistic HP
  iexact HQ

end intuitionistic

-- spatial
namespace spatial

theorem move [BI PROP] (P : PROP) : □ P ⊢ □ Q -∗ Q := by
  iintro #HP
  iintro #HQ
  ispatial HP
  iexact HQ

theorem moveMultiple [BI PROP] (P : PROP) : □ P ⊢ □ Q -∗ Q := by
  iintro #HP
  iintro #HQ
  ispatial HP
  ispatial HQ
  iexact HQ

theorem moveTwice [BI PROP] (P : PROP) : □ P ⊢ □ Q -∗ Q := by
  iintro #HP
  iintro #HQ
  ispatial HP
  ispatial HP
  iexact HQ

end spatial

-- emp intro
namespace empintro

theorem simple [BI PROP] : ⊢ (emp : PROP) := by
  iemp_intro

theorem affineEnv [BI PROP] (P : PROP) : <affine> P ⊢ emp := by
  iintro HP
  iemp_intro

end empintro

-- pure intro
namespace pureintro

theorem simple [BI PROP] : ⊢ (⌜True⌝ : PROP) := by
  ipure_intro
  exact True.intro

theorem or [BI PROP] : ⊢ True ∨ (False : PROP) := by
  ipure_intro
  apply Or.inl True.intro

theorem withProof [BI PROP] (H : A → B) (P Q : PROP) : <affine> P ⊢ <pers> Q → ⌜A⌝ → ⌜B⌝ := by
  iintro HP #HQ
  ipure_intro
  exact H

end pureintro

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

-- left / right
namespace leftright

theorem left [BI PROP] (P : PROP) : P ⊢ P ∨ Q := by
  iintro HP
  ileft
  iexact HP

theorem right [BI PROP] (Q : PROP) : Q ⊢ P ∨ Q := by
  iintro HQ
  iright
  iexact HQ

theorem complex [BI PROP] (P Q : PROP) : ⊢ P -∗ Q -∗ P ∗ (R ∨ Q ∨ R) := by
  iintro HP HQ
  isplit l [HP]
  · iassumption
  iright
  ileft
  iexact HQ

end leftright

-- cases
namespace cases

theorem rename [BI PROP] (P : PROP) : P ⊢ P := by
  iintro HP
  icases HP with H
  iexact H

theorem clear [BI PROP] (P Q : PROP) : ⊢ P -∗ <affine> Q -∗ P := by
  iintro HP
  iintro HQ
  icases HQ with _
  iexact HP

theorem and [BI PROP] (Q : PROP) : □ (P1 ∧ P2 ∧ Q) ⊢ Q := by
  iintro #HP
  icases HP with ⟨HP1, HP2, HQ⟩
  iexact HQ

theorem andIntuitionistic [BI PROP] (Q : PROP) : □ P ∧ Q ⊢ Q := by
  iintro HPQ
  icases HPQ with ⟨HP, HQ⟩
  iexact HQ

theorem andPersistentLeft [BI PROP] (Q : PROP) : <pers> Q ∧ <affine> P ⊢ Q := by
  iintro HQP
  icases HQP with ⟨#HQ, HP⟩
  iexact HQ

theorem andPersistentRight [BI PROP] (Q : PROP) : Q ∧ <pers> P ⊢ Q := by
  iintro HQP
  icases HQP with ⟨HQ, HP⟩
  iexact HQ

theorem sep [BIAffine PROP] (Q : PROP) : P1 ∗ P2 ∗ Q ⊢ Q := by
  iintro HPQ
  icases HPQ with ⟨HP1, HP2, HQ⟩
  iexact HQ

theorem disjunction [BI PROP] (Q : PROP) : Q ⊢ <affine> (P1 ∨ P2 ∨ P3) -∗ Q := by
  iintro HQ
  iintro HP
  icases HP with (HP1 | HP2 | HP3)
  <;> iexact HQ

theorem conjunctionAndDisjunction [BIAffine PROP] (Q : PROP) : (P11 ∨ P12 ∨ P13) ∗ P2 ∗ (P31 ∨ P32 ∨ P33) ∗ Q ⊢ Q := by
  iintro HP
  icases HP with ⟨HP11 | HP12 | HP13, HP2, HP31 | HP32 | HP33, HQ⟩
  <;> iexact HQ

theorem moveToPure [BI PROP] (Q : PROP) : ⊢ <affine> ⌜φ⌝ -∗ Q -∗ Q := by
  iintro Hφ
  iintro HQ
  icases Hφ with %Hφ
  iexact HQ

theorem moveToIntuitionistic [BI PROP] (Q : PROP) : ⊢ □ Q -∗ Q := by
  iintro HQ
  icases HQ with #HQ
  iexact HQ

theorem moveToSpatial [BI PROP] (Q : PROP) : ⊢ □ Q -∗ Q := by
  iintro #HQ
  icases HQ with -#HQ
  iexact HQ

theorem moveToPureConjunction [BI PROP] (Q : PROP) : ⊢ <affine> ⌜φ⌝ ∗ Q -∗ Q := by
  iintro HφQ
  icases HφQ with ⟨%Hφ, HQ⟩
  iexact HQ

theorem moveToPureDisjunction [BI PROP] (Q : PROP) : ⊢ <affine> ⌜φ1⌝ ∨ <affine> ⌜φ2⌝ -∗ Q -∗ Q := by
  iintro Hφ
  iintro HQ
  icases Hφ with (%Hφ1 | %Hφ2)
  <;> iexact HQ

theorem moveToIntuitionisticConjunction [BI PROP] (Q : PROP) : ⊢ □ P ∗ Q -∗ Q := by
  iintro HPQ
  icases HPQ with ⟨#HP, HQ⟩
  iexact HQ

theorem moveToIntuitionisticDisjunction [BI PROP] (Q : PROP) : ⊢ □ Q ∨ Q -∗ Q := by
  iintro HQQ
  icases HQQ with (#HQ | HQ)
  <;> iexact HQ

theorem moveToSpatialConjunction [BI PROP] (Q : PROP) : ⊢ □ (P ∧ Q) -∗ Q := by
  iintro #HPQ
  icases HPQ with ⟨HP, -#HQ⟩
  iexact HQ

theorem moveToSpatialDisjunction [BI PROP] (Q : PROP) : ⊢ □ (Q ∨ Q) -∗ Q := by
  iintro #HPQ
  icases HPQ with (HQ | -#HQ)
  <;> iexact HQ

theorem moveToIntuitionisticAndBackConjunction [BI PROP] (Q : PROP) : ⊢ □ (P ∧ Q) -∗ Q := by
  iintro HPQ
  icases HPQ with #⟨HP, -#HQ⟩
  iexact HQ

theorem moveToIntuitionisticAndBackDisjunction [BI PROP] (Q : PROP) : ⊢ □ (Q ∨ Q) -∗ Q := by
  iintro HPQ
  icases HPQ with #(HQ | -#HQ)
  <;> iexact HQ

theorem conjunctionClear [BIAffine PROP] (Q : PROP) : Q ∗ P ⊢ Q := by
  iintro HQP
  icases HQP with ⟨HQ, _⟩
  <;> iexact HQ

theorem disjunctionClear [BIAffine PROP] (Q : PROP) : Q ⊢ P1 ∨ P2 -∗ Q := by
  iintro HQ
  iintro HP
  icases HP with (_ | HP2)
  <;> iexact HQ

theorem andDestructSpatialRight [BI PROP] (Q : PROP) : P ∧ Q ⊢ Q := by
  iintro HPQ
  icases HPQ with ⟨_, HQ⟩
  iexact HQ

theorem andDestructSpatialLeft [BI PROP] (Q : PROP) : Q ∧ P ⊢ Q := by
  iintro HQP
  icases HQP with ⟨HQ, _⟩
  iexact HQ

theorem andClearSpatialMultiple [BI PROP] (Q : PROP) : P1 ∧ P2 ∧ Q ∧ P3 ⊢ Q := by
  iintro HPQ
  icases HPQ with ⟨_, _, HQ, _⟩
  iexact HQ

theorem andDestructIntuitionisticRight [BI PROP] (Q : PROP) : □ (P ∧ Q) ⊢ Q := by
  iintro #HPQ
  icases HPQ with ⟨_, HQ⟩
  iexact HQ

theorem andDestructIntuitionisticLeft [BI PROP] (Q : PROP) : □ (Q ∧ P) ⊢ Q := by
  iintro #HQP
  icases HQP with ⟨HQ, _⟩
  iexact HQ

theorem andClearIntuitionisticMultiple [BI PROP] (Q : PROP) : □ (P1 ∧ P2 ∧ Q ∧ P3) ⊢ Q := by
  iintro #HPQ
  icases HPQ with ⟨_, _, HQ, _⟩
  iexact HQ

theorem exist [BI PROP] (Q : Nat → PROP) : (∃ x, Q x) ⊢ ∃ x, Q x ∨ False := by
  iintro ⟨x, H⟩
  iexists x
  ileft
  iexact H

theorem exist_intuitionistic [BI PROP] (Q : Nat → PROP) : □ (∃ x, Q x) ⊢ ∃ x, □ Q x ∨ False := by
  iintro ⟨x, #H⟩
  iexists x
  ileft
  iexact H

end cases
end Iris.Tests
