import Iris.BI.Interface

namespace Iris.BI

-- entailment
macro:25 "⊢ " P:term:25 : term => `(emp ⊢ $P)
macro:25 P:term:29 " ⊣⊢ " Q:term:29 : term => `(`[iprop| $P] ≡ `[iprop| $Q])

-- iff and wand iff
syntax:27 term:28 " ↔ " term:28 : term
syntax:27 term:28 " ∗-∗ " term:28 : term

def bi_iff      [BIBase PROP] (P Q : PROP) : PROP := `[iprop| (P → Q) ∧ (Q → P)]
def bi_wand_iff [BIBase PROP] (P Q : PROP) : PROP := `[iprop| (P -∗ Q) ∧ (Q -∗ P)]

macro_rules
  | `(`[iprop| $P ↔ $Q])   => `(bi_iff `[iprop| $P] `[iprop| $Q])
  | `(`[iprop| $P ∗-∗ $Q]) => `(bi_wand_iff `[iprop| $P] `[iprop| $Q])

-- affine and absorb
syntax:max "<affine> " term:40 : term
syntax:max "<absorb> " term:40 : term

def bi_affinely    [BIBase PROP] (P : PROP) : PROP := `[iprop| emp ∧ P]
def bi_absorbingly [BIBase PROP] (P : PROP) : PROP := `[iprop| True ∗ P]

macro_rules
  | `(`[iprop| <affine> $P]) => `(bi_affinely `[iprop| $P])
  | `(`[iprop| <absorb> $P]) => `(bi_absorbingly `[iprop| $P])

-- intuitionistic
syntax:max "□ " term:40 : term

def bi_intuitionistically [BI PROP] (P : PROP) : PROP := `[iprop| <affine> <pers> P]

macro_rules
  | `(`[iprop| □ $P]) => `(bi_intuitionistically `[iprop| $P])

-- conditional modalities
syntax:max "<pers>?"   term:max term:40 : term
syntax:max "<affine>?" term:max term:40 : term
syntax:max "<absorb>?" term:max term:40 : term
syntax:max "□?"        term:max term:40 : term

def bi_persistently_if       [BI PROP] (p : Bool) (P : PROP) : PROP := `[iprop| if p then <pers> P else P]
def bi_affinely_if           [BI PROP] (p : Bool) (P : PROP) : PROP := `[iprop| if p then <affine> P else P]
def bi_absorbingly_if        [BI PROP] (p : Bool) (P : PROP) : PROP := `[iprop| if p then <absorb> P else P]
def bi_intuitionistically_if [BI PROP] (p : Bool) (P : PROP) : PROP := `[iprop| if p then □ P else P]

macro_rules
  | `(`[iprop| <pers>?$p $P])   => `(bi_persistently_if $p `[iprop| $P])
  | `(`[iprop| <affine>?$p $P]) => `(bi_affinely_if $p `[iprop| $P])
  | `(`[iprop| <absorb>?$p $P]) => `(bi_absorbingly_if $p `[iprop| $P])
  | `(`[iprop| □?$p $P])        => `(bi_intuitionistically_if $p `[iprop| $P])

end Iris.BI
