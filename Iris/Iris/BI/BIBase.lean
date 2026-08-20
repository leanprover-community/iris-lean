/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro
-/
module

public import Iris.BI.Notation
public import Iris.Std.Classes
public import Iris.Std.DelabRule
public import Iris.Std.Rewrite
public import Iris.Std.BigOp
public import Iris.Std.Notation

@[expose] public section

namespace Iris.BI
open Iris.Std
open Lean

/--
The basic components of a bunched implication (BI) algebra.

A BI algebra provides the separation logic connectives and units on a carrier
type `PROP`.

The primitive connectives and modalities are:

- `P ⊢ Q` is entailment: `P` entails `Q`.
- `⌜φ⌝` embeds a pure Lean proposition `φ` as a separation logic proposition.
- `emp` is the unit of separating conjunction.
- `P ∗ Q` is separating conjunction.
- `P -∗ Q` is separating implication (the magic wand).
- `<pers> P` is the persistently modality.
- `▷ P` is the later modality.
- `P ∧ Q` is conjunction.
- `P ∨ Q` is disjunction.
- `P → Q` is ordinary implication between BI propositions.
- `∀ x, P x` and `∃ x, P x` are the separation-logic universal and existential quantifiers.

The notation `P ⊢@{PROP} Q` can be used when the carrier type `PROP` needs to
be specified explicitly.
-/
class BIBase (PROP : Type u) where
  Entails : PROP → PROP → Prop
  emp : PROP
  pure : Prop → PROP
  and : PROP → PROP → PROP
  or : PROP → PROP → PROP
  imp : PROP → PROP → PROP
  sForall : (PROP → Prop) → PROP
  sExists : (PROP → Prop) → PROP
  sep : PROP → PROP → PROP
  wand : PROP → PROP → PROP
  persistently : PROP → PROP
  later : PROP → PROP

attribute [inherit_doc BIBase]
  BIBase.Entails BIBase.emp BIBase.pure BIBase.and BIBase.or BIBase.imp
  BIBase.sForall BIBase.sExists BIBase.sep BIBase.wand BIBase.persistently
  BIBase.later

namespace BIBase

@[inherit_doc BIBase.sForall]
def «forall» [BIBase PROP] {α : Sort _} (P : α → PROP) : PROP := sForall fun p => ∃ a, P a = p
@[inherit_doc BIBase.sExists]
def «exists» [BIBase PROP] {α : Sort _} (P : α → PROP) : PROP := sExists fun p => ∃ a, P a = p

@[inherit_doc BIBase.Entails]
macro:25 P:term:29 " ⊢ " Q:term:25 : term => ``(BIBase.Entails iprop($P) iprop($Q))

@[inherit_doc BIBase.Entails]
macro:25 P:term:29 " ⊢@{ " PROP:term "} " Q:term:25 : term =>
  ``(BIBase.Entails (PROP:=$PROP) iprop($P) iprop($Q))

delab_rule BIBase.Entails
  | `($_ $P $Q) => do ``($(← unpackIprop P) ⊢ $(← unpackIprop Q))

syntax "⌜" term "⌝" : term
syntax:35 term:36 " ∗ " term:35 : term
syntax:25 term:26 " -∗ " term:25 : term
syntax:max "<pers> " term:40 : term
syntax:max "▷ " term:40 : term

/-- Existential quantification on separation logic propositions. -/
macro "∃" xs:explicitBinders ", " b:term : term => do
  return ⟨← expandExplicitBinders ``BIBase.exists xs b⟩

-- `iprop` syntax interpretation
macro_rules
  | `(iprop(emp))           => ``(BIBase.emp)
  | `(iprop(⌜%$tk1 $φ ⌝%$tk2)) => ``($(wrapIpropSpan tk1 tk2 ``BIBase.pure) $φ)
  | `(iprop($P ∧%$tk $Q))   => ``($(wrapIprop tk ``BIBase.and) iprop($P) iprop($Q))
  | `(iprop($P ∨%$tk $Q))   => ``($(wrapIprop tk ``BIBase.or) iprop($P) iprop($Q))
  | `(iprop($P →%$tk $Q))   => ``($(wrapIprop tk ``BIBase.imp) iprop($P) iprop($Q))
  | `(iprop(∃ $xs, $Ψ)) => do expandExplicitBinders ``BIBase.exists xs (← ``(iprop($Ψ)))
  | `(iprop($P ∗%$tk $Q))   => ``($(wrapIprop tk ``BIBase.sep) iprop($P) iprop($Q))
  | `(iprop($P -∗%$tk $Q))  => ``($(wrapIprop tk ``BIBase.wand) iprop($P) iprop($Q))
  | `(iprop(<pers>%$tk $P)) => ``($(wrapIprop tk ``BIBase.persistently) iprop($P))
  | `(iprop(▷%$tk $P))     => ``($(wrapIprop tk ``BIBase.later) iprop($P))

delab_rule BIBase.emp
  | `($_) => ``(iprop($(mkIdent `emp)))
delab_rule BIBase.pure
  | `($_ $φ) => ``(iprop(⌜$φ⌝))
delab_rule BIBase.and
  | `($_ $P $Q) => do ``(iprop($(← unpackIprop P) ∧ $(← unpackIprop Q)))
delab_rule BIBase.or
  | `($_ $P $Q) => do ``(iprop($(← unpackIprop P) ∨ $(← unpackIprop Q)))
delab_rule BIBase.imp
  | `($_ $P $Q) => do ``(iprop($(← unpackIprop P) → $(← unpackIprop Q)))

/-- A delaborator for the universal quantifier. -/
@[app_delab BIBase.forall]
meta def delabBIForall : PrettyPrinter.Delaborator.Delab :=
  delabQuant 4 unpackIprop
    (fun x xs body => `(iprop(∀ $x:ident $[$xs:ident]*, $body)))
    (fun | `(∀ $x:ident $[$xs:ident]*, $Ψ) => some (x, xs, Ψ) | _ => none)

/-- A delaborator for the existential quantifier. -/
@[app_delab BIBase.exists]
meta def delabBIExist : PrettyPrinter.Delaborator.Delab :=
  delabQuant 4 unpackIprop
    (fun x xs body => `(iprop(∃ $x:ident $[$xs:ident]*, $body)))
    (fun | `(∃ $x:ident $[$xs:ident]*, $Ψ) => some (x, xs, Ψ) | _ => none)

delab_rule BIBase.sep
  | `($_ $P $Q) => do ``(iprop($(← unpackIprop P) ∗ $(← unpackIprop Q)))
delab_rule BIBase.wand
  | `($_ $P $Q) => do ``(iprop($(← unpackIprop P) -∗ $(← unpackIprop Q)))
delab_rule BIBase.persistently
  | `($_ $P) => do ``(iprop(<pers> $(← unpackIprop P)))
delab_rule BIBase.later
  | `($_ $P) => do ``(iprop(▷ $(← unpackIprop P)))

delab_rule BIBase.pure
  | `($_ True) => ``(iprop($(mkIdent `True)))
  | `($_ False) => ``(iprop($(mkIdent `False)))
delab_rule BIBase.imp
  | `($_ $P iprop(False)) => do ``(iprop(¬$(← unpackIprop P)))

/- This is necessary since the `∀` syntax is not defined using `explicitBinders` and we can
therefore not use `expandExplicitBinders` as for `∃`. -/
macro_rules
  | `(iprop(∀%$tk' _%$tk, $Ψ)) =>
    ``($(wrapIprop tk' ``BIBase.forall) (fun _%$tk => iprop($Ψ)))
macro_rules
  | `(iprop(∀%$tk' $x:ident, $Ψ)) =>
    ``($(wrapIprop tk' ``BIBase.forall) (fun $x => iprop($Ψ)))
macro_rules
  | `(iprop(∀%$tk' _%$tk : $t, $Ψ)) =>
    ``($(wrapIprop tk' ``BIBase.forall) (fun (_%$tk : $t) => iprop($Ψ)))
  | `(iprop(∀%$tk' (_%$tk : $t), $Ψ)) =>
    ``($(wrapIprop tk' ``BIBase.forall) (fun (_%$tk : $t) => iprop($Ψ)))
  | `(iprop(∀%$tk' (_%$tk $xs* : $t), $Ψ)) =>
    ``($(wrapIprop tk' ``BIBase.forall) (fun (_%$tk : $t) => iprop(∀ ($xs* : $t), $Ψ)))
macro_rules
  | `(iprop(∀%$tk' $x:ident : $t, $Ψ)) =>
    ``($(wrapIprop tk' ``BIBase.forall) (fun ($x : $t) => iprop($Ψ)))
  | `(iprop(∀%$tk' ($x:ident : $t), $Ψ)) =>
    ``($(wrapIprop tk' ``BIBase.forall) (fun ($x : $t) => iprop($Ψ)))
  | `(iprop(∀%$tk' ($x:ident $xs* : $t), $Ψ)) =>
    ``($(wrapIprop tk' ``BIBase.forall) (fun ($x : $t) => iprop(∀ ($xs* : $t), $Ψ)))
macro_rules
  | `(iprop(∀%$tk' {_%$tk : $t}, $Ψ)) =>
    ``($(wrapIprop tk' ``BIBase.forall) (fun {_%$tk : $t}  => iprop($Ψ)))
  | `(iprop(∀%$tk' {_%$tk $xs* : $t}, $Ψ)) =>
    ``($(wrapIprop tk' ``BIBase.forall) (fun {_%$tk : $t}  => iprop(∀ {$xs* : $t}, $Ψ)))
macro_rules
  | `(iprop(∀%$tk' {$x:ident : $t}, $Ψ)) =>
    ``($(wrapIprop tk' ``BIBase.forall) (fun ($x : $t) => iprop($Ψ)))
  | `(iprop(∀%$tk' {$x:ident $xs* : $t}, $Ψ)) =>
    ``($(wrapIprop tk' ``BIBase.forall) (fun ($x : $t) => iprop(∀ {$xs* : $t}, $Ψ)))
macro_rules
  | `(iprop(∀%$tk $x $y $xs*, $Ψ)) => ``(iprop(∀%$tk $x, ∀%$tk $y $xs*, $Ψ))

-- `iprop` macros
macro_rules
  | `(iprop(True))  => ``(BIBase.pure True)
  | `(iprop(False)) => ``(BIBase.pure False)
  | `(iprop(¬%$tk $P))   => ``(iprop($P →%$tk False))

/--
  Bidirectional implication on separation logic propositions.
  `P ↔ Q` holds if and only if `P → Q` and `Q → P` both hold.
-/
@[rocq_alias bi_iff]
def iff [BIBase PROP] (P Q : PROP) : PROP := iprop((P → Q) ∧ (Q → P))

/--
  Bidrectional separating implication on separation logic propositions:
  `P ∗-∗ Q` holds if and only if `P -∗ Q` and `Q -∗ P` both hold.
-/
@[rocq_alias bi_wand_iff]
def wandIff [BIBase PROP] (P Q : PROP) : PROP := iprop((P -∗ Q) ∧ (Q -∗ P))

syntax:27 term:28 " ↔ " term:28 : term
syntax:27 term:28 " ∗-∗ " term:28 : term

macro_rules
  | `(iprop($P ↔%$tk $Q))   => ``($(wrapIprop tk ``iff) iprop($P) iprop($Q))
  | `(iprop($P ∗-∗%$tk $Q)) => ``($(wrapIprop tk ``wandIff) iprop($P) iprop($Q))

delab_rule iff
  | `($_ $P $Q) => do ``(iprop($(← unpackIprop P) ↔ $(← unpackIprop Q)))
delab_rule wandIff
  | `($_ $P $Q) => do ``(iprop($(← unpackIprop P) ∗-∗ $(← unpackIprop Q)))

/--
  Separating implication with an optional premise:
  `none -∗? Q` is equivalant to `Q` while `some P -∗? Q` is equivalent to `P -∗ Q`.
-/
@[simp, rocq_alias bi_wandM]
def wandM [BIBase PROP] (mP : Option PROP) (Q : PROP) : PROP :=
  match mP with
  | none => Q
  | some P => iprop(P -∗ Q)

syntax:25 term:26 " -∗? " term:25 : term

macro_rules
  | `(iprop($mP -∗?%$tk $Q)) => ``($(wrapIprop tk ``wandM) $mP iprop($Q))

delab_rule wandM
  | `($_ $mP $Q) => do ``(iprop($mP -∗? $(← unpackIprop Q)))

/-- Affine modality: `<affine> P` is equivalent to `emp ∧ P`. -/
@[rocq_alias bi_affinely]
def affinely    [BIBase PROP] (P : PROP) : PROP := iprop(emp ∧ P)
/-- Absorbingly modality: `<absorb> P` is equivalent to `True ∗ P`. -/
@[rocq_alias bi_absorbingly]
def absorbingly [BIBase PROP] (P : PROP) : PROP := iprop(True ∗ P)

syntax:max "<affine> " term:40 : term
syntax:max "<absorb> " term:40 : term

/-- Bidirectional entailment on separation logic propositions. -/
structure BiEntails [BIBase PROP] (P Q : PROP) where
  mp : P ⊢ Q
  mpr : Q ⊢ P

/-- Entailment on separation logic propositions with an empty context. -/
@[rocq_alias bi_emp_valid]
def EmpValid [BIBase PROP] (P : PROP) : Prop := emp ⊢ P

macro:25 "⊢ " P:term:25 : term => ``(EmpValid iprop($P))
macro:25 "⊢@{ " PROP:term " } " P:term:25 : term =>
  ``(EmpValid (PROP:=$PROP) iprop($P))
macro:25 P:term:29 " ⊣⊢ " Q:term:29 : term => ``(BiEntails iprop($P) iprop($Q))
macro:25 P:term:29 " ⊣⊢@{ " PROP:term " } " Q:term:29 : term =>
  ``(BiEntails (PROP:=$PROP) iprop($P) iprop($Q))

macro_rules
  | `($P -∗ $Q)  => ``(⊢ $P -∗ $Q)

delab_rule BIBase.EmpValid
  | `($_ $P) => do ``(⊢ $(← unpackIprop P))

delab_rule BIBase.BiEntails
  | `($_ $P $Q) => do ``($(← unpackIprop P) ⊣⊢ $(← unpackIprop Q))

macro_rules
  | `(iprop(<affine>%$tk $P)) => ``($(wrapIprop tk ``affinely) iprop($P))
  | `(iprop(<absorb>%$tk $P)) => ``($(wrapIprop tk ``absorbingly) iprop($P))

delab_rule affinely
  | `($_ $P) => do ``(iprop(<affine> $(← unpackIprop P)))
delab_rule absorbingly
  | `($_ $P) => do ``(iprop(<absorb> $(← unpackIprop P)))

/-- Intuitionistic modality: `□ P` is equivalent to `<affine> <pers> P`. -/
@[rocq_alias bi_intuitionistically]
def intuitionistically [BIBase PROP] (P : PROP) : PROP := iprop(<affine> <pers> P)

syntax:max "□ " term:40 : term

macro_rules
  | `(iprop(□%$tk $P)) => ``($(wrapIprop tk ``intuitionistically) iprop($P))

delab_rule intuitionistically
  | `($_ $P) => do ``(iprop(□ $(← unpackIprop P)))

/-- Iterated later modality: `▷^[n] P` is equivalent to `P` with `n` leading occurrences of `▷`. -/
@[rocq_alias bi_laterN]
def laterN [BIBase PROP] (n : Nat) (P : PROP) : PROP := n.repeat later P

syntax:max "▷^[" term:45 "] " term:40 : term
syntax:max "▷?" term:max ppHardSpace term:40 : term

macro_rules
  | `(iprop(▷^[%$tk1 $n ]%$tk2 $P)) => ``($(wrapIpropSpan tk1 tk2 ``laterN) $n iprop($P))
  | `(iprop(▷?%$tk $p $P))          => ``($(wrapIprop tk ``laterN) (Bool.toNat $p) iprop($P))

open Lean PrettyPrinter Delaborator SubExpr in
/--
Delaborator for `laterN`. Prints `▷?p P` when the exponent is `Bool.toNat p`, i.e. when the
term came from the `▷?` notation, and `▷^[n] P` otherwise.
-/
@[app_delab laterN]
meta def delabLaterN : Delab := whenPPOption getPPNotation <| withOverApp 4 do
  let P ← withNaryArg 3 do unpackIprop (← delab)
  if (← getExpr).appFn!.appArg!.isAppOfArity ``Bool.toNat 1 then
    let p ← withNaryArg 2 <| withAppArg delab
    `(iprop(▷?$p $P))
  else
    let n ← withNaryArg 2 delab
    `(iprop(▷^[$n] $P))

/--
  Conditional persistently modality:
  `<pers>?p P` is equivalent to `<pers> P` when `p` is `true`, otherwise equivalent to `P`.
-/
@[rocq_alias bi_persistently_if]
def persistentlyIf [BIBase PROP] (p : Bool) (P : PROP) : PROP := iprop(if p then <pers> P else P)
/--
  Conditional affinely modality:
  `<affine>?p P` is equivalent to `<affine> P` when `p` is `true`, otherwise equivalent to `P`.
-/
@[rocq_alias bi_affinely_if]
def affinelyIf [BIBase PROP] (p : Bool) (P : PROP) : PROP := iprop(if p then <affine> P else P)
/--
  Conditional absorbingly modality:
  `<absorb>?p P` is equivalent to `<absorb> P` when `p` is `true`, otherwise equivalent to `P`.
-/
@[rocq_alias bi_absorbingly_if]
def absorbinglyIf [BIBase PROP] (p : Bool) (P : PROP) : PROP := iprop(if p then <absorb> P else P)
/--
  Conditional intuitionistically modality:
  `□?p P` is equivalent to `□ P` when `p` is `true`, otherwise equivalent to `P`.
-/
@[rocq_alias bi_intuitionistically_if]
def intuitionisticallyIf [BIBase PROP] (p : Bool) (P : PROP) : PROP := iprop(if p then □ P else P)

syntax:max "<pers>?" term:max ppHardSpace term:40 : term
syntax:max "<affine>?" term:max ppHardSpace term:40 : term
syntax:max "<absorb>?" term:max ppHardSpace term:40 : term
syntax:max "□?" term:max ppHardSpace term:40 : term

macro_rules
  | `(iprop(<pers>?%$tk $p $P))   => ``($(wrapIprop tk ``persistentlyIf) $p iprop($P))
  | `(iprop(<affine>?%$tk $p $P)) => ``($(wrapIprop tk ``affinelyIf) $p iprop($P))
  | `(iprop(<absorb>?%$tk $p $P)) => ``($(wrapIprop tk ``absorbinglyIf) $p iprop($P))
  | `(iprop(□?%$tk $p $P))        => ``($(wrapIprop tk ``intuitionisticallyIf) $p iprop($P))

delab_rule persistentlyIf
  | `($_ $p $P) => do ``(iprop(<pers>?$p $(← unpackIprop P)))
delab_rule affinelyIf
  | `($_ $p $P) => do ``(iprop(<affine>?$p $(← unpackIprop P)))
delab_rule absorbinglyIf
  | `($_ $p $P) => do ``(iprop(<absorb>?$p $(← unpackIprop P)))
delab_rule intuitionisticallyIf
  | `($_ $p $P) => do ``(iprop(□?$p $(← unpackIprop P)))

/-- Fold the conjunction `∧` over a list of separation logic propositions. -/
def bigAnd [BIBase PROP] (Ps : List PROP) : PROP := bigOp and iprop(True) Ps
/-- Fold the disjunction `∨` over a list of separation logic propositions. -/
def bigOr [BIBase PROP] (Ps : List PROP) : PROP := bigOp or iprop(False) Ps
/-- Fold the separating conjunction `∗` over a list of separation logic propositions. -/
def bigSep [BIBase PROP] (Ps : List PROP) : PROP := bigOp sep iprop(emp) Ps

notation:40 "[∧] " Ps:max => bigAnd Ps
notation:40 "[∨] " Ps:max => bigOr Ps
notation:40 "[∗] " Ps:max => bigSep Ps

/-- Except-0 modality: `◇ P` is equivalent to `▷ False ∨ P`. -/
@[rocq_alias bi_except_0]
def except0 [BIBase PROP] (P : PROP) := iprop(▷ False ∨ P)

syntax:max "◇ " term:40 : term

macro_rules
  | `(iprop(◇%$tk $P)) => ``($(wrapIprop tk ``except0) iprop($P))

delab_rule except0
  | `($_ $P) => do ``(iprop(◇ $(← unpackIprop P)))

/-- Plainly modality (`■`). -/
class Plainly (PROP : Type _) where
  plainly : PROP → PROP
export Plainly (plainly)

attribute [inherit_doc Plainly] Plainly.plainly
syntax "■ " term:40 : term

macro_rules
  | `(iprop(■%$tk $P))  => ``($(wrapIprop tk ``Plainly.plainly) iprop($P))

delab_rule Plainly.plainly
  | `($_ $P) => do ``(iprop(■ $(← Iris.BI.unpackIprop P)))

/--
  Conditional plainly modality:
  `■?p P` is equivalent to `■ P` when `p` is `true`, otherwise `P`.
-/
@[rocq_alias plainly_if]
def Plainly.plainlyIf [BIBase PROP] [Plainly PROP] (p : Bool) (P : PROP) : PROP :=
  iprop(if p then ■ P else P)

syntax:max "■?" term:max ppHardSpace term:40 : term

macro_rules
  | `(iprop(■?%$tk $p $P))  => ``($(wrapIprop tk ``Plainly.plainlyIf) $p iprop($P))

delab_rule Plainly.plainlyIf
  | `($_ $p $P) => do ``(iprop(■? $p $(← Iris.BI.unpackIprop P)))
