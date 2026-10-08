/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Michael Sammler, Markus de Medeiros, Janine Lohse
-/
module

public import Iris.BI.Sbi
public import Iris.BI.Plainly
public import Iris.BI.InternalEq

@[expose] public section


variable {SI : Type _} [Iris.SIdx SI]

/-!
# Generic ORA validity in a BI logic

This file defines the generic internal ORA validity for any `Sbi PROP`,
as `<si_pure> cmraValid a`.
-/

namespace Iris
open BI OFE SiProp ORA Sbi

section CmraValid

variable [BI PROP] [BIStepIndexed SI PROP] [Sbi SI PROP] [ORA SI A]

@[rocq_alias internal_cmra_valid]
def internalCmraValid (a : A) : PROP := siPure (cmraValid (SI := SI) a)

macro_rules
  | `(iprop(✓[%$tk $si] $a)) => ``($(wrapIprop tk ``internalCmraValid) (SI := $si) $a)

open Lean PrettyPrinter Delaborator SubExpr in
/-- Print `internalCmraValid` as `iprop(✓[SI] a)`, recovering the step index argument. -/
@[app_delab internalCmraValid] meta def delabInternalCmraValid : Delab :=
  whenPPOption getPPNotation do
    let e ← getExpr
    guard (e.getAppNumArgs ≥ 2)
    let si ← withNaryArg 2 delab
    let a ← withNaryArg (e.getAppNumArgs - 1) delab
    `(iprop(✓[$si] $a))

@[rocq_alias internal_cmra_valid_ne]
instance internalCmraValid_ne : NonExpansive SI (internalCmraValid (SI := SI) (PROP := PROP) (A := A)) where
  ne _ _ _ h := siPure_ne.ne (instNonExpansiveCmraValid.ne h)

#rocq_ignore internal_cmra_valid_proper "Derivable from internalCmraValid_ne with NonExpansive.eqv"

@[rocq_alias internal_cmra_valid_intro]
theorem internalCmraValid_intro {P : PROP} {a : A} (h : ✓[SI] a) :
    P ⊢ ✓[SI] a :=
  calc (P : PROP)
    _ ⊢ True := true_intro
    _ ⊢ <si_pure> True := siPure_pure.mpr
    _ ⊢ ✓[SI] a := siPure_mono (cmraValid_intro h)

@[rocq_alias internal_cmra_valid_elim]
theorem internalCmraValid_elim (a : A) : ✓[SI] a ⊢@{PROP} ⌜✓{(0 : SI)} a⌝ :=
  calc iprop(✓[SI] a)
    _ ⊢ <si_pure> ⌜✓{(0 : SI)} a⌝ := siPure_mono cmraValid_elim
    _ ⊢ ⌜✓{(0 : SI)} a⌝ := siPure_pure.mp

@[rocq_alias internal_cmra_valid_weaken]
theorem internalCmraValid_weaken {a b : A} :
    ✓[SI] (a • b) ⊢@{PROP} ✓[SI] a :=
  siPure_mono cmraValid_weaken

@[rocq_alias internal_cmra_valid_entails]
theorem internalCmraValid_entails [ORA SI B] {a : A} {b : B} :
    (✓[SI] a ⊢@{PROP} ✓[SI] b) ↔ ∀ (n : SI), ✓{n} a → ✓{n} b :=
  siPure_entails.trans cmraValid_entails_iff

@[rocq_alias si_pure_internal_cmra_valid]
theorem siPure_internalCmraValid {a : A} : <si_pure> cmraValid (SI := SI) a ⊣⊢@{PROP} ✓[SI] a :=
  .rfl

@[rocq_alias persistently_internal_cmra_valid]
theorem persistently_internalCmraValid {a : A} :
    <pers> ✓[SI] a ⊣⊢@{PROP} ✓[SI] a :=
  persistently_siPure

@[rocq_alias plainly_internal_cmra_valid]
theorem plainly_internalCmraValid (a : A) :
    ■ ✓[SI] a ⊣⊢@{PROP} ✓[SI] a :=
  plainly_siPure

@[rocq_alias intuitionistically_internal_cmra_valid]
theorem intuitionistically_internalCmraValid [BIAffine PROP] {a : A} :
    □ ✓[SI] a ⊣⊢@{PROP} ✓[SI] a :=
  intuitionistically_iff_persistently.trans persistently_internalCmraValid

@[rocq_alias internal_cmra_valid_discrete]
theorem internalCmraValid_discrete [ORA.Discrete SI A] {a : A} :
    ✓[SI] a ⊣⊢@{PROP} ⌜✓[SI] a⌝ :=
  ⟨(internalCmraValid_elim a).trans <| pure_mono (discrete_valid ·),
   pure_elim' internalCmraValid_intro⟩

@[rocq_alias internal_cmra_valid_persistent]
instance internalCmraValid_persistent (a : A) :
    Persistent (PROP := PROP) iprop(✓[SI] a) where
  persistent := persistently_internalCmraValid.mpr

@[rocq_alias internal_cmra_valid_absorbing]
instance internalCmraValid_absorbing (a : A) :
    Absorbing (PROP := PROP) iprop(✓[SI] a) :=
  siPure_absorbing _

@[rocq_alias internal_cmra_valid_plain]
instance internalCmraValid_plain (a : A) :
    Plain (PROP := PROP) iprop(✓[SI] a) where
  plain := plainly_internalCmraValid a |>.mpr

@[rocq_alias internal_cmra_valid_timeless]
instance internalCmraValid_timeless [ORA.Discrete SI A] (a : A) :
    Timeless (PROP := PROP) iprop(✓[SI] a) :=
  siPure_timeless _

end CmraValid

section CmraOrder

variable [BI PROP] [BIStepIndexed SI PROP] [Sbi SI PROP] [ORA SI A]

/-! ### The internal extension inclusion -/

/-- The internal extension inclusion `∃ c, b ≡ a • c`, the relation frame-based
constructions (views, local updates) are stated with; see `internalCmraOrder` for the
internal order. -/
@[rocq_alias internal_included]
def internalCmraIncluded (a b : A) : PROP := siPure ((∃ c, iprop(b ≡[SI] (a • c))) : SiProp SI)

/-- Internal inclusion `a ≼[S] b` inside `iprop(…)`, with the step index `S` explicit. -/
syntax:50 term:51 " ≼[" term "] " term:51 : term
macro_rules
  | `(iprop($a ≼[%$tk $si] $b)) => ``($(wrapIprop tk ``internalCmraIncluded) (SI := $si) $a $b)

open Lean PrettyPrinter Delaborator SubExpr in
/-- Print `internalCmraIncluded` as `iprop(a ≼[SI] b)`, recovering the step index argument. -/
@[app_delab internalCmraIncluded] meta def delabInternalCmraIncluded : Delab :=
  whenPPOption getPPNotation do
    let e ← getExpr
    guard (e.getAppNumArgs ≥ 3)
    let si ← withNaryArg 2 delab
    let a ← withNaryArg (e.getAppNumArgs - 2) delab
    let b ← withNaryArg (e.getAppNumArgs - 1) delab
    `(iprop($a ≼[$si] $b))

@[rocq_alias internal_included_nonexpansive]
instance internalCmraIncluded_ne :
    NonExpansive₂ SI (internalCmraIncluded (SI := SI) (PROP := PROP) (A := A)) where
  ne n _ _ hx _ _ hy := by
    refine siPure_ne.ne ?_
    apply (exists_ne (fun a => NonExpansive₂.ne hy (op_commN.trans ((op_ne.ne hx).trans op_commN))))

#rocq_ignore internal_included_proper "Derivable from internalCmraIncluded_ne with NonExpansive.eqv"

@[rocq_alias internal_included_intro]
theorem internalCmraIncluded_intro {P : PROP} {a b : A} (h : a ≼ b) :
    P ⊢ a ≼[SI] b := by
  obtain ⟨c, hc⟩ := h
  calc (P : PROP)
    _ ⊢ True := true_intro
    _ ⊢ <si_pure> True := siPure_pure.mpr
    _ ⊢ a ≼[SI] b := siPure_mono (BI.exists_intro_trans c (internalEq.of_equiv hc))

/-- The `SiProp SI` underlying the internal `≼` holds at `n` exactly when `a ≼{n} b`. -/
private theorem inc_holds {a b : A} {n : SI} :
    ((∃ c, iprop(b ≡[SI] (a • c))) : SiProp SI).holds n ↔ a ≼{n} b := SiProp.exists_holds

/-- Two internal extension inclusions agree when they agree at every step index. -/
theorem internalCmraIncluded_iff [ORA SI B] {a b : A} {a' b' : B}
    (h : ∀ (n : SI), a ≼{n} b ↔ a' ≼{n} b') : a ≼[SI] b ⊣⊢@{PROP} a' ≼[SI] b' :=
  siPure_mono_bi ⟨fun n hn => inc_holds.mpr ((h n).mp (inc_holds.mp hn)),
    fun n hn => inc_holds.mpr ((h n).mpr (inc_holds.mp hn))⟩

/-- An internal extension inclusion that is step-index independent is a pure proposition. -/
theorem internalCmraIncluded_pure {a b : A} {φ : Prop} (h : ∀ (n : SI), a ≼{n} b ↔ φ) :
    a ≼[SI] b ⊣⊢@{PROP} ⌜φ⌝ :=
  ⟨.trans (siPure_mono fun n hn => (h n).mp (inc_holds.mp hn)) siPure_pure.mp,
   .trans siPure_pure.mpr (siPure_mono fun n hφ => inc_holds.mpr ((h n).mpr hφ))⟩

@[rocq_alias si_pure_internal_included]
theorem siPure_internalCmraIncluded {a b : A} :
    <si_pure> (iprop(a ≼[SI] b) : SiProp SI) ⊣⊢@{PROP} a ≼[SI] b :=
  persistently_iff.symm.trans persistently_siPure

@[rocq_alias persistently_internal_included]
theorem persistently_internalCmraIncluded {a b : A} :
    <pers> a ≼[SI] b ⊣⊢@{PROP} a ≼[SI] b :=
  persistently_siPure

@[rocq_alias plainly_internal_included]
theorem plainly_internalCmraIncluded {a b : A} :
    ■ a ≼[SI] b ⊣⊢@{PROP} a ≼[SI] b :=
  plainly_siPure

@[rocq_alias intuitionistically_internal_included]
theorem intuitionistically_internalCmraIncluded [BIAffine PROP] {a b : A} :
    □ a ≼[SI] b ⊣⊢@{PROP} a ≼[SI] b :=
  intuitionistically_iff_persistently.trans persistently_internalCmraIncluded

@[rocq_alias internal_included_discrete]
theorem internalCmraIncluded_discrete {a b : A} [ORA.Discrete SI A] :
    a ≼[SI] b ⊣⊢@{PROP} ⌜a ≼ b⌝ := by
  haveI : ∀ x : A, DiscreteE SI x := fun x => ⟨OFE.Discrete.discrete⟩
  refine ⟨?_, pure_elim' internalCmraIncluded_intro⟩
  calc internalCmraIncluded a b
    _ ⊢ <si_pure> (∃ c, b ≡[SI] (a • c)) := siPure_internalCmraIncluded.mp
    _ ⊢ <si_pure> (∃ c, ⌜b = a • c⌝) := siPure_mono <| exists_mono fun _ => discrete_eq_mp
    _ ⊢ <si_pure> ⌜∃ c, b = a • c⌝ := siPure_mono pure_exists.mp
    _ ⊢ ⌜∃ c, b = a • c⌝ := siPure_pure.mp
    _ ⊢ ⌜a ≼ b⌝ := pure_mono fun ⟨c, h⟩ => ⟨c, h⟩

@[rocq_alias internal_included_refl]
theorem internalCmraIncluded_refl {a : A} [IsTotal A] : ⊢@{PROP} a ≼[SI] a :=
  internalCmraIncluded_intro .rfl

@[rocq_alias internal_included_trans]
theorem internalCmraIncluded_trans {a b c : A} :
    ⊢@{PROP} a ≼[SI] b -∗ b ≼[SI] c -∗ a ≼[SI] c := by
  refine BI.entails_wand (siPure_exist.mp.trans ?_)
  refine BI.exists_elim (fun a' => ?_)
  refine BI.wand_intro ((BI.sep_mono_right siPure_exist.mp).trans (BI.sep_exists_left.mp.trans ?_))
  refine BI.exists_elim (fun b' => ?_)
  refine siPure_and_sep.mpr.trans (siPure_mono ?_)
  refine BI.exists_intro_trans (a' • b') ?_
  refine Entails.trans ?_ (internalEq.trans (b := (a • a') • b'))
  refine and_intro ?_ (internalEq.of_equiv assoc'.symm)
  refine Entails.trans ?_ (internalEq.trans (b := (b • b')))
  exact and_intro and_elim_r (and_elim_left_trans (BI.internalEq_entails.mpr (fun n heq => op_left_dist _ heq)))

/-- The internal `≼` is monotone under any nonexpansive map commuting with `•`. -/
theorem internalCmraIncluded_map {B : Type _} [ORA SI B] (g : A → B) [NonExpansive SI g]
    (hg : ∀ x y : A, g (x • y) = g x • g y) {a b : A} :
    a ≼[SI] b ⊢@{PROP} g a ≼[SI] g b :=
  siPure_mono <| BI.exists_elim fun c => BI.exists_intro_trans (g c) <| by
    rw [← hg]; exact internalEq.of_internalEquiv_ne g

@[rocq_alias internal_included_timeless]
instance internalCmraIncluded_timeless {a b : A} [ORA.Discrete SI A] :
    Timeless (PROP := PROP) iprop(a ≼[SI] b) := by
  haveI : ∀ x : A, DiscreteE SI x := fun x => ⟨OFE.Discrete.discrete⟩
  unfold internalCmraIncluded
  infer_instance

@[rocq_alias internal_included_plain]
instance internalCmraIncluded_plain {a b : A} :
    Plain (PROP := PROP) iprop(a ≼[SI] b) where
  plain := plainly_internalCmraIncluded.mpr

@[rocq_alias internal_included_persistent]
instance internalCmraIncluded_persistent {a b : A} :
    Persistent (PROP := PROP) iprop(a ≼[SI] b) where
  persistent := persistently_internalCmraIncluded.mpr

@[rocq_alias internal_included_absorbing]
instance internalCmraIncluded_absorbing {a b : A} :
    Absorbing (PROP := PROP) iprop(a ≼[SI] b) :=
  siPure_absorbing _

/-! ### The internal order -/

def _root_.SiProp.cmraOrder (a b : A) : SiProp SI where
  holds n := a ≼ₒ{n} b
  closed h hle := h.le hle

instance _root_.SiProp.cmraOrder_timeless [ORA.Discrete SI A] {a b : A} :
    Timeless (SiProp.cmraOrder (SI := SI) a b) where
  timeless := fun _ h =>
    ordN_of_ord _ (discrete_ord (h 0 SIdx.le_0_l fun k hk => absurd hk (SIdx.not_lt_zero k)))

/-- The internal order `a ≼ₒ b`, holding at step index `n` when `a ≼ₒ{n} b`; ownership is
monotone along it (`ownM_mono`). -/
def internalCmraOrder (a b : A) : PROP := siPure (SiProp.cmraOrder (SI := SI) a b)

macro_rules
  | `(iprop($a ≼ₒ[%$tk $si] $b)) => ``($(wrapIprop tk ``internalCmraOrder) (SI := $si) $a $b)

open Lean PrettyPrinter Delaborator SubExpr in
/-- Print `internalCmraOrder` as `iprop(a ≼ₒ[SI] b)`, recovering the step index argument. -/
@[app_delab internalCmraOrder] meta def delabInternalCmraOrder : Delab :=
  whenPPOption getPPNotation do
    let e ← getExpr
    guard (e.getAppNumArgs ≥ 3)
    let si ← withNaryArg 2 delab
    let a ← withNaryArg (e.getAppNumArgs - 2) delab
    let b ← withNaryArg (e.getAppNumArgs - 1) delab
    `(iprop($a ≼ₒ[$si] $b))

instance internalCmraOrder_ne :
    NonExpansive₂ SI (internalCmraOrder (SI := SI) (PROP := PROP) (A := A)) where
  ne _ _ _ hx _ _ hy := siPure_ne.ne fun hm => ordN_dist_iff (hx.le hm) (hy.le hm)

theorem internalCmraOrder_intro {P : PROP} {a b : A} (h : a ≼ₒ[SI] b) : P ⊢ a ≼ₒ[SI] b :=
  calc (P : PROP)
    _ ⊢ True := true_intro
    _ ⊢ <si_pure> True := siPure_pure.mpr
    _ ⊢ a ≼ₒ[SI] b := siPure_mono fun n _ => ordN_of_ord n h

/-- Two internal orders agree when they agree at every step index. -/
theorem internalCmraOrder_iff [ORA SI B] {a b : A} {a' b' : B}
    (h : ∀ (n : SI), a ≼ₒ{n} b ↔ a' ≼ₒ{n} b') : a ≼ₒ[SI] b ⊣⊢@{PROP} a' ≼ₒ[SI] b' :=
  siPure_mono_bi ⟨fun n => (h n).mp, fun n => (h n).mpr⟩

/-- An internal order that is step-index independent is a pure proposition. -/
theorem internalCmraOrder_pure {a b : A} {φ : Prop} (h : ∀ (n : SI), a ≼ₒ{n} b ↔ φ) :
    a ≼ₒ[SI] b ⊣⊢@{PROP} ⌜φ⌝ :=
  ⟨.trans (siPure_mono (Qi := SiProp.pure φ) fun n => (h n).mp) siPure_pure.mp,
   .trans siPure_pure.mpr (siPure_mono (Pi := SiProp.pure φ) fun n => (h n).mpr)⟩

theorem siPure_internalCmraOrder {a b : A} : <si_pure> (iprop(a ≼ₒ[SI] b) : SiProp SI) ⊣⊢@{PROP} a ≼ₒ[SI] b :=
  persistently_iff.symm.trans persistently_siPure

theorem persistently_internalCmraOrder {a b : A} : <pers> a ≼ₒ[SI] b ⊣⊢@{PROP} a ≼ₒ[SI] b :=
  persistently_siPure

theorem plainly_internalCmraOrder {a b : A} : ■ a ≼ₒ[SI] b ⊣⊢@{PROP} a ≼ₒ[SI] b := plainly_siPure

theorem intuitionistically_internalCmraOrder [BIAffine PROP] {a b : A} :
    □ a ≼ₒ[SI] b ⊣⊢@{PROP} a ≼ₒ[SI] b :=
  intuitionistically_iff_persistently.trans persistently_internalCmraOrder

theorem internalCmraOrder_discrete {a b : A} [ORA.Discrete SI A] :
    a ≼ₒ[SI] b ⊣⊢@{PROP} ⌜a ≼ₒ[SI] b⌝ :=
  internalCmraOrder_pure fun n => (ord_iff_ordN n).symm

theorem internalCmraOrder_refl {a : A} [OrderRefl SI A] : ⊢@{PROP} a ≼ₒ[SI] a :=
  internalCmraOrder_intro (ord_refl a)

theorem internalCmraOrder_trans {a b c : A} : ⊢@{PROP} a ≼ₒ[SI] b -∗ b ≼ₒ[SI] c -∗ a ≼ₒ[SI] c :=
  BI.entails_wand <| BI.wand_intro <| siPure_and_sep.mpr.trans <|
    siPure_mono fun _ h => ordN_trans h.1 h.2

theorem internalCmraOrder_map {B : Type _} [ORA SI B] (g : A -C>[SI] B) {a b : A} :
    a ≼ₒ[SI] b ⊢@{PROP} g a ≼ₒ[SI] g b :=
  siPure_mono fun _ => g.monoN_ord

theorem internalCmraOrder_of_inc [IncOrd SI A] {a b : A} : a ≼[SI] b ⊢@{PROP} a ≼ₒ[SI] b :=
  siPure_mono fun _ h => IncOrd.incN_ordN (inc_holds.mp h)

theorem internalCmraIncluded_of_ord [OrdInc SI A] {a b : A} : a ≼ₒ[SI] b ⊢@{PROP} a ≼[SI] b :=
  siPure_mono fun _ h => inc_holds.mpr (OrdInc.ordN_incN h)

theorem internalCmraIncluded_iff_internalCmraOrder [IncOrd SI A] [OrdInc SI A] {a b : A} : a ≼[SI] b ⊣⊢@{PROP} a ≼ₒ[SI] b :=
  siPure_mono_bi ⟨fun _ hn => incN_iff_ordN.mp (inc_holds.mp hn),
    fun _ hn => inc_holds.mpr (incN_iff_ordN.mpr hn)⟩

instance internalCmraOrder_timeless {a b : A} [ORA.Discrete SI A] :
    Timeless (PROP := PROP) iprop(a ≼ₒ[SI] b) :=
  siPure_timeless _

instance internalCmraOrder_plain {a b : A} : Plain (PROP := PROP) iprop(a ≼ₒ[SI] b) where
  plain := plainly_internalCmraOrder.mpr

instance internalCmraOrder_persistent {a b : A} : Persistent (PROP := PROP) iprop(a ≼ₒ[SI] b) where
  persistent := persistently_internalCmraOrder.mpr

instance internalCmraOrder_absorbing {a b : A} : Absorbing (PROP := PROP) iprop(a ≼ₒ[SI] b) :=
  siPure_absorbing _

end CmraOrder

end Iris
