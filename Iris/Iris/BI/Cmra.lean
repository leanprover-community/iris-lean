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

/-!
# Generic CMRA validity in a BI logic

This file defines the generic internal CMRA validity for any `Sbi PROP`,
as `<si_pure> cmraValid a`.
-/

namespace Iris
open BI OFE SiProp CMRA Sbi

section CmraValid

variable [Sbi PROP] [CMRA A]

@[rocq_alias internal_cmra_valid]
def internalCmraValid (a : A) : PROP := siPure (cmraValid a)

macro_rules
  | `(iprop(✓%$tk $a)) => ``($(wrapIprop tk ``internalCmraValid) $a)

delab_rule internalCmraValid
  | `($_ $a) => ``(iprop(✓ $a))

@[rocq_alias internal_cmra_valid_ne]
instance internalCmraValid_ne : NonExpansive (internalCmraValid (PROP := PROP) (A := A)) where
  ne _ _ _ h := siPure_ne.ne (instNonExpansiveCmraValid.ne h)

#rocq_ignore internal_cmra_valid_proper "Derivable from internalCmraValid_ne with NonExpansive.eqv"

@[rocq_alias internal_cmra_valid_intro]
theorem internalCmraValid_intro {P : PROP} {a : A} (h : ✓ a) :
    P ⊢ ✓ a :=
  calc (P : PROP)
    _ ⊢ True := true_intro
    _ ⊢ <si_pure> True := siPure_pure.mpr
    _ ⊢ ✓ a := siPure_mono (cmraValid_intro h)

@[rocq_alias internal_cmra_valid_elim]
theorem internalCmraValid_elim (a : A) : ✓ a ⊢@{PROP} ⌜✓{0} a⌝ :=
  calc iprop(✓ a)
    _ ⊢ <si_pure> ⌜✓{0} a⌝ := siPure_mono cmraValid_elim
    _ ⊢ ⌜✓{0} a⌝ := siPure_pure.mp

@[rocq_alias internal_cmra_valid_weaken]
theorem internalCmraValid_weaken {a b : A} :
    ✓ (a • b) ⊢@{PROP} ✓ a :=
  siPure_mono cmraValid_weaken

@[rocq_alias internal_cmra_valid_entails]
theorem internalCmraValid_entails [CMRA B] {a : A} {b : B} :
    (✓ a ⊢@{PROP} ✓ b) ↔ ∀ n, ✓{n} a → ✓{n} b :=
  siPure_entails.trans cmraValid_entails_iff

@[rocq_alias si_pure_internal_cmra_valid]
theorem siPure_internalCmraValid {a : A} : <si_pure> cmraValid a ⊣⊢@{PROP} ✓ a :=
  .rfl

@[rocq_alias persistently_internal_cmra_valid]
theorem persistently_internalCmraValid {a : A} :
    <pers> ✓ a ⊣⊢@{PROP} ✓ a :=
  persistently_siPure

@[rocq_alias plainly_internal_cmra_valid]
theorem plainly_internalCmraValid (a : A) :
    ■ ✓ a ⊣⊢@{PROP} ✓ a :=
  plainly_siPure

@[rocq_alias intuitionistically_internal_cmra_valid]
theorem intuitionistically_internalCmraValid [BIAffine PROP] {a : A} :
    □ ✓ a ⊣⊢@{PROP} ✓ a :=
  intuitionistically_iff_persistently.trans persistently_internalCmraValid

@[rocq_alias internal_cmra_valid_discrete]
theorem internalCmraValid_discrete [CMRA.Discrete A] {a : A} :
    ✓ a ⊣⊢@{PROP} ⌜✓ a⌝ :=
  ⟨(internalCmraValid_elim a).trans <| pure_mono (discrete_valid ·),
   pure_elim' internalCmraValid_intro⟩

@[rocq_alias internal_cmra_valid_persistent]
instance internalCmraValid_persistent (a : A) :
    Persistent (PROP := PROP) iprop(✓ a) where
  persistent := persistently_internalCmraValid.mpr

@[rocq_alias internal_cmra_valid_absorbing]
instance internalCmraValid_absorbing (a : A) :
    Absorbing (PROP := PROP) iprop(✓ a) :=
  siPure_absorbing _

@[rocq_alias internal_cmra_valid_plain]
instance internalCmraValid_plain (a : A) :
    Plain (PROP := PROP) iprop(✓ a) where
  plain := plainly_internalCmraValid a |>.mpr

@[rocq_alias internal_cmra_valid_timeless]
instance internalCmraValid_timeless [CMRA.Discrete A] (a : A) :
    Timeless (PROP := PROP) iprop(✓ a) := by
  unfold internalCmraValid; infer_instance

end CmraValid

section CmraIncluded

variable [Sbi PROP] [CMRA A]

/-! ### The internal extension inclusion -/

/-- The internal extension inclusion `∃ c, b ≡ a • c`, the relation frame-based
constructions (views, local updates) are stated with; see `internalCmraIncluded` for the
internal order. -/
@[rocq_alias internal_included]
def internalCmraIncExt (a b : A) : PROP := siPure (∃ c, iprop(b ≡ (a • c)))

macro_rules
  | `(iprop($a ≼ₑ $b)) => ``(internalCmraIncExt $a $b)

delab_rule internalCmraIncExt
  | `($_ $a $b) => ``(iprop($a ≼ₑ $b))

@[rocq_alias internal_included_nonexpansive]
instance internalCmraIncExt_ne :
    NonExpansive₂ (internalCmraIncExt (PROP := PROP) (A := A)) where
  ne n _ _ hx _ _ hy := by
    refine siPure_ne.ne ?_
    apply (exists_ne (fun a => NonExpansive₂.ne hy (op_commN.trans ((op_ne.ne hx).trans op_commN))))

#rocq_ignore internal_included_proper "Derivable from internalCmraIncExt_ne with NonExpansive.eqv"

@[rocq_alias internal_included_intro]
theorem internalCmraIncExt_intro {P : PROP} {a b : A} (h : a ≼ₑ b) :
    P ⊢ a ≼ₑ b := by
  obtain ⟨c, hc⟩ := h
  calc (P : PROP)
    _ ⊢ True := true_intro
    _ ⊢ <si_pure> True := siPure_pure.mpr
    _ ⊢ a ≼ₑ b := siPure_mono (BI.exists_intro_trans c (internalEq.of_equiv hc))

/-- The `SiProp` underlying the internal `≼ₑ` holds at `n` exactly when `a ≼ₑ{n} b`. -/
private theorem incExt_holds {a b : A} {n : Nat} :
    ((∃ c, iprop(b ≡ (a • c))) : SiProp).holds n ↔ a ≼ₑ{n} b := SiProp.exists_holds

/-- Two internal extension inclusions agree when they agree at every step index. -/
theorem internalCmraIncExt_iff [CMRA B] {a b : A} {a' b' : B}
    (h : ∀ n, a ≼ₑ{n} b ↔ a' ≼ₑ{n} b') : a ≼ₑ b ⊣⊢@{PROP} a' ≼ₑ b' :=
  siPure_mono_bi ⟨fun n hn => incExt_holds.mpr ((h n).mp (incExt_holds.mp hn)),
    fun n hn => incExt_holds.mpr ((h n).mpr (incExt_holds.mp hn))⟩

/-- An internal extension inclusion that is step-index independent is a pure proposition. -/
theorem internalCmraIncExt_pure {a b : A} {φ : Prop} (h : ∀ n, a ≼ₑ{n} b ↔ φ) :
    a ≼ₑ b ⊣⊢@{PROP} ⌜φ⌝ :=
  ⟨.trans (siPure_mono fun n hn => (h n).mp (incExt_holds.mp hn)) siPure_pure.mp,
   .trans siPure_pure.mpr (siPure_mono fun n hφ => incExt_holds.mpr ((h n).mpr hφ))⟩

@[rocq_alias si_pure_internal_included]
theorem siPure_internalCmraIncExt {a b : A} :
    <si_pure> a ≼ₑ b ⊣⊢@{PROP} a ≼ₑ b :=
  persistently_iff.symm.trans persistently_siPure

@[rocq_alias persistently_internal_included]
theorem persistently_internalCmraIncExt {a b : A} :
    <pers> a ≼ₑ b ⊣⊢@{PROP} a ≼ₑ b :=
  persistently_siPure

@[rocq_alias plainly_internal_included]
theorem plainly_internalCmraIncExt {a b : A} :
    ■ a ≼ₑ b ⊣⊢@{PROP} a ≼ₑ b :=
  plainly_siPure

@[rocq_alias intuitionistically_internal_included]
theorem intuitionistically_internalCmraIncExt [BIAffine PROP] {a b : A} :
    □ a ≼ₑ b ⊣⊢@{PROP} a ≼ₑ b :=
  intuitionistically_iff_persistently.trans persistently_internalCmraIncExt

@[rocq_alias internal_included_discrete]
theorem internalCmraIncExt_discrete {a b : A} [CMRA.Discrete A] :
    a ≼ₑ b ⊣⊢@{PROP} ⌜a ≼ₑ b⌝ := by
  haveI : ∀ x : A, DiscreteE x := fun x => ⟨OFE.Discrete.discrete⟩
  refine ⟨?_, pure_elim' internalCmraIncExt_intro⟩
  calc internalCmraIncExt a b
    _ ⊢ <si_pure> (∃ c, b ≡ (a • c)) := siPure_internalCmraIncExt.mp
    _ ⊢ <si_pure> (∃ c, ⌜b = a • c⌝) := siPure_mono <| exists_mono fun _ => discrete_eq_mp
    _ ⊢ <si_pure> ⌜∃ c, b = a • c⌝ := siPure_mono pure_exists.mp
    _ ⊢ ⌜∃ c, b = a • c⌝ := siPure_pure.mp
    _ ⊢ ⌜a ≼ₑ b⌝ := pure_mono fun ⟨c, h⟩ => ⟨c, h⟩

@[rocq_alias internal_included_refl]
theorem internalCmraIncExt_refl {a : A} [IsTotal A] : ⊢@{PROP} a ≼ₑ a :=
  internalCmraIncExt_intro .rfl

@[rocq_alias internal_included_trans]
theorem internalCmraIncExt_trans {a b c : A} :
    ⊢@{PROP} a ≼ₑ b -∗ b ≼ₑ c -∗ a ≼ₑ c := by
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

/-- The internal `≼ₑ` is monotone under any nonexpansive map commuting with `•`. -/
theorem internalCmraIncExt_map {B : Type _} [CMRA B] (g : A → B) [NonExpansive g]
    (hg : ∀ x y : A, g (x • y) = g x • g y) {a b : A} :
    a ≼ₑ b ⊢@{PROP} g a ≼ₑ g b :=
  siPure_mono <| BI.exists_elim fun c => BI.exists_intro_trans (g c) <| by
    rw [← hg]; exact internalEq.of_internalEquiv_ne g

@[rocq_alias internal_included_timeless]
instance internalCmraIncExt_timeless {a b : A} [CMRA.Discrete A] :
    Timeless (PROP := PROP) iprop(a ≼ₑ b) := by
  haveI : ∀ x : A, DiscreteE x := fun x => ⟨OFE.Discrete.discrete⟩
  unfold internalCmraIncExt
  infer_instance

@[rocq_alias internal_included_plain]
instance internalCmraIncExt_plain {a b : A} :
    Plain (PROP := PROP) iprop(a ≼ₑ b) where
  plain := plainly_internalCmraIncExt.mpr

@[rocq_alias internal_included_persistent]
instance internalCmraIncExt_persistent {a b : A} :
    Persistent (PROP := PROP) iprop(a ≼ₑ b) where
  persistent := persistently_internalCmraIncExt.mpr

@[rocq_alias internal_included_absorbing]
instance internalCmraIncExt_absorbing {a b : A} :
    Absorbing (PROP := PROP) iprop(a ≼ₑ b) :=
  siPure_absorbing _

/-! ### The internal order -/

/-- The step-indexed order as a step-indexed proposition. -/
def _root_.SiProp.cmraIncluded (a b : A) : SiProp where
  holds n := a ≼{n} b
  closed h hle := h.le hle

instance _root_.SiProp.cmraIncluded_timeless [CMRA.Discrete A] {a b : A} :
    Timeless (SiProp.cmraIncluded a b) where
  timeless := fun n h => by
    cases n with
    | zero => left; trivial
    | succ n => right; exact incN_of_inc _ (CMRA.discrete_inc (inc0_of_incN h))

/-- The internal order `a ≼ b`, holding at step index `n` when `a ≼{n} b`; ownership is
monotone along it (`ownM_mono`). -/
def internalCmraIncluded (a b : A) : PROP := siPure (SiProp.cmraIncluded a b)

macro_rules
  | `(iprop($a ≼ $b)) => ``(internalCmraIncluded $a $b)

delab_rule internalCmraIncluded
  | `($_ $a $b) => ``(iprop($a ≼ $b))

instance internalCmraIncluded_ne :
    NonExpansive₂ (internalCmraIncluded (PROP := PROP) (A := A)) where
  ne _ _ _ hx _ _ hy := siPure_ne.ne fun hm => incN_dist_iff (hx.le hm) (hy.le hm)

theorem internalCmraIncluded_intro {P : PROP} {a b : A} (h : a ≼ b) : P ⊢ a ≼ b :=
  calc (P : PROP)
    _ ⊢ True := true_intro
    _ ⊢ <si_pure> True := siPure_pure.mpr
    _ ⊢ a ≼ b := siPure_mono fun n _ => incN_of_inc n h

/-- Two internal orders agree when they agree at every step index. -/
theorem internalCmraIncluded_iff [CMRA B] {a b : A} {a' b' : B}
    (h : ∀ n, a ≼{n} b ↔ a' ≼{n} b') : a ≼ b ⊣⊢@{PROP} a' ≼ b' :=
  siPure_mono_bi ⟨fun n => (h n).mp, fun n => (h n).mpr⟩

/-- An internal order that is step-index independent is a pure proposition. -/
theorem internalCmraIncluded_pure {a b : A} {φ : Prop} (h : ∀ n, a ≼{n} b ↔ φ) :
    a ≼ b ⊣⊢@{PROP} ⌜φ⌝ :=
  ⟨.trans (siPure_mono (Qi := SiProp.pure φ) fun n => (h n).mp) siPure_pure.mp,
   .trans siPure_pure.mpr (siPure_mono (Pi := SiProp.pure φ) fun n => (h n).mpr)⟩

theorem siPure_internalCmraIncluded {a b : A} : <si_pure> a ≼ b ⊣⊢@{PROP} a ≼ b :=
  persistently_iff.symm.trans persistently_siPure

theorem persistently_internalCmraIncluded {a b : A} : <pers> a ≼ b ⊣⊢@{PROP} a ≼ b :=
  persistently_siPure

theorem plainly_internalCmraIncluded {a b : A} : ■ a ≼ b ⊣⊢@{PROP} a ≼ b :=
  plainly_siPure

theorem intuitionistically_internalCmraIncluded [BIAffine PROP] {a b : A} :
    □ a ≼ b ⊣⊢@{PROP} a ≼ b :=
  intuitionistically_iff_persistently.trans persistently_internalCmraIncluded

theorem internalCmraIncluded_discrete {a b : A} [CMRA.Discrete A] :
    a ≼ b ⊣⊢@{PROP} ⌜a ≼ b⌝ :=
  internalCmraIncluded_pure fun n => (inc_iff_incN n).symm

theorem internalCmraIncluded_refl {a : A} [IncRefl A] : ⊢@{PROP} a ≼ a :=
  internalCmraIncluded_intro (inc_refl a)

theorem internalCmraIncluded_trans {a b c : A} : ⊢@{PROP} a ≼ b -∗ b ≼ c -∗ a ≼ c :=
  BI.entails_wand <| BI.wand_intro <| siPure_and_sep.mpr.trans <|
    siPure_mono fun _ h => incN_trans h.1 h.2

/-- The internal order is monotone under morphisms. -/
theorem internalCmraIncluded_map {B : Type _} [CMRA B] (g : A -C> B) {a b : A} :
    a ≼ b ⊢@{PROP} g a ≼ g b :=
  siPure_mono fun _ => g.monoN

/-- In an affine algebra the internal extension inclusion implies the internal order. -/
theorem internalCmraIncluded_of_incExt [Affine A] {a b : A} : a ≼ₑ b ⊢@{PROP} a ≼ b :=
  siPure_mono fun _ h => incN_of_incExtN (incExt_holds.mp h)

instance internalCmraIncluded_timeless {a b : A} [CMRA.Discrete A] :
    Timeless (PROP := PROP) iprop(a ≼ b) := by
  unfold internalCmraIncluded
  infer_instance

instance internalCmraIncluded_plain {a b : A} : Plain (PROP := PROP) iprop(a ≼ b) where
  plain := plainly_internalCmraIncluded.mpr

instance internalCmraIncluded_persistent {a b : A} : Persistent (PROP := PROP) iprop(a ≼ b) where
  persistent := persistently_internalCmraIncluded.mpr

instance internalCmraIncluded_absorbing {a b : A} : Absorbing (PROP := PROP) iprop(a ≼ b) :=
  siPure_absorbing _

end CmraIncluded

end Iris
