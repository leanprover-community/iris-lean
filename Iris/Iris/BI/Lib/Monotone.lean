/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/
module

public import Iris.ProofMode

/-! # Monotone predicate transformers

A *curried predicate* is a `PROP`, or a (dependent) function into curried predicates. `wandAll Φ Ψ`
is the pointwise wand `∀ x⃗, Φ x⃗ -∗ Ψ x⃗`.

`MonoFn G` says that `G` is monotone in the internal sense, `□ wandAll Φ Ψ ⊢ wandAll (G Φ) (G Ψ)`,
which is what Iris (co)induction needs. The instances below prove it for bodies built from the
usual connectives, for any number of curried arguments, by typeclass search. -/

@[expose] public section

open Iris BI Iris.Std

namespace Iris

/-- Curried BI predicates: `PROP`, and (dependent) functions into curried predicates. -/
class BIPred (τ : Type _) (PROP : outParam (Type _)) [BI PROP] where
  /-- The pointwise wand `∀ x⃗, f x⃗ -∗ g x⃗`. -/
  wandAll : τ → τ → PROP
  wandAll_refl {f : τ} : ⊢ wandAll f f
  /-- Composition, with a persistent second wand. -/
  wandAll_comp {f g h : τ} : wandAll f g ∗ □ wandAll g h ⊢ wandAll f h

open BIPred

section BIPred
variable [BI PROP]

instance : BIPred PROP PROP where
  wandAll P Q := iprop(P -∗ Q)
  wandAll_refl := by intro _; iintro H; iexact H
  wandAll_comp := by
    intro _ _ _
    iintro ⟨H1, #H2⟩ HP
    iapply H2
    iapply H1 $$ HP

instance {α : Type _} {β : α → Type _} [∀ a, BIPred (β a) PROP] :
    BIPred ((a : α) → β a) PROP where
  wandAll f g := iprop(∀ a, wandAll (f a) (g a))
  wandAll_refl := by
    intro _
    iintro %a
    iapply wandAll_refl
  wandAll_comp := by
    intro _ _ _
    iintro ⟨H1, #H2⟩ %a
    iapply wandAll_comp
    isplitl [H1]
    · iapply H1
    · iintro !>
      iapply H2

end BIPred

/-- `G` is monotone: `□ wandAll Φ Ψ ⊢ wandAll (G Φ) (G Ψ)`. -/
class MonoFn [BI PROP] [BIPred σ PROP] [BIPred τ PROP] (G : σ → τ) : Prop where
  mono {Φ Ψ : σ} : ⊢ □ wandAll Φ Ψ -∗ wandAll (G Φ) (G Ψ)

/-- `G` is antitone: `□ wandAll Φ Ψ ⊢ wandAll (G Ψ) (G Φ)`. -/
class AntiFn [BI PROP] [BIPred σ PROP] [BIPred τ PROP] (G : σ → τ) : Prop where
  anti {Φ Ψ : σ} : ⊢ □ wandAll Φ Ψ -∗ wandAll (G Ψ) (G Φ)

namespace MonoFn
variable [BI PROP] [BIPred σ PROP]

/-- `mono` for a `PROP`-valued `G`, with the wand visible to the proof mode. -/
theorem prop {G : σ → PROP} [MonoFn G] {Φ Ψ : σ} : ⊢ □ wandAll Φ Ψ -∗ G Φ -∗ G Ψ :=
  MonoFn.mono (G := G)

theorem of_prop {G : σ → PROP} (h : ∀ Φ Ψ, ⊢ □ wandAll Φ Ψ -∗ G Φ -∗ G Ψ) : MonoFn G := ⟨h _ _⟩

/-- A function-valued `G` is monotone if it is monotone at each argument. -/
theorem of_forall {α : Type _} {β : α → Type _} [∀ a, BIPred (β a) PROP] {G : σ → (a : α) → β a}
    (h : ∀ a, MonoFn (fun Φ => G Φ a)) : MonoFn G where
  mono {Φ Ψ} := by
    change ⊢ □ wandAll Φ Ψ -∗ ∀ a, wandAll (G Φ a) (G Ψ a)
    iintro #H %a
    iapply (h a).mono $$ H

end MonoFn

namespace AntiFn
variable [BI PROP] [BIPred σ PROP]

theorem prop {G : σ → PROP} [AntiFn G] {Φ Ψ : σ} : ⊢ □ wandAll Φ Ψ -∗ G Ψ -∗ G Φ :=
  AntiFn.anti (G := G)

theorem of_prop {G : σ → PROP} (h : ∀ Φ Ψ, ⊢ □ wandAll Φ Ψ -∗ G Ψ -∗ G Φ) : AntiFn G := ⟨h _ _⟩

theorem of_forall {α : Type _} {β : α → Type _} [∀ a, BIPred (β a) PROP] {G : σ → (a : α) → β a}
    (h : ∀ a, AntiFn (fun Φ => G Φ a)) : AntiFn G where
  anti {Φ Ψ} := by
    change ⊢ □ wandAll Φ Ψ -∗ ∀ a, wandAll (G Ψ a) (G Φ a)
    iintro #H %a
    iapply (h a).anti $$ H

end AntiFn

namespace MonoInstances
variable [BI PROP] [BIPred σ PROP]

/-! ## Structure: identity, constants, functions and applications -/

instance mono_id : MonoFn (fun Φ : σ => Φ) where
  mono := by intro _ _; iintro #H; iexact H

instance mono_const [BIPred τ PROP] (c : τ) : MonoFn (fun _ : σ => c) where
  mono := by intro _ _; iintro _; iapply wandAll_refl

instance anti_const [BIPred τ PROP] (c : τ) : AntiFn (fun _ : σ => c) where
  anti := by intro _ _; iintro _; iapply wandAll_refl

instance mono_forall {α : Type _} {β : α → Type _} [∀ a, BIPred (β a) PROP]
    (G : σ → (a : α) → β a) [h : ∀ a, MonoFn (fun Φ => G Φ a)] : MonoFn G :=
  MonoFn.of_forall h

instance anti_forall {α : Type _} {β : α → Type _} [∀ a, BIPred (β a) PROP]
    (G : σ → (a : α) → β a) [h : ∀ a, AntiFn (fun Φ => G Φ a)] : AntiFn G :=
  AntiFn.of_forall h

instance (priority := low) mono_app {α : Type _} {β : α → Type _} [∀ a, BIPred (β a) PROP]
    (G : σ → (a : α) → β a) (a : α) [h : MonoFn G] : MonoFn (fun Φ => G Φ a) where
  mono {Φ Ψ} := by
    have h' : ⊢ □ wandAll Φ Ψ -∗ ∀ a, wandAll (G Φ a) (G Ψ a) := h.mono
    iintro #H
    ihave H' := h' $$ H
    iapply H'

instance (priority := low) anti_app {α : Type _} {β : α → Type _} [∀ a, BIPred (β a) PROP]
    (G : σ → (a : α) → β a) (a : α) [h : AntiFn G] : AntiFn (fun Φ => G Φ a) where
  anti {Φ Ψ} := by
    have h' : ⊢ □ wandAll Φ Ψ -∗ ∀ a, wandAll (G Ψ a) (G Φ a) := h.anti
    iintro #H
    ihave H' := h' $$ H
    iapply H'

/-! ## Connectives -/

instance mono_and (F G : σ → PROP) [MonoFn F] [MonoFn G] :
    MonoFn (fun Φ => iprop(F Φ ∧ G Φ)) := .of_prop fun _ _ => by
  iintro #H HFG
  isplit
  · iapply MonoFn.prop (G := F) $$ H; icases HFG with ⟨HF, -⟩; iexact HF
  · iapply MonoFn.prop (G := G) $$ H; icases HFG with ⟨-, HG⟩; iexact HG

instance anti_and (F G : σ → PROP) [AntiFn F] [AntiFn G] :
    AntiFn (fun Φ => iprop(F Φ ∧ G Φ)) := .of_prop fun _ _ => by
  iintro #H HFG
  isplit
  · iapply AntiFn.prop (G := F) $$ H; icases HFG with ⟨HF, -⟩; iexact HF
  · iapply AntiFn.prop (G := G) $$ H; icases HFG with ⟨-, HG⟩; iexact HG

instance mono_or (F G : σ → PROP) [MonoFn F] [MonoFn G] :
    MonoFn (fun Φ => iprop(F Φ ∨ G Φ)) := .of_prop fun _ _ => by
  iintro #H (HF | HG)
  · ileft; iapply MonoFn.prop (G := F) $$ H HF
  · iright; iapply MonoFn.prop (G := G) $$ H HG

instance anti_or (F G : σ → PROP) [AntiFn F] [AntiFn G] :
    AntiFn (fun Φ => iprop(F Φ ∨ G Φ)) := .of_prop fun _ _ => by
  iintro #H (HF | HG)
  · ileft; iapply AntiFn.prop (G := F) $$ H HF
  · iright; iapply AntiFn.prop (G := G) $$ H HG

instance mono_sep (F G : σ → PROP) [MonoFn F] [MonoFn G] :
    MonoFn (fun Φ => iprop(F Φ ∗ G Φ)) := .of_prop fun _ _ => by
  iintro #H ⟨HF, HG⟩
  isplitl [HF]
  · iapply MonoFn.prop (G := F) $$ H HF
  · iapply MonoFn.prop (G := G) $$ H HG

instance anti_sep (F G : σ → PROP) [AntiFn F] [AntiFn G] :
    AntiFn (fun Φ => iprop(F Φ ∗ G Φ)) := .of_prop fun _ _ => by
  iintro #H ⟨HF, HG⟩
  isplitl [HF]
  · iapply AntiFn.prop (G := F) $$ H HF
  · iapply AntiFn.prop (G := G) $$ H HG

instance mono_wand (F G : σ → PROP) [AntiFn F] [MonoFn G] :
    MonoFn (fun Φ => iprop(F Φ -∗ G Φ)) := .of_prop fun _ _ => by
  iintro #H HFG HF
  ihave HF' := AntiFn.prop (G := F) $$ H HF
  iapply MonoFn.prop (G := G) $$ H (HFG $$ HF')

instance anti_wand (F G : σ → PROP) [MonoFn F] [AntiFn G] :
    AntiFn (fun Φ => iprop(F Φ -∗ G Φ)) := .of_prop fun _ _ => by
  iintro #H HFG HF
  ihave HF' := MonoFn.prop (G := F) $$ H HF
  iapply AntiFn.prop (G := G) $$ H (HFG $$ HF')

instance mono_pers_imp (F G : σ → PROP) [AntiFn F] [MonoFn G] :
    MonoFn (fun Φ => iprop(<pers> F Φ → G Φ)) := .of_prop fun _ _ => by
  iintro #H HFG #HF
  ihave #HF' := AntiFn.prop (G := F) $$ H HF
  iapply MonoFn.prop (G := G) $$ H (HFG $$ HF')

instance anti_pers_imp (F G : σ → PROP) [MonoFn F] [AntiFn G] :
    AntiFn (fun Φ => iprop(<pers> F Φ → G Φ)) := .of_prop fun _ _ => by
  iintro #H HFG #HF
  ihave #HF' := MonoFn.prop (G := F) $$ H HF
  iapply AntiFn.prop (G := G) $$ H (HFG $$ HF')

instance mono_bi_forall {B : Sort _} (F : B → σ → PROP) [∀ y, MonoFn (F y)] :
    MonoFn (fun Φ => BI.forall (fun y => F y Φ)) := .of_prop fun _ _ => by
  iintro #H HF %y
  iapply MonoFn.prop (G := F y) $$ H HF

instance anti_bi_forall {B : Sort _} (F : B → σ → PROP) [∀ y, AntiFn (F y)] :
    AntiFn (fun Φ => BI.forall (fun y => F y Φ)) := .of_prop fun _ _ => by
  iintro #H HF %y
  iapply AntiFn.prop (G := F y) $$ H HF

instance mono_bi_exists {B : Sort _} (F : B → σ → PROP) [∀ y, MonoFn (F y)] :
    MonoFn (fun Φ => BI.exists (fun y => F y Φ)) := .of_prop fun _ _ => by
  iintro #H ⟨%y, HF⟩
  iexists y
  iapply MonoFn.prop (G := F y) $$ H HF

instance anti_bi_exists {B : Sort _} (F : B → σ → PROP) [∀ y, AntiFn (F y)] :
    AntiFn (fun Φ => BI.exists (fun y => F y Φ)) := .of_prop fun _ _ => by
  iintro #H ⟨%y, HF⟩
  iexists y
  iapply AntiFn.prop (G := F y) $$ H HF

/-! ## Modalities -/

instance mono_persistently (F : σ → PROP) [MonoFn F] :
    MonoFn (fun Φ => iprop(<pers> F Φ)) := .of_prop fun _ _ => by
  iintro #H #HF !>
  iapply MonoFn.prop (G := F) $$ H HF

instance anti_persistently (F : σ → PROP) [AntiFn F] :
    AntiFn (fun Φ => iprop(<pers> F Φ)) := .of_prop fun _ _ => by
  iintro #H #HF !>
  iapply AntiFn.prop (G := F) $$ H HF

instance mono_affinely (F : σ → PROP) [MonoFn F] :
    MonoFn (fun Φ => iprop(<affine> F Φ)) := .of_prop fun _ _ => by
  iintro #H HF !>
  iapply MonoFn.prop (G := F) $$ H HF

instance anti_affinely (F : σ → PROP) [AntiFn F] :
    AntiFn (fun Φ => iprop(<affine> F Φ)) := .of_prop fun _ _ => by
  iintro #H HF !>
  iapply AntiFn.prop (G := F) $$ H HF

instance mono_absorbingly (F : σ → PROP) [MonoFn F] :
    MonoFn (fun Φ => iprop(<absorb> F Φ)) := .of_prop fun _ _ => by
  iintro #H >HF !>
  iapply MonoFn.prop (G := F) $$ H HF

instance anti_absorbingly (F : σ → PROP) [AntiFn F] :
    AntiFn (fun Φ => iprop(<absorb> F Φ)) := .of_prop fun _ _ => by
  iintro #H >HF !>
  iapply AntiFn.prop (G := F) $$ H HF

instance mono_intuitionistically (F : σ → PROP) [MonoFn F] :
    MonoFn (fun Φ => iprop(□ F Φ)) := .of_prop fun _ _ => by
  iintro #H #HF !>
  iapply MonoFn.prop (G := F) $$ H HF

instance anti_intuitionistically (F : σ → PROP) [AntiFn F] :
    AntiFn (fun Φ => iprop(□ F Φ)) := .of_prop fun _ _ => by
  iintro #H #HF !>
  iapply AntiFn.prop (G := F) $$ H HF

instance mono_later (F : σ → PROP) [MonoFn F] :
    MonoFn (fun Φ => iprop(▷ F Φ)) := .of_prop fun _ _ => by
  iintro #H HF !>
  iapply MonoFn.prop (G := F) $$ H HF

instance anti_later (F : σ → PROP) [AntiFn F] :
    AntiFn (fun Φ => iprop(▷ F Φ)) := .of_prop fun _ _ => by
  iintro #H HF !>
  iapply AntiFn.prop (G := F) $$ H HF

instance mono_except0 (F : σ → PROP) [MonoFn F] :
    MonoFn (fun Φ => iprop(◇ F Φ)) := .of_prop fun _ _ => by
  iintro #H >HF !>
  iapply MonoFn.prop (G := F) $$ H HF

instance anti_except0 (F : σ → PROP) [AntiFn F] :
    AntiFn (fun Φ => iprop(◇ F Φ)) := .of_prop fun _ _ => by
  iintro #H >HF !>
  iapply AntiFn.prop (G := F) $$ H HF

instance mono_fupd [BIFUpdate PROP] (E1 E2 : CoPset) (F : σ → PROP) [MonoFn F] :
    MonoFn (fun Φ => fupd E1 E2 (F Φ)) := .of_prop fun _ _ => by
  iintro #H >HF !>
  iapply MonoFn.prop (G := F) $$ H HF

instance anti_fupd [BIFUpdate PROP] (E1 E2 : CoPset) (F : σ → PROP) [AntiFn F] :
    AntiFn (fun Φ => fupd E1 E2 (F Φ)) := .of_prop fun _ _ => by
  iintro #H >HF !>
  iapply AntiFn.prop (G := F) $$ H HF

instance mono_bupd [BIUpdate PROP] (F : σ → PROP) [MonoFn F] :
    MonoFn (fun Φ => iprop(|==> F Φ)) := .of_prop fun _ _ => by
  iintro #H >HF !>
  iapply MonoFn.prop (G := F) $$ H HF

instance anti_bupd [BIUpdate PROP] (F : σ → PROP) [AntiFn F] :
    AntiFn (fun Φ => iprop(|==> F Φ)) := .of_prop fun _ _ => by
  iintro #H >HF !>
  iapply AntiFn.prop (G := F) $$ H HF

/-! ## Big operators -/

instance mono_bigSepL (l : List B) (F : Nat → B → σ → PROP) [∀ n y, MonoFn (F n y)] :
    MonoFn (fun Φ => bigSepL (fun n y => F n y Φ) l) := .of_prop fun _ _ => by
  iintro #H HF
  iapply BigSepL.bigSepL_impl $$ HF
  iintro !> %k %y _ HG
  iapply MonoFn.prop (G := F k y) $$ H HG

instance anti_bigSepL (l : List B) (F : Nat → B → σ → PROP) [∀ n y, AntiFn (F n y)] :
    AntiFn (fun Φ => bigSepL (fun n y => F n y Φ) l) := .of_prop fun _ _ => by
  iintro #H HF
  iapply BigSepL.bigSepL_impl $$ HF
  iintro !> %k %y _ HG
  iapply AntiFn.prop (G := F k y) $$ H HG

instance mono_bigSepL2 (l1 : List B) (l2 : List C) (F : Nat → B → C → σ → PROP)
    [∀ n y z, MonoFn (F n y z)] :
    MonoFn (fun Φ => bigSepL2 (fun n y z => F n y z Φ) l1 l2) := .of_prop fun _ _ => by
  iintro #H HF
  iapply BigSepL2.bigSepL2_impl $$ HF
  iintro !> %k %y %z _ _ HG
  iapply MonoFn.prop (G := F k y z) $$ H HG

instance anti_bigSepL2 (l1 : List B) (l2 : List C) (F : Nat → B → C → σ → PROP)
    [∀ n y z, AntiFn (F n y z)] :
    AntiFn (fun Φ => bigSepL2 (fun n y z => F n y z Φ) l1 l2) := .of_prop fun _ _ => by
  iintro #H HF
  iapply BigSepL2.bigSepL2_impl $$ HF
  iintro !> %k %y %z _ _ HG
  iapply AntiFn.prop (G := F k y z) $$ H HG

instance mono_bigSepM [LawfulFiniteMap M K] (m : M V) (F : K → V → σ → PROP)
    [∀ k v, MonoFn (F k v)] : MonoFn (fun Φ => bigSepM (fun k v => F k v Φ) m) :=
  .of_prop fun _ _ => by
  iintro #H HF
  iapply BigSepM.bigSepM_impl $$ HF
  iintro !> %k %v _ HG
  iapply MonoFn.prop (G := F k v) $$ H HG

instance anti_bigSepM [LawfulFiniteMap M K] (m : M V) (F : K → V → σ → PROP)
    [∀ k v, AntiFn (F k v)] : AntiFn (fun Φ => bigSepM (fun k v => F k v Φ) m) :=
  .of_prop fun _ _ => by
  iintro #H HF
  iapply BigSepM.bigSepM_impl $$ HF
  iintro !> %k %v _ HG
  iapply AntiFn.prop (G := F k v) $$ H HG

instance mono_bigSepS [LawfulFiniteSet S B] (X : S) (F : B → σ → PROP) [∀ y, MonoFn (F y)] :
    MonoFn (fun Φ => bigSepS (fun y => F y Φ) X) := .of_prop fun _ _ => by
  iintro #H HF
  iapply BigSepS.bigSepS_impl $$ HF
  iintro !> %y _ HG
  iapply MonoFn.prop (G := F y) $$ H HG

instance anti_bigSepS [LawfulFiniteSet S B] (X : S) (F : B → σ → PROP) [∀ y, AntiFn (F y)] :
    AntiFn (fun Φ => bigSepS (fun y => F y Φ) X) := .of_prop fun _ _ => by
  iintro #H HF
  iapply BigSepS.bigSepS_impl $$ HF
  iintro !> %y _ HG
  iapply AntiFn.prop (G := F y) $$ H HG

instance mono_bigSepMS [LawfulFiniteMultiSet MS B] (X : MS) (F : B → σ → PROP)
    [∀ y, MonoFn (F y)] : MonoFn (fun Φ => bigSepMS (fun y => F y Φ) X) :=
  .of_prop fun _ _ => by
  iintro #H HF
  iapply BigSepMS.bigSepMS_impl $$ HF
  iintro !> %y _ HG
  iapply MonoFn.prop (G := F y) $$ H HG

instance anti_bigSepMS [LawfulFiniteMultiSet MS B] (X : MS) (F : B → σ → PROP)
    [∀ y, AntiFn (F y)] : AntiFn (fun Φ => bigSepMS (fun y => F y Φ) X) :=
  .of_prop fun _ _ => by
  iintro #H HF
  iapply BigSepMS.bigSepMS_impl $$ HF
  iintro !> %y _ HG
  iapply AntiFn.prop (G := F y) $$ H HG

end MonoInstances

end Iris
