/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Iris.BI.Classes
import Iris.BI.BI
import Iris.BI.DerivedLaws
import Iris.BI.DerivedLawsLater
import Iris.BI.Extensions
import Iris.Algebra.Excl
import Iris.Std.RocqAlias
import Iris.Std.TC

namespace Iris
open BI OFE Iris.Std

universe u

/-- Internal equality: compares `a, b : A` for `A : OFE` inside a BI logic. -/
class InternalEq (PROP : Type _) where
  internalEq : {A : Type u} → [OFE A] → A → A → PROP

export InternalEq (internalEq)

/-- The `BIInternalEq` class axiomatizes internal equality for a BI logic. -/
class BIInternalEq (PROP : Type _) [BI PROP] extends InternalEq PROP where
  [ne (A : Type u) [OFE A] : NonExpansive₂ (internalEq (A := A))]
  refl {A : Type u} [OFE A] (P : PROP) (a : A) :
    P ⊢ internalEq a a
  rewrite {A : Type u} [OFE A] (a b : A) (Ψ : A → PROP) [NonExpansive Ψ] :
    internalEq a b ⊢ Ψ a → Ψ b
  discrete_eq_1 {A : Type u} [OFE A] (a b : A) [TCOr (DiscreteE a) (DiscreteE b)] :
    internalEq a b ⊢ ⌜a ≡ b⌝
  sig_equivI_1 {A : Type u} [OFE A] (P : A → Prop) (x y : Subtype P) :
    internalEq x.val y.val ⊢ internalEq x y
  fun_extI {A : Type u} {B : A → Type u} [OFEFun B] (f g : (x : A) → B x) :
    (∀ x, internalEq (f x) (g x)) ⊢ internalEq f g
  later_equivI_1 {A : Type u} [OFE A] (x y : A) :
    internalEq (Later.next x) (Later.next y) ⊢ ▷ internalEq x y
  later_equivI_2 {A : Type u} [OFE A] (x y : A) :
    ▷ internalEq x y ⊢ internalEq (Later.next x) (Later.next y)
  absorbingly_internalEq {A : Type u} [OFE A] (x y : A) :
    <absorb> internalEq x y ⊣⊢ internalEq x y
  persistently_internalEq {A : Type u} [OFE A] (a b : A) :
    <pers> internalEq a b ⊣⊢ internalEq a b
  soundness {A : Type u} [OFE A] (x y : A) :
    (⊢ internalEq x y) → x ≡ y
  entails {A B : Type u} [OFE A] [OFE B] (a₁ a₂ : A) (b₁ b₂ : B) :
    Iff (internalEq a₁ a₂ ⊢ internalEq b₁ b₂) (∀ n, a₁ ≡{n}≡ a₂ → b₁ ≡{n}≡ b₂)
  later_equivI_prop_2 (P Q : PROP) :
    ▷ internalEq P Q ⊢ internalEq (BIBase.later P) (BIBase.later Q)

attribute [instance] BIInternalEq.ne

namespace BI

section InternalEqLaws

variable [BI PROP] [BIInternalEq PROP] {P Q : PROP}

@[rocq_alias internal_eq_refl]
theorem internalEq_refl {A : Type u} [OFE A] (P : PROP) (a : A) :
    P ⊢ internalEq a a :=
  BIInternalEq.refl P a

@[rocq_alias equiv_internal_eq]
theorem equiv_internalEq {A : Type u} [OFE A] (P : PROP) (a b : A) (h : a ≡ b) :
    P ⊢ internalEq a b :=
  (internalEq_refl P a).trans (equiv_iff.mp (NonExpansive₂.eqv Equiv.rfl h)).1

@[rocq_alias pure_internal_eq]
theorem pure_internalEq {A : Type u} [OFE A] (x y : A) :
    ⌜x ≡ y⌝ ⊢ internalEq (PROP := PROP) x y :=
  pure_elim' fun h => equiv_internalEq _ _ _ h

@[rocq_alias internal_eq_rewrite]
theorem internalEq_rewrite {A : Type u} [OFE A] (a b : A) (Ψ : A → PROP) [NonExpansive Ψ] :
    internalEq a b ⊢ Ψ a → Ψ b :=
  BIInternalEq.rewrite a b Ψ

@[rocq_alias internal_eq_rewrite']
theorem internalEq_rewrite' {A : Type u} [OFE A] (a b : A) (Ψ : A → PROP) [NonExpansive Ψ]
    (Heq : P ⊢ internalEq a b) (HΨa : P ⊢ Ψ a) : P ⊢ Ψ b :=
  (and_intro .rfl HΨa).trans <| (and_mono_l Heq).trans <| imp_elim (internalEq_rewrite a b Ψ)

@[rocq_alias internal_eq_sym]
theorem internalEq_sym {A : Type u} [OFE A] (a b : A) :
    internalEq a b ⊢@{PROP} internalEq b a :=
  @internalEq_rewrite' _ _ _ _ _ _ a b (fun b => internalEq b a)
    ⟨fun {_ _ _} h => NonExpansive₂.ne h Dist.rfl⟩ .rfl (internalEq_refl _ _)

@[rocq_alias internal_eq_trans]
theorem internalEq_trans {A : Type u} [OFE A] (a b c : A) :
    internalEq a b ∧ internalEq b c ⊢@{PROP} internalEq a c :=
  @internalEq_rewrite' _ _ _ _ _ _ b a (fun b => internalEq b c)
    ⟨fun {_ _ _} h => NonExpansive₂.ne h Dist.rfl⟩
    (and_elim_l.trans (internalEq_sym a b)) and_elim_r

@[rocq_alias f_equivI]
theorem f_equivI {A B : Type u} [OFE A] [OFE B] (f : A → B) [hf : NonExpansive f] (x y : A) :
    internalEq x y ⊢@{PROP} internalEq (f x) (f y) :=
  @internalEq_rewrite' _ _ _ _ _ _ x y (fun y => internalEq (f x) (f y))
    ⟨fun {_ _ _} h => NonExpansive₂.ne Dist.rfl (hf.ne h)⟩ .rfl (internalEq_refl _ _)

/-! ## Equality of data types -/

@[rocq_alias discrete_eq_1]
theorem discrete_eq_1 {A : Type u} [OFE A] (a b : A) [TCOr (DiscreteE a) (DiscreteE b)] :
    internalEq a b ⊢@{PROP} ⌜a ≡ b⌝ :=
  BIInternalEq.discrete_eq_1 a b

@[rocq_alias discrete_eq]
theorem discrete_eq {A : Type u} [OFE A] (a b : A) [TCOr (DiscreteE a) (DiscreteE b)] :
    internalEq a b ⊣⊢@{PROP} ⌜a ≡ b⌝ :=
  ⟨discrete_eq_1 a b, pure_internalEq a b⟩

@[rocq_alias sig_equivI_1]
theorem sig_equivI_1 {A : Type u} [OFE A] (P : A → Prop) (x y : Subtype P) :
    internalEq x.val y.val ⊢@{PROP} internalEq x y :=
  BIInternalEq.sig_equivI_1 P x y

@[rocq_alias fun_extI]
theorem fun_extI {A : Type u} {B : A → Type u} [OFEFun B] (f g : (x : A) → B x) :
    (∀ x, internalEq (f x) (g x)) ⊢ internalEq (PROP := PROP) f g :=
  BIInternalEq.fun_extI f g

@[rocq_alias prod_equivI]
theorem prod_equivI {A B : Type u} [OFE A] [OFE B] (x y : A × B) :
    internalEq x y ⊣⊢@{PROP} internalEq x.1 y.1 ∧ internalEq x.2 y.2 := by
  constructor
  · exact and_intro
      (@f_equivI _ _ _ _ _ _ _ Prod.fst ⟨fun {_ _ _} h => dist_fst h⟩ x y)
      (@f_equivI _ _ _ _ _ _ _ Prod.snd ⟨fun {_ _ _} h => dist_snd h⟩ x y)
  · rw [show x = (x.1, x.2) from rfl, show y = (y.1, y.2) from rfl]
    refine @internalEq_rewrite' _ _ _ _ _ _ x.1 y.1 (fun a => internalEq (x.1, x.2) (a, y.2))
      ⟨fun {_ _ _} h => NonExpansive₂.ne Dist.rfl (dist_prod_ext h Dist.rfl)⟩ and_elim_l ?_
    exact @internalEq_rewrite' _ _ _ _ _ _ x.2 y.2 (fun b => internalEq (x.1, x.2) (x.1, b))
      ⟨fun {_ _ _} h => NonExpansive₂.ne Dist.rfl (dist_prod_ext Dist.rfl h)⟩
      and_elim_r (internalEq_refl _ _)

@[rocq_alias option_equivI]
theorem option_some_equivI {A : Type u} [OFE A] (a b : A) :
    internalEq (some a) (some b) ⊣⊢@{PROP} internalEq a b := by
  constructor
  · let Ψ : Option A → PROP := fun y =>
      match y with | some b => internalEq a b | none => BIBase.pure False
    have : NonExpansive Ψ :=
      ⟨fun {n x' y'} (h : Option.Forall₂ (Dist n) x' y') =>
        match x', y', h with
        | some _, some _, h => (BIInternalEq.ne A).ne Dist.rfl h
        | none, none, _ => Dist.rfl⟩
    exact internalEq_rewrite' (some a) (some b) Ψ .rfl (internalEq_refl _ _)
  · exact f_equivI some a b

theorem option_none_equivI (A : Type u) [OFE A] :
    internalEq (none : Option A) none ⊣⊢@{PROP} True :=
  ⟨true_intro, internalEq_refl _ _⟩

theorem option_some_none_equivI {A : Type u} [OFE A] (a : A) :
    internalEq (some a) (none : Option A) ⊣⊢@{PROP} False := by
  constructor
  · let Ψ : Option A → PROP := fun y =>
      match y with | some _ => BIBase.pure True | none => BIBase.pure False
    have : NonExpansive Ψ :=
      ⟨fun {n x' y'} (h : Option.Forall₂ (Dist n) x' y') =>
        match x', y', h with
        | some _, some _, _ => Dist.rfl
        | none, none, _ => Dist.rfl⟩
    exact internalEq_rewrite' (some a) none Ψ .rfl true_intro
  · exact false_elim

theorem option_none_some_equivI {A : Type u} [OFE A] (a : A) :
    internalEq (none : Option A) (some a) ⊣⊢@{PROP} False :=
  ⟨(internalEq_sym _ _).trans (option_some_none_equivI a).1, false_elim⟩

@[rocq_alias excl_equivI]
theorem excl_equivI_excl {O : Type u} [OFE O] (a b : O) :
    internalEq (Excl.excl a) (Excl.excl b) ⊣⊢@{PROP} internalEq a b := by
  constructor
  · let Ψ : Excl O → PROP := fun y =>
      match y with | Excl.excl b => internalEq a b | Excl.invalid => BIBase.pure False
    have : NonExpansive Ψ :=
      ⟨fun {n x' y'} (h : Excl.Dist n x' y') =>
        match x', y', h with
        | Excl.excl _, Excl.excl _, h => (BIInternalEq.ne O).ne Dist.rfl h
        | Excl.excl _, Excl.invalid, h => h.elim
        | Excl.invalid, Excl.excl _, h => h.elim
        | Excl.invalid, Excl.invalid, _ => Dist.rfl⟩
    exact internalEq_rewrite' (Excl.excl a) (Excl.excl b) Ψ .rfl (internalEq_refl _ _)
  · exact f_equivI Excl.excl a b

theorem excl_equivI_invalid (O : Type u) [OFE O] :
    internalEq (Excl.invalid : Excl O) Excl.invalid ⊣⊢@{PROP} True :=
  ⟨true_intro, internalEq_refl _ _⟩

theorem excl_equivI_excl_invalid {O : Type u} [OFE O] (a : O) :
    internalEq (Excl.excl a) (Excl.invalid : Excl O) ⊣⊢@{PROP} False := by
  constructor
  · let Ψ : Excl O → PROP := fun y =>
      match y with | Excl.excl _ => BIBase.pure True | Excl.invalid => BIBase.pure False
    have : NonExpansive Ψ :=
      ⟨fun {n x' y'} (h : Excl.Dist n x' y') =>
        match x', y', h with
        | Excl.excl _, Excl.excl _, _ => Dist.rfl
        | Excl.excl _, Excl.invalid, h => h.elim
        | Excl.invalid, Excl.excl _, h => h.elim
        | Excl.invalid, Excl.invalid, _ => Dist.rfl⟩
    exact internalEq_rewrite' (Excl.excl a) Excl.invalid Ψ .rfl true_intro
  · exact false_elim

theorem excl_equivI_invalid_excl {O : Type u} [OFE O] (a : O) :
    internalEq (Excl.invalid : Excl O) (Excl.excl a) ⊣⊢@{PROP} False :=
  ⟨(internalEq_sym _ _).trans (excl_equivI_excl_invalid a).1, false_elim⟩

@[rocq_alias sig_equivI]
theorem sig_equivI {A : Type u} [OFE A] (P : A → Prop) (x y : Subtype P) :
    internalEq x.val y.val ⊣⊢@{PROP} internalEq x y :=
  ⟨sig_equivI_1 P x y, f_equivI Subtype.val x y⟩

-- sum_equivI: omitted, Sum OFE not available
-- sigT_equivI: omitted, SigmaT OFE not available
-- csum_equivI: omitted, CSum is being ported concurrently

private theorem discreteFun_equivI_mp {A : Type u} {B : A → Type u} [OFEFun B]
    (f g : (x : A) → B x) :
    internalEq f g ⊢@{PROP} ∀ x, internalEq (f x) (g x) := by
  refine @internalEq_rewrite' _ _ _ _ _ _ f g
    (fun (g : (x : A) → B x) => BIBase.forall fun x => internalEq (A := B x) (f x) (g x))
    ⟨fun {n f' g'} h => ?_⟩ .rfl ?_
  · exact sForall_ne ⟨
      fun p ⟨a, ha⟩ => ⟨_, ⟨a, rfl⟩, ha ▸ NonExpansive₂.ne Dist.rfl (h a)⟩,
      fun p ⟨a, ha⟩ => ⟨_, ⟨a, rfl⟩, ha ▸ NonExpansive₂.ne Dist.rfl (h a)⟩⟩
  · exact forall_intro fun _ => internalEq_refl _ _

@[rocq_alias discrete_fun_equivI]
theorem discreteFun_equivI {A : Type u} {B : A → Type u} [OFEFun B]
    (f g : (x : A) → B x) :
    internalEq f g ⊣⊢@{PROP} ∀ x, internalEq (f x) (g x) :=
  ⟨discreteFun_equivI_mp f g, fun_extI f g⟩

private theorem ofeMorO_equivI_mp {A B : Type u} [OFE A] [OFE B] (f g : A -n> B) :
    internalEq f g ⊢@{PROP} ∀ x, internalEq (f x) (g x) := by
  refine @internalEq_rewrite' _ _ _ _ _ _ f g
    (fun (g : A -n> B) => BIBase.forall fun x => internalEq (A := B) (f x) (g x))
    ⟨fun {n f' g'} h => ?_⟩ .rfl ?_
  · exact sForall_ne ⟨
      fun p ⟨a, ha⟩ => ⟨_, ⟨a, rfl⟩, ha ▸ NonExpansive₂.ne Dist.rfl (h a)⟩,
      fun p ⟨a, ha⟩ => ⟨_, ⟨a, rfl⟩, ha ▸ NonExpansive₂.ne Dist.rfl (h a)⟩⟩
  · exact forall_intro fun _ => internalEq_refl _ _

@[rocq_alias ofe_morO_equivI]
theorem ofeMorO_equivI {A B : Type u} [OFE A] [OFE B] (f g : A -n> B) :
    internalEq f g ⊣⊢@{PROP} ∀ x, internalEq (f x) (g x) :=
  ⟨ofeMorO_equivI_mp f g,
   (discreteFun_equivI (PROP := PROP) f.f g.f).2 |>.trans <|
   (sig_equivI_1 (PROP := PROP) _ ⟨f.f, f.ne⟩ ⟨g.f, g.ne⟩).trans <|
   @f_equivI _ _ _ _ _ _ _
     (fun (f : { f : A → B // NonExpansive f }) => (⟨f.val, f.property⟩ : A -n> B))
     ⟨fun {_ _ _} h => h⟩ _ _⟩

/-! ## Modalities -/

@[rocq_alias absorbingly_internal_eq]
theorem absorbingly_internalEq {A : Type u} [OFE A] (x y : A) :
    <absorb> internalEq x y ⊣⊢@{PROP} internalEq x y :=
  BIInternalEq.absorbingly_internalEq x y

@[rocq_alias persistently_internal_eq]
theorem persistently_internalEq {A : Type u} [OFE A] (a b : A) :
    <pers> internalEq a b ⊣⊢@{PROP} internalEq a b :=
  BIInternalEq.persistently_internalEq a b

@[rocq_alias internal_eq_absorbing]
instance internalEq_absorbing {A : Type u} [OFE A] (x y : A) :
    Absorbing (PROP := PROP) (internalEq x y) where
  absorbing := (absorbingly_internalEq x y).1

@[rocq_alias internal_eq_persistent]
instance internalEq_persistent {A : Type u} [OFE A] (a b : A) :
    Persistent (PROP := PROP) (internalEq a b) where
  persistent := (persistently_internalEq a b).2

/-! ## Equality under a later -/

@[rocq_alias later_equivI_1]
theorem later_equivI_1 {A : Type u} [OFE A] (x y : A) :
    internalEq (PROP := PROP) (Later.next x) (Later.next y) ⊢ ▷ internalEq x y :=
  BIInternalEq.later_equivI_1 x y

@[rocq_alias later_equivI_2]
theorem later_equivI_2 {A : Type u} [OFE A] (x y : A) :
    ▷ internalEq x y ⊢@{PROP} internalEq (Later.next x) (Later.next y) :=
  BIInternalEq.later_equivI_2 x y

@[rocq_alias later_equivI]
theorem later_equivI {A : Type u} [OFE A] (x y : A) :
    internalEq (PROP := PROP) (Later.next x) (Later.next y) ⊣⊢ ▷ internalEq x y :=
  ⟨later_equivI_1 x y, later_equivI_2 x y⟩

@[rocq_alias f_equivI_contractive]
theorem f_equivI_contractive {A B : Type u} [OFE A] [OFE B]
    (f : A → B) [hf : Contractive f] (x y : A) :
    ▷ internalEq x y ⊢@{PROP} internalEq (f x) (f y) :=
  (later_equivI_2 x y).trans <|
    @f_equivI _ _ _ _ _ _ _ (f ∘ Later.car) ⟨fun {_ _ _} h => hf.distLater_dist h⟩ _ _

@[rocq_alias internal_eq_rewrite_contractive]
theorem internalEq_rewrite_contractive {A : Type u} [OFE A] (a b : A) (Ψ : A → PROP)
    [Contractive Ψ] :
    ▷ internalEq a b ⊢ Ψ a → Ψ b :=
  (f_equivI_contractive Ψ a b).trans (internalEq_rewrite (Ψ a) (Ψ b) id)

@[rocq_alias internal_eq_rewrite_contractive']
theorem internalEq_rewrite_contractive' {A : Type u} [OFE A] (a b : A) (Ψ : A → PROP)
    [Contractive Ψ] (Heq : P ⊢ ▷ internalEq a b) (HΨa : P ⊢ Ψ a) : P ⊢ Ψ b :=
  (and_intro .rfl HΨa).trans <|
    (and_mono_l Heq).trans <| imp_elim (internalEq_rewrite_contractive a b Ψ)

@[rocq_alias eq_timeless]
instance eq_timeless {A : Type u} [OFE A] (a b : A)
    [TCOr (DiscreteE a) (DiscreteE b)] :
    Timeless (PROP := PROP) (internalEq a b) where
  timeless := (later_mono (discrete_eq a b).1).trans <|
    (Timeless.timeless (P := (BIBase.pure (a ≡ b) : PROP))).trans <|
    except0_mono (discrete_eq a b).2

/-! ## Equality of propositions -/

@[rocq_alias internal_eq_iff]
theorem internalEq_iff (P Q : PROP) :
    internalEq P Q ⊢ BIBase.iff P Q :=
  @internalEq_rewrite' _ _ _ _ _ _ P Q (fun Q => BIBase.iff P Q)
    ⟨fun {_ _ _} h => and_ne.ne (imp_ne.ne Dist.rfl h) (imp_ne.ne h Dist.rfl)⟩
    .rfl (and_intro (imp_intro and_elim_r) (imp_intro and_elim_r))

@[rocq_alias affinely_internal_eq_wand_iff]
theorem affinely_internalEq_wandIff (P Q : PROP) :
    <affine> internalEq P Q ⊢ P ∗-∗ Q :=
  @internalEq_rewrite' _ _ _ _ _ _ P Q (fun Q => wandIff P Q)
    ⟨fun {_ _ _} h => and_ne.ne (wand_ne.ne Dist.rfl h) (wand_ne.ne h Dist.rfl)⟩
    (affinely_elim.trans .rfl) (affinely_elim_emp.trans wandIff_refl)

@[rocq_alias internal_eq_wand_iff]
theorem internalEq_wandIff (P Q : PROP) :
    internalEq P Q ⊢ <absorb> (P ∗-∗ Q) :=
  absorbingly_affinely_intro_of_persistent.trans
    (absorbingly_mono (affinely_internalEq_wandIff P Q))

@[rocq_alias later_equivI_prop_2]
theorem later_equivI_prop_2 (P Q : PROP) :
    ▷ internalEq P Q ⊢ internalEq (PROP := PROP) (BIBase.later P) (BIBase.later Q) :=
  BIInternalEq.later_equivI_prop_2 P Q

@[rocq_alias internal_eq_soundness]
theorem internalEq_soundness {A : Type u} [OFE A] (x y : A) :
    (⊢@{PROP} internalEq x y) → x ≡ y :=
  BIInternalEq.soundness x y

/-! ## Derive NonExpansive/Contractive from internal statements -/

@[rocq_alias internal_eq_entails]
theorem internalEq_entails {A B : Type u} [OFE A] [OFE B] (a₁ a₂ : A) (b₁ b₂ : B) :
    Iff (internalEq a₁ a₂ ⊢@{PROP} internalEq b₁ b₂)
      (∀ n, a₁ ≡{n}≡ a₂ → b₁ ≡{n}≡ b₂) :=
  BIInternalEq.entails a₁ a₂ b₁ b₂

@[rocq_alias ne_internal_eq]
theorem ne_internalEq {A B : Type u} [OFE A] [OFE B] (f : A → B) :
    Iff (NonExpansive f) (∀ x₁ x₂, internalEq x₁ x₂ ⊢@{PROP} internalEq (f x₁) (f x₂)) :=
  ⟨fun ⟨hne⟩ x₁ x₂ => (internalEq_entails x₁ x₂ (f x₁) (f x₂)).mpr (fun _ h => hne h),
   fun h => ⟨fun {_ _ _} hx => (internalEq_entails _ _ _ _).mp (h _ _) _ hx⟩⟩

@[rocq_alias ne_2_internal_eq]
theorem ne_2_internalEq {A B C : Type u} [OFE A] [OFE B] [OFE C] (f : A → B → C) :
    Iff (NonExpansive₂ f)
      (∀ x₁ x₂ y₁ y₂, internalEq x₁ x₂ ∧ internalEq y₁ y₂ ⊢@{PROP}
        internalEq (f x₁ y₁) (f x₂ y₂)) := by
  constructor
  · intro hf x₁ x₂ y₁ y₂
    exact (prod_equivI (PROP := PROP) (x₁, y₁) (x₂, y₂) |>.2).trans
      (@f_equivI _ _ _ _ _ _ _ (Function.uncurry f)
        ⟨fun {_ _ _} (h : _ ∧ _) => hf.ne h.1 h.2⟩ _ _)
  · intro hf
    exact ⟨fun {_ x₁ x₂} hx {y₁ y₂} hy =>
      (internalEq_entails (x₁, y₁) (x₂, y₂) (f x₁ y₁) (f x₂ y₂)).mp
        (prod_equivI _ _ |>.1 |>.trans (hf _ _ _ _)) _ (dist_prod_ext hx hy)⟩

@[rocq_alias contractive_internal_eq]
theorem contractive_internalEq {A B : Type u} [OFE A] [OFE B] (f : A → B) :
    Iff (Contractive f)
      (∀ x₁ x₂, ▷ internalEq x₁ x₂ ⊢@{PROP} internalEq (f x₁) (f x₂)) := by
  constructor
  · intro _ x₁ x₂
    exact f_equivI_contractive f x₁ x₂
  · intro hf
    exact ⟨fun {n x y} h =>
      (internalEq_entails (Later.next x) (Later.next y) (f x) (f y)).mp
        ((later_equivI_1 x y).trans (hf x y)) n h⟩

@[rocq_alias sbi_later_contractive]
instance sbi_later_contractive : BILaterContractive PROP where
  toContractive := (contractive_internalEq (PROP := PROP) BIBase.later).mpr
    (fun P Q => later_equivI_prop_2 P Q)

end InternalEqLaws

end Iris.BI
