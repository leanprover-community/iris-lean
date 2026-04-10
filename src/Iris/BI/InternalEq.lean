/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.BI.Sbi
public import Iris.Algebra.Csum
public import Iris.Algebra.Excl

@[expose] public section

namespace Iris
open BI OFE Iris.Std

/-- Internal equality in a BI with step-indexed structure, defined as
`siPure (SiProp.internalEq a b)`. -/
@[rocq_alias internal_eq]
def internalEq [Sbi PROP] {A : Type _} [OFE A] (a b : A) : PROP :=
  iprop(<si_pure> (SiProp.internalEq a b))

namespace BI

section internalEqLaws

variable {PROP : Type u} [Sbi PROP] {P Q : PROP}

namespace internalEq


@[rocq_alias bi.internal_eq_ne]
instance instInternalEq_ne (A : Type _) [OFE A] :
    NonExpansive₂ (internalEq (PROP := PROP) (A := A)) where
  ne _ _ _ h₁ _ _ h₂ := Sbi.siPure_ne.ne (SiProp.instNonExpansive₂InternalEq.ne h₁ h₂)

theorem ne_l {A : Type _} [OFE A] (a : A) :
    NonExpansive (internalEq (PROP := PROP) · a) :=
  NonExpansive₂.ne_left internalEq a

theorem ne_r {A : Type _} [OFE A] (a : A) :
    NonExpansive (internalEq (PROP := PROP) a ·) :=
  NonExpansive₂.ne_right internalEq a

@[rocq_alias bi.internal_eq_refl]
theorem refl {A : Type _} [OFE A] {P : PROP} {a : A} : P ⊢ internalEq a a :=
  true_intro.trans <| siPure_pure.mpr.trans <| siPure_mono (SiProp.internalEq_refl _ _)

@[rocq_alias equiv_internal_eq]
theorem of_equiv {A : Type _} [OFE A] {P : PROP} {a b : A} (h : a ≡ b) :
    P ⊢ internalEq a b :=
  refl.trans (equiv_iff.mp (NonExpansive₂.eqv Equiv.rfl h)).1

@[rocq_alias pure_internal_eq]
theorem of_pure {A : Type _} [OFE A] {x y : A} : ⌜x ≡ y⌝ ⊢ internalEq (PROP := PROP) x y :=
  pure_elim' of_equiv

@[rocq_alias bi.internal_eq_rewrite]
theorem rewrite {A : Type _} [OFE A] {a b : A} (Ψ : A → PROP) [hΨ : NonExpansive Ψ] :
    internalEq a b ⊢ Ψ a → Ψ b := by
  let Φ : A → SiProp := fun a' => iprop(<si_emp_valid> (True -∗ Ψ a → Ψ a'))
  letI _ : NonExpansive Φ :=
    ⟨fun {_ _ _} h => Sbi.siEmpValid_ne.ne (wand_ne.ne .rfl (imp_ne.ne .rfl (hΨ.ne h)))⟩
  calc internalEq (PROP := PROP) a b
    _ ⊢ <si_pure> iprop(Φ a → Φ b) := siPure_mono (SiProp.internalEq_rewrite _ _ _)
    _ ⊢ <si_pure> (Φ b) := by
        refine mp siPure_imp.mp ?_
        refine persistently_emp_intro.trans ?_
        refine (persistently_mono (siPure_emp_valid.mpr ?_)).trans persistently_elim
        refine siEmpValid_emp_valid.mpr ?_
        exact wand_intro' (sep_emp.1.trans <| imp_intro and_elim_r)
    _ ⊢ True -∗ Ψ a → Ψ b := siPure_siEmpValid_elim
    _ ⊢ Ψ a → Ψ b := emp_sep.2.trans <| (sep_mono_l true_intro).trans wand_elim_r

@[rocq_alias internal_eq_rewrite']
theorem rewrite' {A : Type _} [OFE A] {a b : A} (Ψ : A → PROP) [NonExpansive Ψ]
     (Heq : P ⊢ internalEq a b) (HΨa : P ⊢ Ψ a) : P ⊢ Ψ b :=
  (and_intro .rfl HΨa).trans <| (and_mono_l Heq).trans <| imp_elim (rewrite Ψ)

@[rocq_alias internal_eq_sym]
theorem symm {A : Type _} [OFE A] {a b : A} : internalEq a b ⊢@{PROP} internalEq b a :=
  letI _ := ne_l (PROP := PROP) a
  rewrite' (internalEq · a) .rfl refl

@[rocq_alias internal_eq_trans]
theorem trans {A : Type _} [OFE A] {a b c : A} :
    internalEq a b ∧ internalEq b c ⊢@{PROP} internalEq a c :=
  letI _ := ne_l (PROP := PROP) c
  rewrite' (internalEq · c) (and_elim_l.trans symm) and_elim_r

@[rocq_alias f_equivI]
theorem of_internalEquiv_ne {A B : Type _} [OFE A] [OFE B] (f : A → B) [hf : NonExpansive f] {x y : A} :
    internalEq x y ⊢@{PROP} internalEq (f x) (f y) :=
  letI _ : NonExpansive (fun y => internalEq (PROP := PROP) (f x) (f y)) := (ne_r (f x)).comp hf
  rewrite' (fun y => internalEq (f x) (f y)) .rfl refl

end internalEq

section datatypes

open internalEq

@[rocq_alias bi.discrete_eq_1]
theorem discrete_eq_mp {A : Type _} [OFE A] {a b : A} [TCOr (DiscreteE a) (DiscreteE b)] :
    internalEq a b ⊢@{PROP} ⌜a ≡ b⌝ :=
  siPure_mono (SiProp.discrete_eq_internalEq _ _)|>.trans siPure_pure.mp

@[rocq_alias discrete_eq]
theorem discrete_eq {A : Type _} [OFE A] {a b : A} [TCOr (DiscreteE a) (DiscreteE b)] :
    internalEq a b ⊣⊢@{PROP} ⌜a ≡ b⌝ :=
  ⟨discrete_eq_mp, of_pure⟩

@[rocq_alias bi.fun_extI]
theorem fun_extI {A : Type _} {B : A → Type _} [OFEFun B] {f g : (x : A) → B x} :
    (∀ x, internalEq (f x) (g x)) ⊢ internalEq (PROP := PROP) f g :=
  siPure_forall_mpr.trans <| siPure_mono (SiProp.fun_ext_internalEq f g)

@[rocq_alias bi.sig_equivI_1]
theorem sig_equivI_mp {A : Type _} [OFE A] {P : A → Prop} {x y : Subtype P} :
    internalEq x.val y.val ⊢@{PROP} internalEq x y :=
  siPure_mono (SiProp.sig_equiv_internalEq P x y)

@[rocq_alias sig_equivI]
theorem sig_equivI {A : Type _} [OFE A] (P : A → Prop) (x y : Subtype P) :
    internalEq x.val y.val ⊣⊢@{PROP} internalEq x y :=
  ⟨sig_equivI_mp, of_internalEquiv_ne Subtype.val⟩

-- TODO: sum_equivI (requires Sum OFE)
-- TODO: sigT_equivI (requires SigmaT OFE)

@[rocq_alias prod_equivI]
theorem prod_equivI {A B : Type _} [OFE A] [OFE B] (x y : A × B) :
    internalEq x y ⊣⊢@{PROP} internalEq x.1 y.1 ∧ internalEq x.2 y.2 := by
  constructor
  · exact and_intro (of_internalEquiv_ne Prod.fst) (of_internalEquiv_ne Prod.snd)
  · letI _ : NonExpansive (fun a => internalEq (PROP := PROP) x (a, y.2)) :=
      (ne_r x).comp (prod_mk_ne_left y.2)
    letI _ : NonExpansive (fun b => internalEq (PROP := PROP) x (x.1, b)) :=
      (ne_r x).comp (prod_mk_ne_right x.1)
    refine rewrite' (fun a => internalEq x (a, y.2)) and_elim_l ?_
    exact rewrite' (fun b => internalEq x (x.1, b)) and_elim_r refl

@[rocq_alias option_equivI]
theorem option_some_equivI {A : Type _} [OFE A] (a b : A) :
    internalEq (some a) (some b) ⊣⊢@{PROP} internalEq a b := by
  refine ⟨?_, of_internalEquiv_ne some⟩
  let Ψ : Option A → PROP := fun y =>
    match y with | some b => internalEq a b | none => iprop(⌜False⌝)
  have : NonExpansive Ψ := Option.ne_match _ (ne_r a) _
  exact rewrite' Ψ .rfl refl

theorem option_none_equivI (A : Type _) [OFE A] :
    internalEq (none : Option A) none ⊣⊢@{PROP} True :=
  ⟨true_intro, refl⟩

theorem option_some_none_equivI {A : Type _} [OFE A] (a : A) :
    internalEq (some a) (none : Option A) ⊣⊢@{PROP} False := by
  refine ⟨?_, false_elim⟩
  let Ψ : Option A → PROP := fun y =>
    match y with | some _ => iprop(⌜True⌝) | none => iprop(⌜False⌝)
  have : NonExpansive Ψ := Option.ne_match _ ⟨fun {_ _ _} _ => Dist.rfl⟩ _
  exact rewrite' Ψ .rfl true_intro

theorem option_none_some_equivI {A : Type _} [OFE A] (a : A) :
    internalEq (none : Option A) (some a) ⊣⊢@{PROP} False :=
  ⟨symm.trans (option_some_none_equivI a).1, false_elim⟩

@[rocq_alias excl_equivI]
theorem excl_equivI_excl {O : Type _} [OFE O] (a b : O) :
    internalEq (Excl.excl a) (Excl.excl b) ⊣⊢@{PROP} internalEq a b := by
  refine ⟨?_, of_internalEquiv_ne Excl.excl⟩
  let Ψ : Excl O → PROP := fun y =>
    match y with | Excl.excl b => internalEq a b | Excl.invalid => iprop(⌜False⌝)
  have : NonExpansive Ψ := Excl.ne_match _ (ne_r a) _
  exact rewrite' Ψ .rfl refl

theorem excl_equivI_invalid (O : Type _) [OFE O] :
    internalEq (Excl.invalid : Excl O) Excl.invalid ⊣⊢@{PROP} True :=
  ⟨true_intro, refl⟩

theorem excl_equivI_excl_invalid {O : Type _} [OFE O] (a : O) :
    internalEq (Excl.excl a) (Excl.invalid : Excl O) ⊣⊢@{PROP} False := by
  refine ⟨?_, false_elim⟩
  let Ψ : Excl O → PROP := fun y =>
    match y with | Excl.excl _ => iprop(⌜True⌝) | Excl.invalid => iprop(⌜False⌝)
  have : NonExpansive Ψ := Excl.ne_match _ ⟨fun {_ _ _} _ => Dist.rfl⟩ _
  exact rewrite' Ψ .rfl true_intro

theorem excl_equivI_invalid_excl {O : Type _} [OFE O] (a : O) :
    internalEq (Excl.invalid : Excl O) (Excl.excl a) ⊣⊢@{PROP} False :=
  ⟨symm.trans (excl_equivI_excl_invalid a).1, false_elim⟩

@[rocq_alias csum_equivI]
theorem csum_equivI {A B : Type _} [OFE A] [OFE B] (sx sy : Csum A B) :
    internalEq sx sy ⊣⊢@{PROP}
      match sx, sy with
      | .inl x, .inl y => internalEq x y
      | .inr x, .inr y => internalEq x y
      | .invalid, .invalid => iprop(⌜True⌝)
      | _, _ => iprop(⌜False⌝) := by
  constructor
  · let Ψ : Csum A B → PROP := fun sy' =>
      match sx, sy' with
      | .inl x, .inl y => internalEq x y
      | .inr x, .inr y => internalEq x y
      | .invalid, .invalid => iprop(⌜True⌝)
      | _, _ => iprop(⌜False⌝)
    have : NonExpansive Ψ := by
      refine ⟨fun {n x' y'} (h : Csum.Dist n x' y') => ?_⟩
      cases sx <;> cases x' <;> cases y' <;> first
        | exact (ne_r _).ne h
        | exact Dist.rfl
        | exact h.elim
    refine rewrite' Ψ .rfl ?_
    cases sx <;> first | exact refl | exact true_intro
  · cases sx <;> cases sy <;> first
      | exact of_internalEquiv_ne _
      | exact refl
      | exact false_elim

theorem discreteFun_equivI_mp {A : Type _} {B : A → Type _} [OFEFun B] (f g : (x : A) → B x) :
    internalEq f g ⊢@{PROP} ∀ x, internalEq (f x) (g x) := by
  let Ψ : ((x : A) → B x) → PROP := fun g => iprop(∀ x, internalEq (A := B x) (f x) (g x))
  have : NonExpansive Ψ := ⟨fun {_ _ _} h => sForall_ne ⟨
    fun p ⟨a, ha⟩ => ⟨_, ⟨a, rfl⟩, ha ▸ (ne_r (f a)).ne (h a)⟩,
    fun p ⟨a, ha⟩ => ⟨_, ⟨a, rfl⟩, ha ▸ (ne_r (f a)).ne (h a)⟩⟩⟩
  exact rewrite' Ψ .rfl (forall_intro fun _ => refl)

@[rocq_alias discrete_fun_equivI]
theorem discreteFun_equivI {A : Type _} {B : A → Type _} [OFEFun B] (f g : (x : A) → B x) :
    internalEq f g ⊣⊢@{PROP} ∀ x, internalEq (f x) (g x) :=
  ⟨discreteFun_equivI_mp f g, fun_extI⟩

theorem ofeMorO_equivI_mp {A B : Type _} [OFE A] [OFE B] (f g : A -n> B) :
    internalEq f g ⊢@{PROP} ∀ x, internalEq (f x) (g x) := by
  let Ψ : (A -n> B) → PROP := fun g => iprop(∀ x, internalEq (A := B) (f x) (g x))
  have : NonExpansive Ψ := ⟨fun {_ _ _} h => sForall_ne ⟨
    fun p ⟨a, ha⟩ => ⟨_, ⟨a, rfl⟩, ha ▸ (ne_r (f a)).ne (h a)⟩,
    fun p ⟨a, ha⟩ => ⟨_, ⟨a, rfl⟩, ha ▸ (ne_r (f a)).ne (h a)⟩⟩⟩
  exact rewrite' Ψ .rfl (forall_intro fun _ => refl)

theorem ofeMorO_equivI_mpr {A B : Type _} [OFE A] [OFE B] (f g : A -n> B) :
    (∀ x, internalEq (f x) (g x)) ⊢@{PROP} internalEq f g := by
  refine (discreteFun_equivI (PROP := PROP) f.f g.f).2 |>.trans ?_
  refine (sig_equivI_mp (x := f.toSubtype) (y := g.toSubtype)).trans ?_
  exact of_internalEquiv_ne Hom.ofSubtype

@[rocq_alias ofe_morO_equivI]
theorem ofeMorO_equivI {A B : Type _} [OFE A] [OFE B] (f g : A -n> B) :
    internalEq f g ⊣⊢@{PROP} ∀ x, internalEq (f x) (g x) :=
  ⟨ofeMorO_equivI_mp f g, ofeMorO_equivI_mpr f g⟩

/-! ## Modalities -/

@[rocq_alias absorbingly_internal_eq]
theorem absorbingly_internalEq {A : Type _} [OFE A] (x y : A) :
    <absorb> internalEq x y ⊣⊢@{PROP} internalEq x y :=
  absorbingly_siPure

@[rocq_alias persistently_internal_eq]
theorem persistently_internalEq {A : Type _} [OFE A] (a b : A) :
    <pers> internalEq a b ⊣⊢@{PROP} internalEq a b :=
  persistently_siPure

@[rocq_alias internal_eq_absorbing]
instance internalEq_absorbing {A : Type _} [OFE A] (x y : A) :
    Absorbing (PROP := PROP) (internalEq x y) where
  absorbing := (absorbingly_internalEq x y).1

@[rocq_alias internal_eq_persistent]
instance internalEq_persistent {A : Type _} [OFE A] (a b : A) :
    Persistent (PROP := PROP) (internalEq a b) where
  persistent := (persistently_internalEq a b).2

/-! ## Equality under a later -/

@[rocq_alias bi.later_equivI_1]
theorem later_equivI_mp {A : Type _} [OFE A] (x y : A) :
    internalEq (PROP := PROP) (Later.next x) (Later.next y) ⊢ ▷ internalEq x y :=
  (siPure_mono (SiProp.later_equiv_internalEq_mp x y)).trans siPure_later.mp

@[rocq_alias bi.later_equivI_2]
theorem later_equivI_mpr {A : Type _} [OFE A] (x y : A) :
    ▷ internalEq x y ⊢@{PROP} internalEq (Later.next x) (Later.next y) :=
  siPure_later.mpr.trans (siPure_mono (SiProp.later_equiv_internalEq_mpr x y))

@[rocq_alias later_equivI]
theorem later_equivI {A : Type _} [OFE A] (x y : A) :
    internalEq (PROP := PROP) (Later.next x) (Later.next y) ⊣⊢ ▷ internalEq x y :=
  ⟨later_equivI_mp x y, later_equivI_mpr x y⟩

@[rocq_alias f_equivI_contractive]
theorem f_equivI_contractive {A B : Type _} [OFE A] [OFE B] (f : A → B) [hf : Contractive f]
    (x y : A) : ▷ internalEq x y ⊢@{PROP} internalEq (f x) (f y) := by
  letI _ : NonExpansive (f ∘ Later.car) := ⟨fun {_ _ _} h => hf.distLater_dist h⟩
  exact (later_equivI_mpr x y).trans <| of_internalEquiv_ne (f ∘ Later.car)

@[rocq_alias internal_eq_rewrite_contractive]
theorem internalEq_rewrite_contractive {A : Type _} [OFE A] (a b : A) (Ψ : A → PROP)
    [Contractive Ψ] :
    ▷ internalEq a b ⊢ Ψ a → Ψ b :=
  (f_equivI_contractive Ψ a b).trans (rewrite id)

@[rocq_alias internal_eq_rewrite_contractive']
theorem internalEq_rewrite_contractive' {A : Type _} [OFE A] (a b : A) (Ψ : A → PROP)
    [Contractive Ψ] (Heq : P ⊢ ▷ internalEq a b) (HΨa : P ⊢ Ψ a) : P ⊢ Ψ b :=
  (and_intro .rfl HΨa).trans <|
    (and_mono_l Heq).trans <| imp_elim (internalEq_rewrite_contractive a b Ψ)

@[rocq_alias eq_timeless]
instance eq_timeless {A : Type _} [OFE A] (a b : A) [TCOr (DiscreteE a) (DiscreteE b)] :
    Timeless (PROP := PROP) (internalEq a b) where
  timeless :=
    calc iprop(▷ internalEq a b)
      _ ⊢ ▷ ⌜a ≡ b⌝ := later_mono discrete_eq.1
      _ ⊢ ◇ ⌜a ≡ b⌝ := Timeless.timeless (P := iprop(⌜a ≡ b⌝))
      _ ⊢ ◇ internalEq a b := except0_mono discrete_eq.2

/-! ## Equality of propositions -/

@[rocq_alias internal_eq_iff]
theorem internalEq_iff (P Q : PROP) : internalEq P Q ⊢ iprop(P ↔ Q) :=
  letI _ := NonExpansive₂.ne_right (BIBase.iff (PROP := PROP)) P
  rewrite' (BIBase.iff P) .rfl (and_intro (imp_intro and_elim_r) (imp_intro and_elim_r))

@[rocq_alias affinely_internal_eq_wand_iff]
theorem affinely_internalEq_wandIff (P Q : PROP) : <affine> internalEq P Q ⊢ P ∗-∗ Q :=
  letI _ := NonExpansive₂.ne_right (wandIff (PROP := PROP)) P
  rewrite' (wandIff P) (affinely_elim.trans .rfl) (affinely_elim_emp.trans wandIff_refl)

@[rocq_alias internal_eq_wand_iff]
theorem internalEq_wandIff (P Q : PROP) : internalEq P Q ⊢ <absorb> (P ∗-∗ Q) :=
  absorbingly_affinely_intro_of_persistent.trans (absorbingly_mono (affinely_internalEq_wandIff P Q))

@[rocq_alias si_pure_internal_eq]
theorem siPure_internalEq {A : Type _} [OFE A] (x y : A) :
    <si_pure> (SiProp.internalEq x y) ⊣⊢@{PROP} internalEq x y := .rfl

@[rocq_alias prop_ext_si_emp_valid_2]
theorem prop_ext_siEmpValid_mpr (P Q : PROP) :
    iprop(<si_emp_valid> (P ∗-∗ Q)) ⊢@{SiProp} SiProp.internalEq P Q :=
  prop_ext_siEmpValid

@[rocq_alias prop_ext_si_emp_valid]
theorem prop_ext_siEmpValid_equiv (P Q : PROP) :
    SiProp.internalEq P Q ⊣⊢@{SiProp} <si_emp_valid> (P ∗-∗ Q) := by
  letI _ : NonExpansive (fun Q : PROP => iprop(<si_pure> <si_emp_valid> (P ∗-∗ Q))) :=
    ((Sbi.siPure_ne (PROP := PROP)).comp Sbi.siEmpValid_ne).comp (NonExpansive₂.ne_right wandIff P)
  refine ⟨?_, prop_ext_siEmpValid⟩
  rw [← siPure_entails (PROP := PROP)]
  change internalEq P Q ⊢@{PROP} <si_pure> <si_emp_valid> (P ∗-∗ Q)
  refine rewrite' (fun Q => iprop(<si_pure> <si_emp_valid> (P ∗-∗ Q))) .rfl ?_
  refine (pure_intro trivial).trans <| ?_
  refine siPure_pure.mpr.trans (siPure_mono ?_)
  refine siEmpValid_emp.mpr.trans (siEmpValid_mono wandIff_refl)

@[rocq_alias later_equivI_prop_2]
theorem later_equivI_prop_mpr (P Q : PROP) :
    ▷ internalEq P Q ⊢ internalEq (PROP := PROP) (BIBase.later P) (BIBase.later Q) := by
  show iprop(▷ <si_pure> (SiProp.internalEq P Q) ⊢ <si_pure> (SiProp.internalEq (BIBase.later P) (BIBase.later Q)))
  calc iprop(▷ <si_pure> (SiProp.internalEq P Q))
    _ ⊢ <si_pure> ▷ (SiProp.internalEq P Q) := siPure_later.mpr
    _ ⊢ <si_pure> ▷ (<si_emp_valid> (P ∗-∗ Q)) :=
        siPure_mono (later_mono (prop_ext_siEmpValid_equiv P Q).mp)
    _ ⊢ <si_pure> <si_emp_valid> ▷ (P ∗-∗ Q) := siPure_mono siEmpValid_later.mpr
    _ ⊢ <si_pure> <si_emp_valid> (▷ P ∗-∗ ▷ Q) := siPure_mono (siEmpValid_mono later_wand_iff)
    _ ⊢ <si_pure> (SiProp.internalEq (BIBase.later P) (BIBase.later Q)) :=
        siPure_mono (prop_ext_siEmpValid_equiv _ _).mpr

@[rocq_alias bi.internal_eq_soundness]
theorem internalEq_soundness {A : Type _} [OFE A] (x y : A) :
    (⊢@{PROP} internalEq x y) → x ≡ y :=
  (SiProp.internalEq_soundness <| siPure_emp_valid.mp ·)

/-! ## Derive NonExpansive/Contractive from internal statements -/

@[rocq_alias bi.internal_eq_entails]
theorem internalEq_entails {A B : Type _} [OFE A] [OFE B] {a₁ a₂ : A} {b₁ b₂ : B} :
    (internalEq a₁ a₂ ⊢@{PROP} internalEq b₁ b₂) ↔ (∀ n, a₁ ≡{n}≡ a₂ → b₁ ≡{n}≡ b₂) :=
  siPure_entails.trans (SiProp.internalEq_entails ..)

@[rocq_alias ne_internal_eq]
theorem ne_internalEq {A B : Type _} [OFE A] [OFE B] (f : A → B) :
    NonExpansive f ↔ (∀ {x₁ x₂}, internalEq x₁ x₂ ⊢@{PROP} internalEq (f x₁) (f x₂)) :=
  ⟨fun ⟨hne⟩ _ _ => internalEq_entails.mpr (fun _ h => hne h),
   fun h => ⟨fun {_ _ _} hx => internalEq_entails.mp h _ hx⟩⟩

@[rocq_alias ne_2_internal_eq]
theorem ne_2_internalEq {A B C : Type _} [OFE A] [OFE B] [OFE C] (f : A → B → C) :
    NonExpansive₂ f ↔
      (∀ x₁ x₂ y₁ y₂, internalEq x₁ x₂ ∧ internalEq y₁ y₂ ⊢@{PROP}
        internalEq (f x₁ y₁) (f x₂ y₂)) := by
  constructor
  · intro hf x₁ x₂ y₁ y₂
    letI _ := hf.uncurry
    exact (prod_equivI (PROP := PROP) (x₁, y₁) (x₂, y₂) |>.2).trans
      (of_internalEquiv_ne (Function.uncurry f))
  · exact fun hf => ⟨fun {_ x₁ x₂} hx {y₁ y₂} hy =>
      internalEq_entails.mp (prod_equivI _ _ |>.1 |>.trans (hf ..)) _ (dist_prod_ext hx hy)⟩

@[rocq_alias contractive_internal_eq]
theorem contractive_internalEq {A B : Type _} [OFE A] [OFE B] (f : A → B) :
    Contractive f ↔ (∀ x₁ x₂, ▷ internalEq x₁ x₂ ⊢@{PROP} internalEq (f x₁) (f x₂)) :=
  ⟨fun _ x₁ x₂ => f_equivI_contractive f x₁ x₂,
   fun hf => ⟨fun {n x y} h => internalEq_entails.mp ((later_equivI_mp x y).trans (hf x y)) n h⟩⟩

@[rocq_alias sbi_later_contractive]
instance sbi_later_contractive : BILaterContractive PROP where
  toContractive := (contractive_internalEq (PROP := PROP) BIBase.later).mpr
    (fun P Q => later_equivI_prop_mpr P Q)

end datatypes

end internalEqLaws

end Iris.BI
