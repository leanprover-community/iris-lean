/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
import Iris.BI.Sbi
import Iris.Algebra.Csum
import Iris.Algebra.Excl

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

theorem ne_l {A : Type u} [OFE A] (a : A) :
    NonExpansive (internalEq (PROP := PROP) · a) :=
  NonExpansive₂.ne_left internalEq a

theorem ne_r {A : Type u} [OFE A] (a : A) :
    NonExpansive (internalEq (PROP := PROP) a ·) :=
  NonExpansive₂.ne_right internalEq a

@[rocq_alias bi.internal_eq_refl]
theorem refl {A : Type u} [OFE A] {P : PROP} {a : A} : P ⊢ internalEq a a :=
  true_intro.trans <| siPure_pure.mpr.trans <| siPure_mono (SiProp.internalEq_refl _ _)

@[rocq_alias equiv_internal_eq]
theorem of_equiv {A : Type u} [OFE A] {P : PROP} {a b : A} (h : a ≡ b) :
    P ⊢ internalEq a b :=
  refl.trans (equiv_iff.mp (NonExpansive₂.eqv Equiv.rfl h)).1

@[rocq_alias pure_internal_eq]
theorem of_pure {A : Type u} [OFE A] {x y : A} : ⌜x ≡ y⌝ ⊢ internalEq (PROP := PROP) x y :=
  pure_elim' of_equiv

@[rocq_alias bi.internal_eq_rewrite]
theorem rewrite {A : Type u} [OFE A] {a b : A} (Ψ : A → PROP) [hΨ : NonExpansive Ψ] :
    internalEq a b ⊢ Ψ a → Ψ b := by
  let Φ : A → SiProp := fun a' => siEmpValid (PROP := PROP) iprop(True -∗ Ψ a → Ψ a')
  letI _ : NonExpansive Φ :=
    ⟨fun {_ _ _} h => Sbi.siEmpValid_ne.ne (wand_ne.ne .rfl (imp_ne.ne .rfl (hΨ.ne h)))⟩
  calc internalEq (PROP := PROP) a b
    _ ⊢ siPure iprop(Φ a → Φ b) := siPure_mono (SiProp.internalEq_rewrite _ _ _)
    _ ⊢ siPure (Φ b) := by
        refine mp siPure_imp.mp ?_
        refine persistently_emp_intro.trans ?_
        refine (persistently_mono (siPure_emp_valid.mpr ?_)).trans persistently_elim
        refine siEmpValid_emp_valid.mpr ?_
        exact wand_intro' (sep_emp.1.trans <| imp_intro and_elim_r)
    _ ⊢ True -∗ Ψ a → Ψ b := siPure_siEmpValid_elim
    _ ⊢ Ψ a → Ψ b := emp_sep.2.trans <| (sep_mono_l true_intro).trans wand_elim_r

@[rocq_alias internal_eq_rewrite']
theorem rewrite' {A : Type u} [OFE A] {a b : A} (Ψ : A → PROP) [NonExpansive Ψ]
     (Heq : P ⊢ internalEq a b) (HΨa : P ⊢ Ψ a) : P ⊢ Ψ b :=
  (and_intro .rfl HΨa).trans <| (and_mono_l Heq).trans <| imp_elim (rewrite Ψ)

@[rocq_alias internal_eq_sym]
theorem symm {A : Type u} [OFE A] {a b : A} : internalEq a b ⊢@{PROP} internalEq b a :=
  letI _ := ne_l (PROP := PROP) a
  rewrite' (internalEq · a) .rfl refl

@[rocq_alias internal_eq_trans]
theorem trans {A : Type u} [OFE A] {a b c : A} :
    internalEq a b ∧ internalEq b c ⊢@{PROP} internalEq a c :=
  letI _ := ne_l (PROP := PROP) c
  rewrite' (internalEq · c) (and_elim_l.trans symm) and_elim_r

@[rocq_alias f_equivI]
theorem of_internalEquiv_ne {A B : Type u} [OFE A] [OFE B] (f : A → B) [hf : NonExpansive f] {x y : A} :
    internalEq x y ⊢@{PROP} internalEq (f x) (f y) :=
  letI _ : NonExpansive (fun y => internalEq (PROP := PROP) (f x) (f y)) := (ne_r (f x)).comp hf
  rewrite' (fun y => internalEq (f x) (f y)) .rfl refl

-- Here

end internalEq

section datatypes

open internalEq

@[rocq_alias bi.discrete_eq_1]
theorem discrete_eq_1 {A : Type u} [OFE A] (a b : A) [TCOr (DiscreteE a) (DiscreteE b)] :
    internalEq a b ⊢@{PROP} ⌜a ≡ b⌝ :=
  (siPure_mono (SiProp.discrete_eq_internalEq a b)).trans siPure_pure.mp

@[rocq_alias discrete_eq]
theorem discrete_eq {A : Type u} [OFE A] (a b : A) [TCOr (DiscreteE a) (DiscreteE b)] :
    internalEq a b ⊣⊢@{PROP} ⌜a ≡ b⌝ :=
  ⟨discrete_eq_1 _ _, of_pure⟩

@[rocq_alias bi.sig_equivI_1]
theorem sig_equivI_1 {A : Type u} [OFE A] (P : A → Prop) (x y : Subtype P) :
    internalEq x.val y.val ⊢@{PROP} internalEq x y :=
  siPure_mono (SiProp.sig_equiv_internalEq P x y)

@[rocq_alias bi.fun_extI]
theorem fun_extI {A : Type u} {B : A → Type u} [OFEFun B] (f g : (x : A) → B x) :
    (∀ x, internalEq (f x) (g x)) ⊢ internalEq (PROP := PROP) f g :=
  siPure_forall_mpr.trans <| siPure_mono (SiProp.fun_ext_internalEq f g)

@[rocq_alias prod_equivI]
theorem prod_equivI {A B : Type u} [OFE A] [OFE B] (x y : A × B) :
    internalEq x y ⊣⊢@{PROP} internalEq x.1 y.1 ∧ internalEq x.2 y.2 := by
  constructor
  · exact and_intro (of_internalEquiv_ne Prod.fst) (of_internalEquiv_ne Prod.snd)
  · rw [show x = (x.1, x.2) from rfl, show y = (y.1, y.2) from rfl]
    letI _ : NonExpansive (fun a => internalEq (PROP := PROP) (x.1, x.2) (a, y.2)) :=
      (ne_r (x.1, x.2)).comp (prod_mk_ne_left y.2)
    letI _ : NonExpansive (fun b => internalEq (PROP := PROP) (x.1, x.2) (x.1, b)) :=
      (ne_r (x.1, x.2)).comp (prod_mk_ne_right x.1)
    refine rewrite' (fun a => internalEq (x.1, x.2) (a, y.2)) and_elim_l ?_
    exact rewrite' (fun b => internalEq (x.1, x.2) (x.1, b)) and_elim_r refl

@[rocq_alias option_equivI]
theorem option_some_equivI {A : Type u} [OFE A] (a b : A) :
    internalEq (some a) (some b) ⊣⊢@{PROP} internalEq a b := by
  constructor
  · let Ψ : Option A → PROP := fun y =>
      match y with | some b => internalEq a b | none => BIBase.pure False
    have : NonExpansive Ψ :=
      ⟨fun {n x' y'} (h : Option.Forall₂ (Dist n) x' y') =>
        match x', y', h with
        | some _, some _, h => (ne_r a).ne h
        | none, none, _ => Dist.rfl⟩
    exact rewrite' Ψ .rfl refl
  · exact of_internalEquiv_ne some

theorem option_none_equivI (A : Type u) [OFE A] :
    internalEq (none : Option A) none ⊣⊢@{PROP} True :=
  ⟨true_intro, refl⟩

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
    exact rewrite' Ψ .rfl true_intro
  · exact false_elim

theorem option_none_some_equivI {A : Type u} [OFE A] (a : A) :
    internalEq (none : Option A) (some a) ⊣⊢@{PROP} False :=
  ⟨symm.trans (option_some_none_equivI a).1, false_elim⟩

@[rocq_alias excl_equivI]
theorem excl_equivI_excl {O : Type u} [OFE O] (a b : O) :
    internalEq (Excl.excl a) (Excl.excl b) ⊣⊢@{PROP} internalEq a b := by
  constructor
  · let Ψ : Excl O → PROP := fun y =>
      match y with | Excl.excl b => internalEq a b | Excl.invalid => BIBase.pure False
    have : NonExpansive Ψ :=
      ⟨fun {n x' y'} (h : Excl.Dist n x' y') =>
        match x', y', h with
        | Excl.excl _, Excl.excl _, h => (ne_r a).ne h
        | Excl.excl _, Excl.invalid, h => h.elim
        | Excl.invalid, Excl.excl _, h => h.elim
        | Excl.invalid, Excl.invalid, _ => Dist.rfl⟩
    exact rewrite' Ψ .rfl refl
  · exact of_internalEquiv_ne Excl.excl

theorem excl_equivI_invalid (O : Type u) [OFE O] :
    internalEq (Excl.invalid : Excl O) Excl.invalid ⊣⊢@{PROP} True :=
  ⟨true_intro, refl⟩

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
    exact rewrite' Ψ .rfl true_intro
  · exact false_elim

theorem excl_equivI_invalid_excl {O : Type u} [OFE O] (a : O) :
    internalEq (Excl.invalid : Excl O) (Excl.excl a) ⊣⊢@{PROP} False :=
  ⟨symm.trans (excl_equivI_excl_invalid a).1, false_elim⟩

@[rocq_alias sig_equivI]
theorem sig_equivI {A : Type u} [OFE A] (P : A → Prop) (x y : Subtype P) :
    internalEq x.val y.val ⊣⊢@{PROP} internalEq x y :=
  ⟨sig_equivI_1 P x y,
   of_internalEquiv_ne Subtype.val⟩

-- TODO: sum_equivI (requires Sum OFE)
-- TODO: sigT_equivI (requires SigmaT OFE)

@[rocq_alias csum_equivI]
theorem csum_equivI {A B : Type u} [OFE A] [OFE B] (sx sy : Csum A B) :
    internalEq sx sy ⊣⊢@{PROP}
      match sx, sy with
      | .inl x, .inl y => internalEq x y
      | .inr x, .inr y => internalEq x y
      | .invalid, .invalid => BIBase.pure True
      | _, _ => BIBase.pure False := by
  constructor
  · let Ψ : Csum A B → PROP := fun sy' =>
      match sx, sy' with
      | .inl x, .inl y => internalEq x y
      | .inr x, .inr y => internalEq x y
      | .invalid, .invalid => BIBase.pure True
      | _, _ => BIBase.pure False
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

private theorem discreteFun_equivI_mp {A : Type u} {B : A → Type u} [OFEFun B]
    (f g : (x : A) → B x) :
    internalEq f g ⊢@{PROP} ∀ x, internalEq (f x) (g x) := by
  let Ψ : ((x : A) → B x) → PROP := fun g => BIBase.forall fun x => internalEq (A := B x) (f x) (g x)
  have : NonExpansive Ψ := ⟨fun {_ _ _} h => sForall_ne ⟨
    fun p ⟨a, ha⟩ => ⟨_, ⟨a, rfl⟩, ha ▸ (ne_r (f a)).ne (h a)⟩,
    fun p ⟨a, ha⟩ => ⟨_, ⟨a, rfl⟩, ha ▸ (ne_r (f a)).ne (h a)⟩⟩⟩
  exact rewrite' Ψ .rfl (forall_intro fun _ => refl)

@[rocq_alias discrete_fun_equivI]
theorem discreteFun_equivI {A : Type u} {B : A → Type u} [OFEFun B]
    (f g : (x : A) → B x) :
    internalEq f g ⊣⊢@{PROP} ∀ x, internalEq (f x) (g x) :=
  ⟨discreteFun_equivI_mp f g, fun_extI f g⟩

private theorem ofeMorO_equivI_mp {A B : Type u} [OFE A] [OFE B] (f g : A -n> B) :
    internalEq f g ⊢@{PROP} ∀ x, internalEq (f x) (g x) := by
  let Ψ : (A -n> B) → PROP := fun g => BIBase.forall fun x => internalEq (A := B) (f x) (g x)
  have : NonExpansive Ψ := ⟨fun {_ _ _} h => sForall_ne ⟨
    fun p ⟨a, ha⟩ => ⟨_, ⟨a, rfl⟩, ha ▸ (ne_r (f a)).ne (h a)⟩,
    fun p ⟨a, ha⟩ => ⟨_, ⟨a, rfl⟩, ha ▸ (ne_r (f a)).ne (h a)⟩⟩⟩
  exact rewrite' Ψ .rfl (forall_intro fun _ => refl)

@[rocq_alias ofe_morO_equivI]
theorem ofeMorO_equivI {A B : Type u} [OFE A] [OFE B] (f g : A -n> B) :
    internalEq f g ⊣⊢@{PROP} ∀ x, internalEq (f x) (g x) :=
  ⟨ofeMorO_equivI_mp f g,
   (discreteFun_equivI (PROP := PROP) f.f g.f).2 |>.trans <|
   (sig_equivI_1 (PROP := PROP) _ ⟨f.f, f.ne⟩ ⟨g.f, g.ne⟩).trans <|
   (let toHom : { f : A → B // NonExpansive f } → (A -n> B) := fun f => ⟨f.val, f.property⟩
    letI _ : NonExpansive toHom := ⟨fun {_ _ _} h => h⟩
    of_internalEquiv_ne toHom)⟩

/-! ## Modalities -/

@[rocq_alias absorbingly_internal_eq]
theorem absorbingly_internalEq {A : Type u} [OFE A] (x y : A) :
    <absorb> internalEq x y ⊣⊢@{PROP} internalEq x y :=
  absorbingly_siPure

@[rocq_alias persistently_internal_eq]
theorem persistently_internalEq {A : Type u} [OFE A] (a b : A) :
    <pers> internalEq a b ⊣⊢@{PROP} internalEq a b :=
  persistently_siPure

@[rocq_alias internal_eq_absorbing]
instance internalEq_absorbing {A : Type u} [OFE A] (x y : A) :
    Absorbing (PROP := PROP) (internalEq x y) where
  absorbing := (absorbingly_internalEq x y).1

@[rocq_alias internal_eq_persistent]
instance internalEq_persistent {A : Type u} [OFE A] (a b : A) :
    Persistent (PROP := PROP) (internalEq a b) where
  persistent := (persistently_internalEq a b).2

/-! ## Equality under a later -/

@[rocq_alias bi.later_equivI_1]
theorem later_equivI_1 {A : Type u} [OFE A] (x y : A) :
    internalEq (PROP := PROP) (Later.next x) (Later.next y) ⊢ ▷ internalEq x y :=
  (siPure_mono (SiProp.later_equiv_internalEq_mp x y)).trans siPure_later.mp

@[rocq_alias bi.later_equivI_2]
theorem later_equivI_2 {A : Type u} [OFE A] (x y : A) :
    ▷ internalEq x y ⊢@{PROP} internalEq (Later.next x) (Later.next y) :=
  siPure_later.mpr.trans (siPure_mono (SiProp.later_equiv_internalEq_mpr x y))

@[rocq_alias later_equivI]
theorem later_equivI {A : Type u} [OFE A] (x y : A) :
    internalEq (PROP := PROP) (Later.next x) (Later.next y) ⊣⊢ ▷ internalEq x y :=
  ⟨later_equivI_1 x y, later_equivI_2 x y⟩

@[rocq_alias f_equivI_contractive]
theorem f_equivI_contractive {A B : Type u} [OFE A] [OFE B]
    (f : A → B) [hf : Contractive f] (x y : A) :
    ▷ internalEq x y ⊢@{PROP} internalEq (f x) (f y) :=
  (later_equivI_2 x y).trans <|
    letI _ : NonExpansive (f ∘ Later.car) := ⟨fun {_ _ _} h => hf.distLater_dist h⟩
    of_internalEquiv_ne (f ∘ Later.car)

@[rocq_alias internal_eq_rewrite_contractive]
theorem internalEq_rewrite_contractive {A : Type u} [OFE A] (a b : A) (Ψ : A → PROP)
    [Contractive Ψ] :
    ▷ internalEq a b ⊢ Ψ a → Ψ b :=
  (f_equivI_contractive Ψ a b).trans (rewrite id)

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
  letI _ := NonExpansive₂.ne_right (BIBase.iff (PROP := PROP)) P
  rewrite' (BIBase.iff P)
    .rfl (and_intro (imp_intro and_elim_r) (imp_intro and_elim_r))

@[rocq_alias affinely_internal_eq_wand_iff]
theorem affinely_internalEq_wandIff (P Q : PROP) :
    <affine> internalEq P Q ⊢ P ∗-∗ Q :=
  letI _ := NonExpansive₂.ne_right (wandIff (PROP := PROP)) P
  rewrite' (wandIff P)
    (affinely_elim.trans .rfl) (affinely_elim_emp.trans wandIff_refl)

@[rocq_alias internal_eq_wand_iff]
theorem internalEq_wandIff (P Q : PROP) :
    internalEq P Q ⊢ <absorb> (P ∗-∗ Q) :=
  absorbingly_affinely_intro_of_persistent.trans
    (absorbingly_mono (affinely_internalEq_wandIff P Q))

@[rocq_alias si_pure_internal_eq]
theorem siPure_internalEq {A : Type u} [OFE A] (x y : A) :
    siPure (SiProp.internalEq x y) ⊣⊢@{PROP} internalEq x y :=
  .rfl

@[rocq_alias prop_ext_si_emp_valid_2]
theorem prop_ext_siEmpValid_2 (P Q : PROP) :
    siEmpValid iprop(P ∗-∗ Q) ⊢@{SiProp} SiProp.internalEq P Q :=
  prop_ext_siEmpValid

@[rocq_alias prop_ext_si_emp_valid]
theorem prop_ext_siEmpValid_equiv (P Q : PROP) :
    SiProp.internalEq P Q ⊣⊢@{SiProp} siEmpValid iprop(P ∗-∗ Q) := by
  refine ⟨?_, prop_ext_siEmpValid⟩
  rw [← siPure_entails (PROP := PROP)]
  show internalEq P Q ⊢@{PROP} siPure (siEmpValid iprop(P ∗-∗ Q))
  letI _ : NonExpansive (fun Q => siPure (PROP := PROP) (siEmpValid iprop(P ∗-∗ Q))) :=
    (Sbi.siPure_ne.comp Sbi.siEmpValid_ne).comp (NonExpansive₂.ne_right wandIff P)
  refine rewrite' (fun Q => siPure (siEmpValid iprop(P ∗-∗ Q))) .rfl ?_
  exact (pure_intro trivial).trans <|
    siPure_pure.mpr.trans <| siPure_mono <| siEmpValid_emp.mpr.trans (siEmpValid_mono wandIff_refl)

@[rocq_alias later_equivI_prop_2]
theorem later_equivI_prop_2 (P Q : PROP) :
    ▷ internalEq P Q ⊢ internalEq (PROP := PROP) (BIBase.later P) (BIBase.later Q) := by
  show iprop(▷ siPure (SiProp.internalEq P Q) ⊢ siPure (SiProp.internalEq (BIBase.later P) (BIBase.later Q)))
  calc iprop(▷ siPure (SiProp.internalEq P Q))
    _ ⊢ siPure (BIBase.later (SiProp.internalEq P Q)) := siPure_later.mpr
    _ ⊢ siPure (BIBase.later (siEmpValid iprop(P ∗-∗ Q))) :=
        siPure_mono (later_mono (prop_ext_siEmpValid_equiv P Q).mp)
    _ ⊢ siPure (siEmpValid iprop(▷ (P ∗-∗ Q))) := siPure_mono siEmpValid_later.mpr
    _ ⊢ siPure (siEmpValid iprop(▷ P ∗-∗ ▷ Q)) := siPure_mono (siEmpValid_mono later_wand_iff)
    _ ⊢ siPure (SiProp.internalEq (BIBase.later P) (BIBase.later Q)) :=
        siPure_mono (prop_ext_siEmpValid_equiv _ _).mpr

@[rocq_alias bi.internal_eq_soundness]
theorem internalEq_soundness {A : Type u} [OFE A] (x y : A) :
    (⊢@{PROP} internalEq x y) → x ≡ y :=
  fun h => SiProp.internalEq_soundness ((siPure_emp_valid (PROP := PROP)).mp h)

/-! ## Derive NonExpansive/Contractive from internal statements -/

@[rocq_alias bi.internal_eq_entails]
theorem internalEq_entails {A B : Type u} [OFE A] [OFE B] (a₁ a₂ : A) (b₁ b₂ : B) :
    (internalEq a₁ a₂ ⊢@{PROP} internalEq b₁ b₂) ↔
      (∀ n, a₁ ≡{n}≡ a₂ → b₁ ≡{n}≡ b₂) :=
  (siPure_entails (PROP := PROP)).trans (SiProp.internalEq_entails a₁ a₂ b₁ b₂)

@[rocq_alias ne_internal_eq]
theorem ne_internalEq {A B : Type u} [OFE A] [OFE B] (f : A → B) :
    NonExpansive f ↔ (∀ x₁ x₂, internalEq x₁ x₂ ⊢@{PROP} internalEq (f x₁) (f x₂)) :=
  ⟨fun ⟨hne⟩ x₁ x₂ => (internalEq_entails x₁ x₂ (f x₁) (f x₂)).mpr (fun _ h => hne h),
   fun h => ⟨fun {_ _ _} hx => (internalEq_entails _ _ _ _).mp (h _ _) _ hx⟩⟩

@[rocq_alias ne_2_internal_eq]
theorem ne_2_internalEq {A B C : Type u} [OFE A] [OFE B] [OFE C] (f : A → B → C) :
    NonExpansive₂ f ↔
      (∀ x₁ x₂ y₁ y₂, internalEq x₁ x₂ ∧ internalEq y₁ y₂ ⊢@{PROP}
        internalEq (f x₁ y₁) (f x₂ y₂)) := by
  constructor
  · intro hf x₁ x₂ y₁ y₂
    letI _ := hf.uncurry
    exact (prod_equivI (PROP := PROP) (x₁, y₁) (x₂, y₂) |>.2).trans
      (of_internalEquiv_ne (Function.uncurry f))
  · intro hf
    exact ⟨fun {_ x₁ x₂} hx {y₁ y₂} hy =>
      (internalEq_entails (x₁, y₁) (x₂, y₂) (f x₁ y₁) (f x₂ y₂)).mp
        (prod_equivI _ _ |>.1 |>.trans (hf _ _ _ _)) _ (dist_prod_ext hx hy)⟩

@[rocq_alias contractive_internal_eq]
theorem contractive_internalEq {A B : Type u} [OFE A] [OFE B] (f : A → B) :
    Contractive f ↔
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

end datatypes

end internalEqLaws

end Iris.BI
