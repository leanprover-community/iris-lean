/-
Copyright (c) 2026 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
module

public import Iris.Algebra.Updates
meta import Iris.Std.RocqPorting

@[expose] public section

namespace Iris
open OFE CMRA

/-!
# Dependent Function Resources

Insertion and singleton operations for dependent functions whose codomains carry
OFE or CMRA structure, together with their non-expansiveness, validity, core,
composition, and update laws.
-/

@[rocq_alias discrete_fun_insert]
def discreteFunInsert {ι : Type _} [DecidableEq ι] {β : ι → Type _}
    [∀ i, OFE (β i)]
    (x : ι) (y : β x) (f : (a : ι) → β a) : (a : ι) → β a :=
  fun x' => if h : x = x' then h ▸ y else f x'

@[rocq_alias discrete_fun_singleton]
def discreteFunSingleton {ι : Type _} [DecidableEq ι] {β : ι → Type _}
    [∀ i, UCMRA (β i)] (x : ι) (y : β x) : (a : ι) → β a :=
  discreteFunInsert x y fun _ => unit

section OFE

variable {ι : Type _} [DecidableEq ι] {β : ι → Type _} [∀ i, OFE (β i)]

@[rocq_alias discrete_funO_ofe_discrete]
instance instDiscreteFunOfeDiscrete [∀ i, OFE.Discrete (β i)] :
    OFE.Discrete ((i : ι) → β i) where
  discrete_0 h _ i := (OFE.Discrete.discrete_0 (h i)).dist

private instance instDiscreteFunDiscreteE (f : (a : ι) → β a)
    [∀ i, DiscreteE (f i)] : DiscreteE f where
  discrete h _ i := (DiscreteE.discrete (h i)).dist

@[rocq_alias discrete_fun_insert_ne]
instance instDiscreteFunInsertNonExpansive (x : ι) :
    NonExpansive₂ (discreteFunInsert (β := β) x) where
  ne {n y₁ y₂} hy {f₁ f₂} hf x' := by
    simp only [discreteFunInsert]
    split <;> subst_vars <;> first | exact hy | exact hf x'

#rocq_ignore discrete_fun_insert_proper "Subsumed by Iris.instDiscreteFunInsertNonExpansive."

@[rocq_alias discrete_fun_lookup_insert]
theorem discrete_fun_lookup_insert (f : (a : ι) → β a) (x : ι) (y : β x) :
    discreteFunInsert x y f x = y := by
  simp [discreteFunInsert]

@[rocq_alias discrete_fun_lookup_insert_ne]
theorem discrete_fun_lookup_insert_ne (f : (a : ι) → β a) (x x' : ι)
    (y : β x)
    (h : x ≠ x') : discreteFunInsert x y f x' = f x' := by
  simp [discreteFunInsert, h]

private theorem discreteE_apply (f : (a : ι) → β a) [DiscreteE f] (x : ι) :
    DiscreteE (f x) where
  discrete {y} h n := by
    have hfun : f ≡{0}≡ discreteFunInsert x y f := by
      intro x'
      by_cases hxx' : x = x'
      · subst x'
        rw [discrete_fun_lookup_insert]
        exact h
      · rw [discrete_fun_lookup_insert_ne (h := hxx') ..]
    simpa only [discrete_fun_lookup_insert] using
      DiscreteE.discrete hfun n x

@[rocq_alias discrete_fun_insert_discrete]
instance instDiscreteFunInsertDiscrete (f : (a : ι) → β a) (x : ι)
    (y : β x)
    [DiscreteE f] [DiscreteE y] : DiscreteE (discreteFunInsert x y f) := by
  letI : ∀ i, DiscreteE (discreteFunInsert x y f i) := fun x' => by
    simp only [discreteFunInsert]
    split <;> subst_vars <;>
      first | infer_instance | exact discreteE_apply f x'
  exact instDiscreteFunDiscreteE ..

end OFE

section CMRA

variable {ι : Type _} [DecidableEq ι] {β : ι → Type _}
    [∀ i, UCMRA (β i)]

@[rocq_alias discrete_funR_cmra_discrete]
instance instDiscreteFunCmraDiscrete [∀ i, CMRA.Discrete (β i)] :
    CMRA.Discrete ((i : ι) → β i) where
  discrete_valid h i := CMRA.Discrete.discrete_valid (h i)

@[rocq_alias discrete_fun_singleton_ne]
instance instDiscreteFunSingletonNonExpansive (x : ι) :
    NonExpansive (discreteFunSingleton (β := β) x) where
  ne {_ _ _} h := instDiscreteFunInsertNonExpansive x |>.ne h .rfl

#rocq_ignore discrete_fun_singleton_proper "Subsumed by Iris.instDiscreteFunSingletonNonExpansive."

@[rocq_alias discrete_fun_lookup_singleton]
theorem discrete_fun_lookup_singleton (x : ι) (y : β x) :
    discreteFunSingleton x y x = y := discrete_fun_lookup_insert ..

@[rocq_alias discrete_fun_lookup_singleton_ne]
theorem discrete_fun_lookup_singleton_ne (x x' : ι) (y : β x) (h : x ≠ x') :
    discreteFunSingleton x y x' = (unit : β x') :=
  discrete_fun_lookup_insert_ne (h := h) ..

@[rocq_alias discrete_fun_singleton_discrete]
instance instDiscreteFunSingletonDiscrete (x : ι) (y : β x)
    [∀ i, DiscreteE (unit : β i)] [DiscreteE y] :
    DiscreteE (discreteFunSingleton x y) :=
  instDiscreteFunInsertDiscrete (fun _ => unit) x y

@[rocq_alias discrete_fun_singleton_validN]
theorem discrete_fun_singleton_validN_iff (n : Nat) (x : ι) (y : β x) :
    ✓{n} discreteFunSingleton x y ↔ ✓{n} y := by
  constructor
  · exact fun h => discrete_fun_lookup_singleton x y ▸ h x
  · intro hy x'
    simp only [discreteFunSingleton, discreteFunInsert]
    split <;> subst_vars <;> first | exact hy | exact unit_validN

@[rocq_alias discrete_fun_singleton_valid]
theorem discrete_fun_singleton_valid_iff (x : ι) (y : β x) :
    ✓ discreteFunSingleton x y ↔ ✓ y := by
  rw [valid_iff_validN, valid_iff_validN]
  exact forall_congr' fun n => discrete_fun_singleton_validN_iff ..

@[rocq_alias discrete_fun_singleton_unit]
theorem discrete_fun_singleton_unit_equiv (x : ι) :
    discreteFunSingleton x (unit : β x) ≡ (unit : (a : ι) → β a) := by
  intro n x'
  change discreteFunSingleton x (unit : β x) x' ≡{n}≡ (unit : β x')
  simp only [discreteFunSingleton, discreteFunInsert]
  split <;> subst_vars <;> exact .rfl

@[rocq_alias discrete_fun_singleton_core]
theorem discrete_fun_singleton_core_equiv (x : ι) (y : β x) :
    core (discreteFunSingleton x y) ≡ discreteFunSingleton x (core y) := by
  intro n x'
  change core (discreteFunSingleton x y x') ≡{n}≡
    discreteFunSingleton x (core y) x'
  simp only [discreteFunSingleton, discreteFunInsert]
  split <;> subst_vars <;>
    first | exact .rfl | exact (core_eqv_self (unit : β x')).dist

@[rocq_alias discrete_fun_singleton_core_id]
instance instDiscreteFunSingletonCoreId (x : ι) (y : β x) [CoreId y] :
    CoreId (discreteFunSingleton x y) :=
  coreId_iff_core_eqv_self.mpr <| (discrete_fun_singleton_core_equiv x y).trans
    (NonExpansive.eqv (core_eqv_self y))

@[rocq_alias discrete_fun_singleton_op]
theorem discrete_fun_singleton_op_equiv (x : ι) (y₁ y₂ : β x) :
    discreteFunSingleton x y₁ • discreteFunSingleton x y₂ ≡
      discreteFunSingleton x (y₁ • y₂) := by
  intro n x'
  change discreteFunSingleton x y₁ x' •
    discreteFunSingleton x y₂ x' ≡{n}≡
      discreteFunSingleton x (y₁ • y₂) x'
  simp only [discreteFunSingleton, discreteFunInsert]
  split <;> subst_vars <;> first | exact .rfl | exact unit_left_id.dist

@[rocq_alias discrete_fun_insert_updateP]
theorem discrete_fun_insert_update_p (x : ι) (P : β x → Prop)
    (Q : ((a : ι) → β a) → Prop) (g : (a : ι) → β a) (y₁ : β x)
    (hy : y₁ ~~>: P)
    (hQ : ∀ y₂, P y₂ → Q (discreteFunInsert x y₂ g)) :
    discreteFunInsert x y₁ g ~~>: Q := by
  refine UpdateP.total.mpr fun n gf hgf => ?_
  change (∀ a, ✓{n} discreteFunInsert x y₁ g a • gf a) at hgf
  obtain ⟨y₂, hy₂, hvalid⟩ :=
    hy n (some (gf x)) (by
      change ✓{n} y₁ • gf x
      simpa only [discrete_fun_lookup_insert] using hgf x)
  refine ⟨discreteFunInsert x y₂ g, hQ y₂ hy₂, fun x' => ?_⟩
  change ✓{n} discreteFunInsert x y₂ g x' • gf x'
  by_cases hx'x : x' = x
  · subst x'
    rw [discrete_fun_lookup_insert]
    exact hvalid
  · simpa only [discrete_fun_lookup_insert_ne (h := Ne.symm hx'x) ..] using
      hgf x'

@[rocq_alias discrete_fun_insert_updateP']
theorem discrete_fun_insert_update_p' (x : ι) (P : β x → Prop)
    (g : (a : ι) → β a) (y₁ : β x) (hy : y₁ ~~>: P) :
    discreteFunInsert x y₁ g ~~>:
      fun g' => ∃ y₂, g' = discreteFunInsert x y₂ g ∧ P y₂ :=
  discrete_fun_insert_update_p x P _ g y₁ hy fun y₂ hy₂ =>
    ⟨y₂, rfl, hy₂⟩

@[rocq_alias discrete_fun_insert_update]
theorem discrete_fun_insert_update (g : (a : ι) → β a) (x : ι)
    (y₁ y₂ : β x)
    (hy : y₁ ~~> y₂) :
    discreteFunInsert x y₁ g ~~> discreteFunInsert x y₂ g :=
  Update.of_updateP <| discrete_fun_insert_update_p x _ _ g y₁
    (UpdateP.of_update hy) fun _ hy₂ => hy₂ ▸ rfl

@[rocq_alias discrete_fun_singleton_updateP]
theorem discrete_fun_singleton_update_p (x : ι) (P : β x → Prop)
    (Q : ((a : ι) → β a) → Prop) (y₁ : β x) (hy : y₁ ~~>: P)
    (hQ : ∀ y₂, P y₂ → Q (discreteFunSingleton x y₂)) :
    discreteFunSingleton x y₁ ~~>: Q :=
  discrete_fun_insert_update_p x P Q _ y₁ hy hQ

@[rocq_alias discrete_fun_singleton_updateP']
theorem discrete_fun_singleton_update_p' (x : ι) (P : β x → Prop)
    (y₁ : β x) (hy : y₁ ~~>: P) :
    discreteFunSingleton x y₁ ~~>:
      fun g => ∃ y₂, g = discreteFunSingleton x y₂ ∧ P y₂ :=
  discrete_fun_singleton_update_p x P _ y₁ hy fun y₂ hy₂ =>
    ⟨y₂, rfl, hy₂⟩

@[rocq_alias discrete_fun_singleton_update]
theorem discrete_fun_singleton_update (x : ι) (y₁ y₂ : β x)
    (hy : y₁ ~~> y₂) :
    discreteFunSingleton x y₁ ~~> discreteFunSingleton x y₂ :=
  discrete_fun_insert_update _ x y₁ y₂ hy

@[rocq_alias discrete_fun_singleton_updateP_empty]
theorem discrete_fun_singleton_update_p_unit (x : ι) (P : β x → Prop)
    (Q : ((a : ι) → β a) → Prop) (hy : (unit : β x) ~~>: P)
    (hQ : ∀ y₂, P y₂ → Q (discreteFunSingleton x y₂)) :
    (unit : (a : ι) → β a) ~~>: Q :=
  UpdateP.equiv_left (discrete_fun_singleton_unit_equiv x) <|
    discrete_fun_singleton_update_p x P Q unit hy hQ

@[rocq_alias discrete_fun_singleton_updateP_empty']
theorem discrete_fun_singleton_update_p_unit' (x : ι) (P : β x → Prop)
    (hy : (unit : β x) ~~>: P) :
    (unit : (a : ι) → β a) ~~>:
      fun g => ∃ y₂, g = discreteFunSingleton x y₂ ∧ P y₂ :=
  discrete_fun_singleton_update_p_unit x P _ hy fun y₂ hy₂ =>
    ⟨y₂, rfl, hy₂⟩

@[rocq_alias discrete_fun_singleton_update_empty]
theorem discrete_fun_singleton_update_unit (x : ι) (y : β x)
    (hy : (unit : β x) ~~> y) :
    (unit : (a : ι) → β a) ~~> discreteFunSingleton x y :=
  Update.of_updateP <|
    discrete_fun_singleton_update_p_unit x _ _ (UpdateP.of_update hy) <|
      fun _ hz => hz ▸ rfl

end CMRA

section CMRA

variable {ι : Type _} {β : ι → Type _} [∀ i, UCMRA (β i)]

@[rocq_alias discrete_fun_updateP]
theorem discrete_fun_update_p (f : (a : ι) → β a)
    (P : (a : ι) → β a → Prop) (Q : ((a : ι) → β a) → Prop)
    (hf : ∀ a, f a ~~>: P a) (hQ : ∀ f', (∀ a, P a (f' a)) → Q f') :
    f ~~>: Q := by
  refine UpdateP.total.mpr fun n g hfg => ?_
  have hchoice : ∀ a, ∃ y, P a y ∧ ✓{n} y • g a := fun a =>
    hf a n (some (g a)) (hfg a)
  let f' : (a : ι) → β a := fun a => Classical.choose (hchoice a)
  refine ⟨f', hQ f' ?_, ?_⟩
  · exact fun a => (Classical.choose_spec (hchoice a)).1
  · exact fun a => (Classical.choose_spec (hchoice a)).2

@[rocq_alias discrete_fun_updateP']
theorem discrete_fun_update_p' (f : (a : ι) → β a)
    (P : (a : ι) → β a → Prop) (hf : ∀ a, f a ~~>: P a) :
    f ~~>: fun f' => ∀ a, P a (f' a) :=
  discrete_fun_update_p f P _ hf fun _ h => h

@[rocq_alias discrete_fun_update]
theorem discrete_fun_update (f g : (a : ι) → β a)
    (hfg : ∀ a, f a ~~> g a) :
    f ~~> g := fun n mh v a =>
  match mh with
  | none => hfg a n none (v a)
  | some h => hfg a n (some (h a)) (v a)

end CMRA

end Iris
