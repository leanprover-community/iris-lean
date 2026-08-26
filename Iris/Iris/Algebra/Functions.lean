/-
Copyright (c) 2026 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
module

public import Iris.Algebra.Updates

@[expose] public section

namespace Iris

variable {SI : Type _} [instSI : SIdx SI]
local stepindex SI
open OFE CMRA

/-!
# Dependent Function Resources

Insertion and singleton operations for dependent functions whose codomains carry
OFE or CMRA structure, together with their non-expansiveness, validity, core,
composition, and update laws.
-/

@[rocq_alias discrete_fun_insert]
def discreteFunInsert {ι : Type _} [DecidableEq ι] {β : ι → Type _}
    (x : ι) (y : β x) (f : (a : ι) → β a) : (a : ι) → β a :=
  fun x' => if h : x = x' then h ▸ y else f x'

@[rocq_alias discrete_fun_singleton]
def discreteFunSingleton {ι : Type _} [DecidableEq ι] {β : ι → Type _}
    [∀ i, UCMRA (β i)] (x : ι) (y : β x) : (a : ι) → β a :=
  discreteFunInsert x y fun _ => unit

section insert

variable {ι : Type _} [DecidableEq ι] {β : ι → Type _}

@[rocq_alias discrete_fun_lookup_insert, simp]
theorem discreteFunInsert_self (f : (a : ι) → β a) (x : ι) (y : β x) :
    discreteFunInsert x y f x = y := by
  simp [discreteFunInsert]

@[rocq_alias discrete_fun_lookup_insert_ne, simp]
theorem discreteFunInsert_of_ne (f : (a : ι) → β a) (x x' : ι)
    (y : β x) (h : x ≠ x') : discreteFunInsert x y f x' = f x' := by
  simp [discreteFunInsert, h]

end insert

section OFE

variable {ι : Type _} [DecidableEq ι] {β : ι → Type _} [∀ i, OFE (β i)]

@[rocq_alias discrete_funO_ofe_discrete]
instance instDiscreteFunOfeDiscrete [∀ i, OFE.Discrete (β i)] :
    OFE.Discrete ((i : ι) → β i) where
  discrete_0 h := funext fun i => discrete_0 (h i)

omit [DecidableEq ι] in
/-- Not an instance, cycle with `discreteE_apply`. -/
theorem discreteE_pi {f : (a : ι) → β a} (hf : ∀ i, DiscreteE (f i)) : DiscreteE f where
  discrete h := funext fun i => (hf i).discrete (h i)

@[rocq_alias discrete_fun_insert_ne]
instance instDiscreteFunInsertNonExpansive (x : ι) :
    NonExpansive₂ (discreteFunInsert (β := β) x) where
  ne {n y₁ y₂} hy {f₁ f₂} hf x' := by
    by_cases h : x = x'
    · subst h
      simpa using hy
    · rw [discreteFunInsert_of_ne (h := h) .., discreteFunInsert_of_ne (h := h) ..]
      exact hf x'

#rocq_ignore discrete_fun_insert_proper "Use the NonExpansive instance instead."

/-- Not an instance, cycle with `discreteE_pi`. -/
theorem discreteE_apply {f : (a : ι) → β a} (hf : DiscreteE f) (x : ι) :
    DiscreteE (f x) where
  discrete {y} h := by
    have hfun : f ≡{0}≡ discreteFunInsert x y f := fun x' => by
      by_cases hxx' : x = x'
      · subst hxx'
        simpa using h
      · rw [discreteFunInsert_of_ne (h := hxx') ..]; exact .rfl
    exact (congrFun (hf.discrete hfun) x).trans (discreteFunInsert_self ..)

@[rocq_alias discrete_fun_insert_discrete]
instance instDiscreteFunInsertDiscrete (f : (a : ι) → β a) (x : ι) (y : β x)
    [DiscreteE f] [DiscreteE y] : DiscreteE (discreteFunInsert x y f) :=
  discreteE_pi fun x' => by
    by_cases h : x = x'
    · subst h
      rw [discreteFunInsert_self]
      infer_instance
    · rw [discreteFunInsert_of_ne (h := h) ..]
      exact discreteE_apply ‹DiscreteE f› x'

end OFE

section CMRA

variable {ι : Type _} [DecidableEq ι] {β : ι → Type _} [∀ i, UCMRA (β i)]

@[rocq_alias discrete_funR_cmra_discrete]
instance instDiscreteFunCmraDiscrete [∀ i, CMRA.Discrete (β i)] :
    CMRA.Discrete ((i : ι) → β i) where
  discrete_valid h i := CMRA.Discrete.discrete_valid (h i)

@[rocq_alias discrete_fun_singleton_ne]
instance instDiscreteFunSingletonNonExpansive (x : ι) :
    NonExpansive (discreteFunSingleton (β := β) x) where
  ne {_ _ _} h := instDiscreteFunInsertNonExpansive x |>.ne h .rfl

#rocq_ignore discrete_fun_singleton_proper "Use NonExpansive instance instead."

@[rocq_alias discrete_fun_lookup_singleton, simp]
theorem discreteFunSingleton_self {x : ι} (y : β x) :
    discreteFunSingleton x y x = y := discreteFunInsert_self ..

@[rocq_alias discrete_fun_lookup_singleton_ne, simp]
theorem discreteFunSingleton_of_ne {x x' : ι} (y : β x) (h : x ≠ x') :
    discreteFunSingleton x y x' = unit :=
  discreteFunInsert_of_ne (h := h) ..

@[rocq_alias discrete_fun_singleton_discrete]
instance instDiscreteFunSingletonDiscrete {x : ι} (y : β x)
    [∀ i, DiscreteE (unit : β i)] [DiscreteE y] :
    DiscreteE (discreteFunSingleton x y) :=
  haveI : DiscreteE fun i : ι => (unit : β i) := discreteE_pi fun _ => inferInstance
  instDiscreteFunInsertDiscrete (fun _ => unit) x y

@[rocq_alias discrete_fun_singleton_validN]
theorem discreteFunSingleton_validN_iff (n : SI) {x : ι} (y : β x) :
    ✓{n} discreteFunSingleton x y ↔ ✓{n} y := by
  constructor
  · exact fun h => discreteFunSingleton_self y ▸ h x
  · intro hy x'
    by_cases h : x = x'
    · subst h
      rw [discreteFunSingleton_self]
      exact hy
    · rw [discreteFunSingleton_of_ne y h]
      exact unit_validN

@[rocq_alias discrete_fun_singleton_valid]
theorem discreteFunSingleton_valid_iff {x : ι} (y : β x) :
    ✓ discreteFunSingleton x y ↔ ✓ y := by
  rw [valid_iff_validN, valid_iff_validN]
  exact forall_congr' fun n => discreteFunSingleton_validN_iff ..

@[rocq_alias discrete_fun_singleton_unit]
theorem discreteFunSingleton_unit_eq (x : ι) :
    discreteFunSingleton x (unit : β x) = (unit : (a : ι) → β a) :=
  funext fun x' => by
    by_cases h : x = x'
    · subst h
      rw [discreteFunSingleton_self]
      rfl
    · rw [discreteFunSingleton_of_ne _ h]
      rfl

@[rocq_alias discrete_fun_singleton_core]
theorem discreteFunSingleton_core_eq {x : ι} (y : β x) :
    core (discreteFunSingleton x y) = discreteFunSingleton x (core y) :=
  funext fun x' => by
    simp only [core, CMRA.pcore, Option.getD_some]
    by_cases h : x = x'
    · subst h
      rw [discreteFunSingleton_self, discreteFunSingleton_self]
    · rw [discreteFunSingleton_of_ne y h, discreteFunSingleton_of_ne _ h]
      exact core_eqv_self unit

@[rocq_alias discrete_fun_singleton_core_id]
instance instDiscreteFunSingletonCoreId (x : ι) (y : β x) [CoreId y] :
    CoreId (discreteFunSingleton x y) :=
  coreId_iff_core_eqv_self.mpr <| (discreteFunSingleton_core_eq y).trans
    (congrArg (discreteFunSingleton x) (core_eqv_self y))

@[rocq_alias discrete_fun_singleton_op]
theorem discreteFunSingleton_op_eq {x : ι} (y₁ y₂ : β x) :
    discreteFunSingleton x y₁ • discreteFunSingleton x y₂ =
      discreteFunSingleton x (y₁ • y₂) :=
  funext fun x' => by
    simp only [CMRA.op]
    by_cases h : x = x'
    · subst h
      rw [discreteFunSingleton_self, discreteFunSingleton_self, discreteFunSingleton_self]
    · rw [discreteFunSingleton_of_ne y₁ h, discreteFunSingleton_of_ne y₂ h,
        discreteFunSingleton_of_ne _ h]
      exact unit_left_id

@[rocq_alias discrete_fun_insert_updateP]
theorem discreteFunInsert_updateP {x : ι} {P : β x → Prop} {Q : ((a : ι) → β a) → Prop}
    {g : (a : ι) → β a} {y₁ : β x} (hy : y₁ ~~>: P)
    (hQ : ∀ y₂, P y₂ → Q (discreteFunInsert x y₂ g)) :
    discreteFunInsert x y₁ g ~~>: Q := by
  refine UpdateP.total.mpr fun n gf hgf => ?_
  have hgf_at (a : ι) : ✓{n} discreteFunInsert x y₁ g a • gf a := hgf a
  obtain ⟨y₂, hy₂, hvalid⟩ := hy n (some (gf x))
    (by simpa only [CMRA.op?, discreteFunInsert_self] using hgf_at x)
  refine ⟨discreteFunInsert x y₂ g, hQ y₂ hy₂, fun x' => ?_⟩
  simp only [CMRA.op]
  by_cases hx'x : x' = x
  · subst x'
    simpa only [CMRA.op?, discreteFunInsert_self]
  · simpa only [discreteFunInsert_of_ne (h := Ne.symm hx'x) ..] using hgf_at x'

@[rocq_alias discrete_fun_insert_updateP']
theorem discreteFunInsert_updateP' {x : ι} {P : β x → Prop} (g : (a : ι) → β a)
    {y₁ : β x} (hy : y₁ ~~>: P) :
    discreteFunInsert x y₁ g ~~>: fun g' => ∃ y₂, g' = discreteFunInsert x y₂ g ∧ P y₂ :=
  discreteFunInsert_updateP hy fun y₂ hy₂ => ⟨y₂, rfl, hy₂⟩

@[rocq_alias discrete_fun_insert_update]
theorem discreteFunInsert_update (g : (a : ι) → β a) {x : ι} {y₁ y₂ : β x} (hy : y₁ ~~> y₂) :
    discreteFunInsert x y₁ g ~~> discreteFunInsert x y₂ g :=
  Update.of_updateP <| discreteFunInsert_updateP (UpdateP.of_update hy) fun _ hy₂ => hy₂ ▸ rfl

@[rocq_alias discrete_fun_singleton_updateP]
theorem discreteFunSingleton_updateP {x : ι} {P : β x → Prop} (Q : ((a : ι) → β a) → Prop)
    {y₁ : β x} (hy : y₁ ~~>: P) (hQ : ∀ y₂, P y₂ → Q (discreteFunSingleton x y₂)) :
    discreteFunSingleton x y₁ ~~>: Q :=
  discreteFunInsert_updateP hy hQ

@[rocq_alias discrete_fun_singleton_updateP']
theorem discreteFunSingleton_updateP' {x : ι} {P : β x → Prop}
    {y₁ : β x} (hy : y₁ ~~>: P) :
    discreteFunSingleton x y₁ ~~>: fun g => ∃ y₂, g = discreteFunSingleton x y₂ ∧ P y₂ :=
  discreteFunSingleton_updateP _ hy fun y₂ hy₂ => ⟨y₂, rfl, hy₂⟩

@[rocq_alias discrete_fun_singleton_update]
theorem discreteFunSingleton_update {x : ι} {y₁ y₂ : β x} (hy : y₁ ~~> y₂) :
    discreteFunSingleton x y₁ ~~> discreteFunSingleton x y₂ :=
  discreteFunInsert_update _ hy

@[rocq_alias discrete_fun_singleton_updateP_empty]
theorem discreteFunSingleton_updateP_unit {x : ι} {P : β x → Prop}
    {Q : ((a : ι) → β a) → Prop} (hy : unit ~~>: P)
    (hQ : ∀ y₂, P y₂ → Q (discreteFunSingleton x y₂)) : unit ~~>: Q :=
  discreteFunSingleton_unit_eq (β := β) x ▸ discreteFunSingleton_updateP Q hy hQ

@[rocq_alias discrete_fun_singleton_updateP_empty']
theorem discreteFunSingleton_updateP_unit' {x : ι} {P : β x → Prop}
    (hy : (unit : β x) ~~>: P) :
    unit ~~>: fun g => ∃ y₂, g = discreteFunSingleton x y₂ ∧ P y₂ :=
  discreteFunSingleton_updateP_unit hy fun y₂ hy₂ => ⟨y₂, rfl, hy₂⟩

@[rocq_alias discrete_fun_singleton_update_empty]
theorem discreteFunSingleton_update_unit {x : ι} {y : β x} (hy : unit ~~> y) :
    unit ~~> discreteFunSingleton x y :=
  Update.of_updateP <|
    discreteFunSingleton_updateP_unit (UpdateP.of_update hy) <| fun _ hz => hz ▸ rfl

end CMRA

section CMRA

variable {ι : Type _} {β : ι → Type _} [∀ i, UCMRA (β i)]

@[rocq_alias discrete_fun_updateP]
theorem discreteFun_updateP {f : (a : ι) → β a} {P : (a : ι) → β a → Prop}
    {Q : ((a : ι) → β a) → Prop} (hf : ∀ a, f a ~~>: P a)
    (hQ : ∀ f', (∀ a, P a (f' a)) → Q f') : f ~~>: Q := by
  refine UpdateP.total.mpr fun n g hfg => ?_
  obtain ⟨f', hf'⟩ := Classical.axiomOfChoice fun a => hf a n (some (g a)) (hfg a)
  exact ⟨f', hQ f' fun a => (hf' a).1, fun a => (hf' a).2⟩

@[rocq_alias discrete_fun_updateP']
theorem discreteFun_updateP' {f : (a : ι) → β a} {P : (a : ι) → β a → Prop}
    (hf : ∀ a, f a ~~>: P a) : f ~~>: fun f' => ∀ a, P a (f' a) :=
  discreteFun_updateP hf fun _ h => h

@[rocq_alias discrete_fun_update]
theorem discreteFun_update {f g : (a : ι) → β a} (hfg : ∀ a, f a ~~> g a) : f ~~> g :=
  Update.of_updateP <| discreteFun_updateP (fun a => UpdateP.of_update (hfg a))
    fun _ h => funext h

end CMRA

end Iris
