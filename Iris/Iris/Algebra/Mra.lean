/-
Copyright (c) 2026 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
module

public import Iris.Algebra.LocalUpdates
public import Iris.Std.Classes
meta import Iris.Std.RocqPorting

/-!
# Monotone resource algebras

Given a relation `R` on `α`, the monotone resource algebra records finite collections of
elements up to agreement on the elements lying below them. The principal element `toMra a`
embeds `a`; for preorders, the resource-algebra inclusion order between principal elements
coincides with `R`.
-/

@[expose] public section

namespace Iris

open CMRA Iris.Std OFE

def mraBelowList (R : α → α → Prop) (a : α) (xs : List α) : Prop :=
  ∃ b, b ∈ xs ∧ R a b

def mraListEquiv (R : α → α → Prop) (xs ys : List α) : Prop :=
  ∀ a, mraBelowList R a xs ↔ mraBelowList R a ys

theorem mra_list_equiv_equivalence (R : α → α → Prop) :
    Equivalence (mraListEquiv R) where
  refl _ _ := Iff.rfl
  symm h a := (h a).symm
  trans h₁ h₂ a := (h₁ a).trans (h₂ a)

def mraSetoid (R : α → α → Prop) : Setoid (List α) where
  r := mraListEquiv R
  iseqv := mra_list_equiv_equivalence R

abbrev MraRepr {α : Type _} (R : α → α → Prop) := Quotient (mraSetoid R)

@[rocq_alias mra]
structure Mra {α : Type _} (R : α → α → Prop) where
  repr : MraRepr R

namespace Mra

variable {α : Type _} {R : α → α → Prop}

/-- A type equipped with a distinguished binary relation. -/
class HasEquiv (α : Type _) where
  equiv : α → α → Prop

/-- A function preserving a relation between its domain and codomain. -/
class RelHom (S : α → α → Prop) (T : β → β → Prop) (f : α → β) : Prop where
  map_rel {a b} : S a b → T (f a) (f b)

/-- A binary function preserving relations in both arguments. -/
class RelHom₂ (S : α → α → Prop) (T : β → β → Prop) (U : γ → γ → Prop)
    (f : α → β → γ) : Prop where
  map_rel {a a' b b'} : S a a' → T b b' → U (f a b) (f a' b')

/-- A function reflecting a codomain relation back to its domain. -/
class RelInjective (S : α → α → Prop) (T : β → β → Prop) (f : α → β) : Prop where
  injective {a b} : T (f a) (f b) → S a b

/-- A setoid's equivalence is a distinguished binary relation. -/
instance (priority := low) instHasEquivOfSetoid [s : Setoid α] : HasEquiv α where
  equiv := (· ≈ ·)

/-- Every binary relation respects equality in both arguments. -/
instance instRelHom₂EqIff (R : α → α → Prop) :
    RelHom₂ (fun a b : α ↦ a = b) (fun a b : α ↦ a = b) Iff R where
  map_rel h₁ h₂ := h₁ ▸ h₂ ▸ Iff.rfl

@[rocq_alias to_mra]
def toMra (a : α) : Mra R := ⟨Quotient.mk _ [a]⟩

@[rocq_alias mra_below]
def below (a : α) (x : Mra R) : Prop :=
  Quotient.lift (mraBelowList R a) (by
    intro xs ys h
    change mraListEquiv R xs ys at h
    exact propext (h a)) x.repr

@[rocq_alias mra_below_to_mra]
theorem below_to_mra (a b : α) : below a (toMra (R := R) b) ↔ R a b :=
  ⟨fun ⟨_, hc, hac⟩ ↦ List.mem_singleton.mp hc ▸ hac,
    fun hab ↦ ⟨b, List.mem_singleton_self b, hab⟩⟩

#rocq_ignore mra_equiv
  "Subsumed by the equality-based `COFE (Mra R)` instance on the quotient representation."
#rocq_ignore mra_equiv_equiv
  "Subsumed by `OFE.equiv_eqv`; Lean's `Equivalence` is not a typeclass."

@[rocq_alias mraO]
instance (R : α → α → Prop) : COFE (Mra R) := COFE.ofDiscrete _

theorem below_list_append (a : α) (xs ys : List α) :
    mraBelowList R a (xs ++ ys) ↔ mraBelowList R a xs ∨ mraBelowList R a ys := by
  constructor
  · rintro ⟨b, hb, hab⟩
    exact (List.mem_append.mp hb).elim
      (fun h ↦ .inl ⟨b, h, hab⟩) (fun h ↦ .inr ⟨b, h, hab⟩)
  · rintro (⟨b, hb, hab⟩ | ⟨b, hb, hab⟩)
    · exact ⟨b, List.mem_append.mpr (.inl hb), hab⟩
    · exact ⟨b, List.mem_append.mpr (.inr hb), hab⟩

theorem list_equiv_append {xs xs' ys ys' : List α}
    (hx : mraListEquiv R xs xs') (hy : mraListEquiv R ys ys') :
    mraListEquiv R (xs ++ ys) (xs' ++ ys') := by
  intro a
  rw [below_list_append, below_list_append, hx a, hy a]

def append (x y : Mra R) : Mra R :=
  ⟨Quotient.lift₂ (fun xs ys ↦ Quotient.mk _ (xs ++ ys))
    (by
      intro xs ys xs' ys' hx hy
      change mraListEquiv R xs xs' at hx
      change mraListEquiv R ys ys' at hy
      exact Quotient.sound (list_equiv_append hx hy)) x.repr y.repr⟩

@[elab_as_elim]
private theorem quotient_induction_on {motive : Mra R → Prop} (x : Mra R)
    (h : ∀ xs, motive ⟨Quotient.mk _ xs⟩) : motive x := by
  obtain ⟨x⟩ := x
  exact Quotient.inductionOn x h

private theorem eq_of_below_iff {x y : Mra R}
    (h : ∀ a, below a x ↔ below a y) : x = y := by
  revert h
  refine quotient_induction_on x fun _ ↦ ?_
  refine quotient_induction_on y fun _ ↦ ?_
  intro h
  exact congrArg Mra.mk (Quotient.sound h)

private theorem below_append (a : α) (x y : Mra R) :
    below a (append x y) ↔ below a x ∨ below a y := by
  refine quotient_induction_on x fun xs ↦ ?_
  refine quotient_induction_on y fun ys ↦ ?_
  exact below_list_append a xs ys

theorem append_assoc (x y z : Mra R) : append x (append y z) = append (append x y) z := by
  refine quotient_induction_on x fun xs ↦ ?_
  refine quotient_induction_on y fun ys ↦ ?_
  refine quotient_induction_on z fun zs ↦ ?_
  exact congrArg Mra.mk <|
    congrArg (Quotient.mk (mraSetoid R)) (List.append_assoc xs ys zs).symm

theorem append_comm (x y : Mra R) : append x y = append y x := by
  refine quotient_induction_on x fun _ ↦ ?_
  refine quotient_induction_on y fun _ ↦ ?_
  apply congrArg Mra.mk
  apply Quotient.sound
  intro a
  rw [below_list_append, below_list_append, or_comm]

theorem append_idem (x : Mra R) : append x x = x := by
  refine quotient_induction_on x fun _ ↦ ?_
  apply congrArg Mra.mk
  apply Quotient.sound
  intro a
  rw [below_list_append, or_self]

private theorem pcore_ne_of_eq (hxy : (x : Mra R) ≡{n}≡ y)
    (h : some x = some cx) : ∃ cy, some y = some cy ∧ cx ≡{n}≡ cy := by
  cases hxy
  exact ⟨cx, h, .rfl⟩

private theorem pcore_op_left_of_eq (h : some (x : Mra R) = some cx) :
    append cx x ≡ x := by
  rw [← Option.some.inj h]
  exact OFE.Equiv.of_eq (append_idem x)

private theorem pcore_op_mono_of_eq (h : some (x : Mra R) = some cx) (y : Mra R) :
    ∃ cy, some (append x y) ≡ some (append cx cy) := by
  rw [← Option.some.inj h]
  exact ⟨y, .rfl⟩

#rocq_ignore mra_valid "Replaced by the `Valid` field of `Iris.Mra.instCMRA`."
#rocq_ignore mra_validN "Replaced by the `ValidN` field of `Iris.Mra.instCMRA`."
#rocq_ignore mra_op "Replaced by the `op` field of `Iris.Mra.instCMRA`."
#rocq_ignore mra_pcore "Replaced by the `pcore` field of `Iris.Mra.instCMRA`."
#rocq_ignore mra_cmra_mixin
  "Replaced by direct `Iris.Mra.instCMRA`; iris-lean does not separate CMRA mixins."

@[rocq_alias mraR]
instance (R : α → α → Prop) : CMRA (Mra R) where
  pcore := some; op := append
  ValidN _ _ := True; Valid _ := True
  op_ne.ne _ _ _ h := by rw [h]
  pcore_ne hxy h := by exact pcore_ne_of_eq hxy h
  validN_ne _ := id
  valid_iff_validN := by simp
  validN_succ := id
  validN_op_left _ := trivial
  assoc := OFE.Equiv.of_eq (append_assoc ..)
  comm := OFE.Equiv.of_eq (append_comm ..)
  pcore_op_left h := by exact pcore_op_left_of_eq h
  pcore_idem _ := .rfl
  pcore_op_mono h y := by exact pcore_op_mono_of_eq h y
  extend _ h := ⟨_, _, OFE.Equiv.of_eq h, .rfl, .rfl⟩

@[rocq_alias mra_cmra_total]
instance : CMRA.IsTotal (Mra R) where
  total x := ⟨x, rfl⟩

@[rocq_alias mra_core_id]
instance (x : Mra R) : CMRA.CoreId x where
  core_id := .rfl

@[rocq_alias mra_cmra_discrete]
instance : CMRA.Discrete (Mra R) where
  discrete_0 := fun h _ ↦ h
  discrete_valid := id

#rocq_ignore mra_unit "Replaced by the `unit` field of `Iris.Mra.instUCMRA`."
#rocq_ignore auth_ucmra_mixin
  "Replaced by direct `Iris.Mra.instUCMRA`; iris-lean does not separate UCMRA mixins."

private theorem unit_left_eq (x : Mra R) :
    append ⟨Quotient.mk _ []⟩ x = x := by
  refine quotient_induction_on x fun _ ↦ ?_
  rfl

@[rocq_alias mraUR]
instance (R : α → α → Prop) : UCMRA (Mra R) where
  unit := ⟨Quotient.mk _ []⟩; unit_valid := trivial
  unit_left_id := (by exact OFE.Equiv.of_eq (unit_left_eq _)); pcore_unit := .rfl

@[rocq_alias mra_idemp]
theorem idem (x : Mra R) : x • x ≡ x :=
  OFE.Equiv.of_eq (append_idem x)

@[rocq_alias mra_included]
theorem inc_iff (x y : Mra R) : x ≼ y ↔ y ≡ x • y :=
  ⟨fun h ↦ (CMRA.op_core_right_of_inc h).symm, fun h ↦ ⟨y, h⟩⟩

private theorem append_to_mra_eq_of_rel [hR : Transitive R] (h : R a b) :
    append (toMra (R := R) a) (toMra b) = toMra b := by
  refine eq_of_below_iff fun c ↦ ?_
  rw [below_append, below_to_mra, below_to_mra]
  constructor
  · exact fun hca_or_hcb ↦ hca_or_hcb.elim (fun hca ↦ hR.trans hca h) id
  · exact .inr

@[rocq_alias to_mra_R_op]
theorem to_mra_op_of_rel [hR : Transitive R] (a b : α) (h : R a b) :
    toMra (R := R) a • toMra b ≡ toMra b :=
  OFE.Equiv.of_eq (append_to_mra_eq_of_rel h)

private theorem rel_of_to_mra_inc [hR : Preorder R]
    (h : toMra (R := R) a ≼ toMra b) : R a b := by
  obtain ⟨z, hz⟩ := h
  rw [← below_to_mra (R := R) a b, hz.to_eq]
  exact (below_append a (toMra a) z).mpr <|
    .inl ((below_to_mra a a).mpr hR.refl)

@[rocq_alias to_mra_included]
theorem to_mra_inc_iff [hR : Preorder R] (a b : α) :
    toMra (R := R) a ≼ toMra b ↔ R a b :=
  ⟨rel_of_to_mra_inc, fun h ↦ ⟨toMra b, (to_mra_op_of_rel a b h).symm⟩⟩

private theorem local_update_grow_eq [hR : Transitive R] (h : R a b)
    (haz : toMra (R := R) a = append x z) :
    toMra b = append (toMra b) z := by
  refine eq_of_below_iff fun c ↦ ?_
  rw [below_to_mra, below_append, below_to_mra]
  constructor
  · exact .inl
  · rintro (hcb | hcz)
    · exact hcb
    · refine hR.trans ?_ h
      rw [← below_to_mra (R := R) c a, haz, below_append]
      exact .inr hcz

@[rocq_alias mra_local_update_grow]
theorem local_update_grow [hR : Transitive R] (a : α) (x : Mra R) (b : α) (h : R a b) :
    (toMra (R := R) a, x) ~l~> (toMra b, toMra b) := by
  refine (local_update_unital_discrete ..).mpr fun z _ haz ↦ ⟨trivial, ?_⟩
  exact OFE.Equiv.of_eq (local_update_grow_eq h haz.to_eq)

@[rocq_alias mra_local_update_get_frag]
theorem local_update_get_frag [hR : Preorder R] (a b : α) (h : R b a) :
    (toMra (R := R) a, UCMRA.unit) ~l~> (toMra a, toMra b) := by
  refine (local_update_unital_discrete ..).mpr fun z _ haz ↦ ⟨trivial, ?_⟩
  calc
    toMra a ≡ toMra b • toMra a := (to_mra_op_of_rel b a h).symm
    _ ≡ toMra b • z := (haz.trans CMRA.unit_left_id).op_r

private theorem to_mra_eq_of_rel {S : α → α → Prop} (hS : ∀ {a}, S a a)
    (hrel : ∀ {a a' b b'}, S a a' → S b b' → (R a b ↔ R a' b'))
    (hab : S a b) : toMra (R := R) a = toMra b :=
  eq_of_below_iff fun c ↦ by
    calc
      below c (toMra a) ↔ R c a := below_to_mra c a
      _ ↔ R c b := hrel hS hab
      _ ↔ below c (toMra b) := (below_to_mra c b).symm

private theorem rel_iff_of_to_mra_equiv (hab : toMra (R := R) a ≡ toMra b) (c : α) :
    R c a ↔ R c b := by
  calc
    R c a ↔ below c (toMra a) := (below_to_mra c a).symm
    _ ↔ below c (toMra b) := iff_of_eq (congrArg (below c) hab.to_eq)
    _ ↔ R c b := below_to_mra c b

@[rocq_alias to_mra_rel_proper]
theorem to_mra_rel_proper (S : α → α → Prop) (hS : ∀ {a}, S a a)
    (hrel : ∀ {a a' b b'}, S a a' → S b b' → (R a b ↔ R a' b')) :
    ∀ {a b}, S a b → toMra (R := R) a ≡ toMra b :=
  fun hab ↦ OFE.Equiv.of_eq (to_mra_eq_of_rel hS hrel hab)

@[rocq_alias to_mra_rel_inj]
theorem to_mra_rel_injective (S : α → α → Prop) (hR : ∀ {a}, R a a)
    (hanti : ∀ {a b}, R a b → R b a → S a b) :
    ∀ {a b}, toMra (R := R) a ≡ toMra b → S a b :=
  fun hab ↦ hanti
    ((rel_iff_of_to_mra_equiv hab _).mp hR)
    ((rel_iff_of_to_mra_equiv hab _).mpr hR)

@[rocq_alias to_mra_inj]
instance (priority := default + 1) [hR : Reflexive R]
    [hanti : Antisymmetric (fun a b : α ↦ a = b) R] :
    RelInjective (fun a b : α ↦ a = b) (OFE.Equiv : Mra R → Mra R → Prop) toMra where
  injective := to_mra_rel_injective (fun a b : α ↦ a = b)
    hR.refl hanti.antisymm

@[rocq_alias to_mra_proper]
instance [HasEquiv α] [hS : Reflexive (HasEquiv.equiv (α := α))]
    [hrel : RelHom₂ (HasEquiv.equiv (α := α)) HasEquiv.equiv Iff R] :
    RelHom (HasEquiv.equiv (α := α)) (OFE.Equiv : Mra R → Mra R → Prop) toMra where
  map_rel := to_mra_rel_proper HasEquiv.equiv hS.refl hrel.map_rel

@[rocq_alias to_mra_equiv_inj]
instance (priority := default) [HasEquiv α] [hR : Reflexive R]
    [hanti : Antisymmetric (HasEquiv.equiv (α := α)) R] :
    RelInjective (HasEquiv.equiv (α := α)) (OFE.Equiv : Mra R → Mra R → Prop) toMra where
  injective := to_mra_rel_injective HasEquiv.equiv hR.refl hanti.antisymm

end Mra
end Iris
